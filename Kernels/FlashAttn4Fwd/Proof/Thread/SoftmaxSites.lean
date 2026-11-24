-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Common
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderWork
public import Lemmas.Flow.Widen
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The softmax warps: sites and states

Warps 0 to 7 of both CTAs (all lanes) run lines 1618-4514 of the PTX. Warp `w` serves stage
`st = w / 4` (the query rows `128 st …` of the CTA's 256-row half of the item) and, as the
`k = w % 4`-th warp of its stage, the Tensor Memory lanes `32 k … 32 k + 31`; its thread owns
row `ρ = tid % 128` of the stage. After the register increase and the start barrier
(`bar.sync 2, 416`) a thread walks the static schedule of its cluster (`Work`); for item `i`,
with `n` the number of key-value tiles:

* the first tile: the poll of its statistics barrier (`+240 + 8 st`, the credit of the
  correction warp), the poll of the score barrier (`+128 + 8 st`), four loads of 32 score
  columns, the row maximum, generation 0 of the named barrier `k + 3 + 4 st` (`bar.arrive`),
  the exponentials, the stores of the half-precision probabilities (`tcgen05.st`, columns
  `64 … 127` of the stage), the remote arrivals on the leader's P-ready barriers (`+144`, and
  by the elected lane `+160`), the second statistics poll and the row sum;
* `n - 1` loop trips `t`: the score poll and loads, the lazy rescale (`α`) stored to shared
  memory (`+332 + 512 st + 4 ρ`), a named-barrier generation, the exponentials and stores, the
  arrivals, the statistics poll and the rescaled row sum;
* the store of the row sum `l` and the last named-barrier generation.

After its items the thread polls the statistics barrier once more, arrives on the end barrier
(`bar.arrive 2, 416`) and leaves.

A state is the next event (`Site`), the item `i`, the loop trip `t`, the 128 words of the tile
loaded last as the loads returned them (`w`: a load may return any value), the reference
maximum (`m`, register `%r3597`) and the row sum (`l`, `%r3598`) as the values the code computed
(outcomes of the floating instructions on the loaded words, which need not be numbers). Every
register is a function of these (`SoftmaxTable`). The score of column `j` (`d.s j`) is the number
its half of the packed pair reads as (`0` where it does not read as one). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### Shape of the thread -/

/-- The shared-memory base address. -/
abbrev sb (L : Launch) : Nat := L.sharedBase
/-- The thread's index in the block. -/
abbrev tidOf (L : Launch) (g : Nat) : Nat := g % L.block
/-- The thread's stage (`w / 4`). -/
abbrev stOf (L : Launch) (g : Nat) : Nat := warpOf L g / 4
/-- The warp's index in its stage (`w % 4`). -/
abbrev kOf (L : Launch) (g : Nat) : Nat := warpOf L g % 4
/-- The number of key-value tiles of an item: `ceil (sk / 128)`. -/
abbrev trips (L : Launch) : Nat := Work.n L
/-- The number of work items of the thread's cluster. -/
abbrev items (L : Launch) (g : Nat) : Nat := Work.T L g

/-- The Tensor Memory address of the warp's lanes at column `col` of the stage. -/
abbrev tmem (L : Launch) (g : Nat) (col : Nat) : Nat :=
  2097152 * kOf L g + 128 * stOf L g + col

/-- The `mapa` of a barrier at offset `off` of the cluster's leader CTA. -/
def leadPtr (L : Launch) (g : Nat) (off : Nat) : Value :=
  .ptr 32 false (.shared (ctaOf L g) (2 * (ctaOf L g / 2))) (BitVec.ofNat 64 (sb L + off))

/-- The bits of the scale parameter (`param_8`) as `ld.param.b32` reads them. -/
def scaleV (L : Launch) : Value := .bits 32 (truncBits 32 ((L.params (param "8")).getD 0))

/-! ### Sites -/

theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

theorem fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  fin_cases x <;> simp

theorem fin4_cases (x : Fin 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  fin_cases x <;> simp

/-- The softmax warps' next event. `lp` tells the loop body (`true`) from the first tile. -/
inductive Site where
  /-- `setmaxnreg.inc 176` and the start barrier `bar.sync 2, 416`. -/
  | setMaxReg | bar0
  /-- The polls of the statistics barrier: before the first tile (`0`), after it (`1`), at
  the end of a loop trip (`2`), and after the last item (`3`). -/
  | statsW (w : Fin 4)
  /-- The poll of the score barrier. -/
  | sW (lp : Bool)
  /-- The load of score columns `32 c …` and its implicit `tcgen05.wait::ld`. -/
  | ld (lp : Bool) (c : Fin 4) | ldW (lp : Bool) (c : Fin 4)
  /-- The store of `α` to the statistics word. -/
  | alphaSt
  /-- The named barrier `k + 3 + 4 st`: after the first tile's maximum (`0`), in a loop trip
  (`1`), after the item (`2`). -/
  | gen (j : Fin 3)
  /-- The store of probability columns `64 + 16 c …` and the two `tcgen05.wait::st`. -/
  | pst (lp : Bool) (c : Fin 4) | pwait (lp : Bool) (h : Fin 2)
  /-- The arrival on the leader's P-ready barrier (`+144 + 8 st`), the warp barrier, the
  election, and the elected lane's arrival on `+160 + 8 st`. -/
  | pArr (lp : Bool) | warpBar (lp : Bool) | el (lp : Bool) | p2Arr (lp : Bool)
  /-- The store of the row sum `l`, the end barrier, the exit. -/
  | lSt | barEnd | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .setMaxReg => Flow.setMaxReg_4 | .bar0 => Flow.bar_2
  | .statsW 0 => Flow.mbarWait_30 | .statsW 1 => Flow.mbarWait_32
  | .statsW 2 => Flow.mbarWait_34 | .statsW 3 => Flow.mbarWait_35
  | .sW false => Flow.mbarWait_31 | .sW true => Flow.mbarWait_33
  | .ld false c => Flow.tmemLoad.getD c.val 0 | .ld true c => Flow.tmemLoad.getD (4 + c.val) 0
  | .ldW false c => Flow.tmemLoad.getD c.val 0
  | .ldW true c => Flow.tmemLoad.getD (4 + c.val) 0
  | .alphaSt => Flow.store_0
  | .gen 0 => Flow.barArrive_0 | .gen 1 => Flow.barArrive_1 | .gen 2 => Flow.barArrive_2
  | .pst false c => Flow.tmemStore.getD c.val 0
  | .pst true c => Flow.tmemStore.getD (4 + c.val) 0
  | .pwait false h => Flow.tmemWait.getD h.val 0
  | .pwait true h => Flow.tmemWait.getD (2 + h.val) 0
  | .pArr false => Flow.mbarArrive_10 | .pArr true => Flow.mbarArrive_12
  | .warpBar false => Flow.warpBar_0 | .warpBar true => Flow.warpBar_1
  | .el false => Flow.elect_52 | .el true => Flow.elect_53
  | .p2Arr false => Flow.mbarArrive_11 | .p2Arr true => Flow.mbarArrive_13
  | .lSt => Flow.store_1 | .barEnd => Flow.barArrive_3 | .exit => Flow.exit_0

/-- The sub-step of the instruction the thread is at: `1` at the implicit `tcgen05.wait::ld`
after a load (ASM-TCLD-DATAFLOW). -/
def Site.sub : Site → Nat
  | .ldW _ _ => 1
  | _ => 0

/-- Sites of the first tile of an item (up to its second statistics poll). -/
def Site.tile0 : Site → Bool
  | .statsW 0 | .statsW 1 | .sW false | .ld false _ | .ldW false _ | .gen 0 | .pst false _
  | .pwait false _ | .pArr false | .warpBar false | .el false | .p2Arr false => true
  | _ => false

/-- Sites of a loop trip. -/
def Site.inTrip : Site → Bool
  | .statsW 2 | .sW true | .ld true _ | .ldW true _ | .alphaSt | .gen 1 | .pst true _
  | .pwait true _ | .pArr true | .warpBar true | .el true | .p2Arr true => true
  | _ => false

/-- Sites inside an item. -/
def Site.inItem : Site → Bool
  | .setMaxReg | .bar0 | .statsW 3 | .barEnd | .exit => false
  | _ => true

/-- A softmax state. -/
structure D where
  site : Site
  /-- The work item (the number of items done, at the tail). -/
  i : Nat := 0
  /-- The loop trip (`n - 1` after the loop). -/
  t : Nat := 0
  /-- The words of the tile loaded last, by column, as the loads returned them (after the first
  tile's row maximum, the halves it selected). -/
  w : Nat → Value := fun _ => b32 0
  /-- The value of the reference maximum (`%r3597`): the outcome of the `max.f32` tree, which a
  NaN, an infinite or a non-numeric score word may make other than a number. -/
  m : Value := b32 0
  /-- The value of the row sum (`%r3598`). -/
  l : Value := b32 0

/-- The words after the load of columns `32 c … 32 c + 31` with values `vals`. -/
def loadW (w : Nat → Value) (c : Nat) (vals : List Value) : Nat → Value :=
  fun j => if j / 32 = c then vals.getD (j % 32) (b32 0) else w j

/-- Column `j`'s half of the pack of columns `2 k, 2 k + 1` (`mov.b64 d, {lo, hi}` then
`mov.b64 {lo, hi}, d`). -/
def half (w : Nat → Value) (j : Nat) : Value :=
  if j % 2 = 0 then (splitValue 64 (joinValue (w j) (w (j + 1)))).1
  else (splitValue 64 (joinValue (w (j - 1)) (w j))).2

/-- The score of column `j`: the number its half reads as (`0` if it does not read as one). The
real readings of the computed values hold where the halves read as numbers. -/
abbrev D.s (d : D) (j : Nat) : ℝ := rd32 (half d.w j)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
