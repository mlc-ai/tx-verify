-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
public import Kernels.TmlFa4Fwd.Proof.Lib.SchedWords

@[expose] public section

/-! # The correction warps as a site machine

Warps 8 to 11 (128 threads, one accumulator row each) run from their `setmaxnreg` (pc 7746) to
the `ret`. A lane meets the MMA and softmax warps at named barrier 2 (`bar1`), frees the two
statistics slots (`arr`), and picks its CTA's tile by the persistent scheduler's first pass,
exactly as the output warp (`word` … `tiles`, the same arithmetic on other registers, recorded in
an `Epilogue.D`). With a tile it reads the request's offsets and used-K length (`q0`, `q1`,
`uk`), meets its softmax warp at its two named barriers (`nb`, with the arrival `free` between),
and runs one rescale round per K/V block after the first (`r…`): per stage, a named barrier, the
stage's scale from the statistics word, a ballot whether some row needs rescaling, and then eight
Tensor Memory loads of 16 accumulator columns, each multiplied by the scale and stored back
(`rld`, `rldw`, `rst`), a store wait and two arrivals. The final stage (`f…`) reads each stage's
row sum and maximum, waits for the last PV MMA, and normalizes the accumulator: sixteen loads of
8 columns (`fld`, `fwl`), multiplied by the reciprocal row sum and stored to shared memory in two
four-word stores each (`fst`), a proxy fence and two arrivals. The LSE stores (`lse`) and the
scheduler's second pass follow; the second pass finds no further tile, and the lane waits for the
output warp (`wend`), meets the other warps at barrier 2 (`barEnd`) and returns (`exit`).

A state is a site, the recorded values, and the sub-step `k` of the instruction (`Code.sub`):
the four elements of a vector store fire at sub-steps 0 to 3, and a rescale load (a site of the
kernel's `tcLdDataflow` assumption) performs its load at sub-step 0 and its implicit wait at
sub-step 1 (`rldw`). Every successor of a state at sub-step 0 is at sub-step 0 (in both
branches of a conditional successor, `D.ite`).

The machine follows every value: a load or shuffle of a 32-bit register records the word, and a
value of another kind stops the machine (`some none`); a statistics word or a Tensor Memory
element records its real number (`.float .f32 x`), and a value of another kind stops it. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 add32 addi sub32 mul32 mad32 min32 shrs shru
  andi scmp scmpi sel addrU addrS xor32 not32 shl popc divOk fdiv Scan laneW paramW
  batchOf skipFirst reqOf tlOf prefixD headsW lanePreds partials chosen loopOf)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ori ceil128 sbW sbi w32 neg32 wideS)

noncomputable section

/-! ### Values -/

/-- A real `f32` payload, and a pair of them. -/
abbrev fv (x : ℝ) : Value := .float .f32 x
abbrev fp (x y : ℝ) : Value := .pair (fv x) (fv y)

/-- The real number of an `f32` payload. -/
def fl32 (v : Value) : Option ℝ :=
  match v with
  | .float .f32 x => some x
  | _ => none

/-- The real numbers of `n` loaded elements, when each is an `f32` payload. -/
def flN (n : Nat) (vals : List Value) : Option (Nat → ℝ) :=
  if (List.range n).all fun i => (fl32 (vals.getD i (.pred false))).isSome then
    some fun i => (fl32 (vals.getD i (.pred false))).getD 0
  else none

/-! ### Sites -/

inductive Site where
  | setmax | bar1
  /-- The two statistics-slot arrivals of the start. -/
  | arr (k : Fin 2)
  | word (k : Scan)
  | down (k : Scan)
  | up (k : Scan) (j : Fin 5)
  | total (k : Scan)
  | vote (late : Bool)
  | pre (late : Bool)
  | tiles (late : Bool)
  | q0 | q1 | uk
  /-- The two named barriers with the softmax warp before the rescale rounds, and the arrival
  between them. -/
  | nb (k : Fin 2)
  | free
  /-- A rescale round's stage `st`: the named barrier, the scale, the ballot. -/
  | rbar (st : Fin 2)
  | rscale (st : Fin 2)
  | rvote (st : Fin 2)
  /-- Chunk `c` of a stage: its load (sub-step 0), its implicit wait (sub-step 1), its store. -/
  | rld (st : Fin 2) (c : Fin 8)
  | rldw (st : Fin 2) (c : Fin 8)
  | rst (st : Fin 2) (c : Fin 8)
  /-- The stage's store wait and its two arrivals. -/
  | rwait (st : Fin 2)
  | rarr (st : Fin 2) (k : Fin 2)
  /-- The final stage: the first arrival, then per stage the named barrier, the row sum and
  maximum, the arrival, the two polls. -/
  | farr0
  | fbar (st : Fin 2)
  | fsum (st : Fin 2)
  | fmax (st : Fin 2)
  | farr (st : Fin 2)
  | fw (st : Fin 2) (k : Fin 2)
  /-- Chunk `j` of the final stage: its load, its wait, its two four-word stores. -/
  | fld (st : Fin 2) (j : Fin 16)
  | fwl (st : Fin 2) (j : Fin 16)
  | fst (st : Fin 2) (j : Fin 16) (h : Fin 2)
  | fence (st : Fin 2)
  | fdone (st : Fin 2) (k : Fin 2)
  /-- The two LSE stores. -/
  | lse (h : Fin 2)
  /-- The end, after the first pass (no tile, `late = false`) or the second. -/
  | wend (late : Bool) | barEnd (late : Bool) | exit (late : Bool)
  deriving DecidableEq

/-- The program counter of rescale load `c` of stage `st`, and of its store. -/
def rldPc (st : Fin 2) (c : Fin 8) : Nat :=
  8012 + 219 * st.val + if c.val = 0 then 0 else 27 + 26 * (c.val - 1)
def rstPc (st : Fin 2) (c : Fin 8) : Nat := rldPc st c + if c.val = 0 then 26 else 25

/-- The program counter of final load `j` of stage `st`. -/
def fldPc (st : Fin 2) (j : Fin 16) : Nat :=
  296 * st.val + [8480, 8499, 8518, 8537, 8555, 8572, 8589, 8606, 8623, 8640, 8657, 8674, 8691,
    8708, 8725, 8742].getD j.val 0

/-- The distance from final store 0 of a chunk to its store 1. -/
def fstGap (j : Fin 16) : Nat := if j.val < 4 then 4 else 3

def Site.pc : Site → Nat
  | .setmax => 7746
  | .bar1 => 7747
  | .arr k => 7752 + 2 * k.val
  | .word k => match k with | .first => 7761 | .loop => 7821 | .second => 9089 | .loop2 => 9144
  | .down k => match k with | .first => 7762 | .loop => 7823 | .second => 9090 | .loop2 => 9146
  | .up k j => match k with
    | .first => 7781 + 4 * j.val | .loop => 7844 + 3 * j.val
    | .second => 9110 + 3 * j.val | .loop2 => 9167 + 3 * j.val
  | .total k => match k with | .first => 7801 | .loop => 7859 | .second => 9125 | .loop2 => 9182
  | .vote l => if l then 9194 else 7873
  | .pre l => if l then 9199 else 7880
  | .tiles l => if l then 9200 else 7884
  | .q0 => 7955
  | .q1 => 7956
  | .uk => 7959
  | .nb k => 7985 + 3 * k.val
  | .free => 7987
  | .rbar st => 8006 + 219 * st.val
  | .rscale st => 8007 + 219 * st.val
  | .rvote st => 8009 + 219 * st.val
  | .rld st c => rldPc st c
  | .rldw st c => rldPc st c
  | .rst st c => rstPc st c
  | .rwait st => 8221 + 219 * st.val
  | .rarr st k => 8223 + 219 * st.val + k.val
  | .farr0 => 8464
  | .fbar st => 8465 + 296 * st.val
  | .fsum st => 8466 + 296 * st.val
  | .fmax st => 8467 + 296 * st.val
  | .farr st => 8468 + 296 * st.val
  | .fw st k => 8473 + 296 * st.val + 3 * k.val
  | .fld st j => fldPc st j
  | .fwl st j => fldPc st j + 5
  | .fst st j h => fldPc st j + 12 + h.val * fstGap j
  | .fence st => 8758 + 296 * st.val
  | .fdone st k => 8759 + 296 * st.val + k.val
  | .lse h => 9073 + 9 * h.val
  | .wend _ => 9201
  | .barEnd _ => 9204
  | .exit _ => 9205

/-! ### States -/

/-- A row maximum: an extended real below `+∞` (`-∞` on a row with no unmasked key). -/
abbrev Mx : Type := {x : EReal // x ≠ ⊤}

instance : Zero Mx := ⟨⟨((0 : ℝ) : EReal), EReal.coe_ne_top 0⟩⟩

/-- A row sum's rescale factor: a number, or the pattern of one (a kept row maximum stores the
pattern `0f3F800000`). -/
inductive Sc where
  | num (x : ℝ)
  | one

/-- The factor as the code holds it. -/
abbrev Sc.val : Sc → Value
  | .num x => fv x
  | .one => .bits 32 (BitVec.ofNat 64 1065353216)

/-- The pair of the factor with itself, as the code packs it. -/
abbrev Sc.pair : Sc → Value
  | .num x => fp x x
  | .one => .bits 64 (BitVec.ofNat 64 4575657222473777152)

/-- The factor's real number. -/
abbrev Sc.real : Sc → ℝ
  | .num x => x
  | .one => 1

/-- A number times the factor, as the ideal product writes it. -/
abbrev Sc.mul (y : ℝ) : Sc → ℝ
  | .num x => y * x
  | .one => y

theorem Sc.mul_eq (y : ℝ) (s : Sc) : s.mul y = y * s.real := by
  cases s <;> simp

instance : Zero Sc := ⟨.num 0⟩

/-- The values a state records. -/
structure V where
  /-- The scheduler's scan: the words its events returned and its loop state (its `site` is
  not read). -/
  sc : Epilogue.D := { site := .start }
  /-- The request's used-K length. -/
  ukw : BitVec 64 := 0
  /-- The rescale rounds' counter `%r6218` (the negated number of rounds left). -/
  trip : BitVec 64 := 0
  /-- The scales of the current rescale round, by stage, and its two ballots. -/
  s0 : Sc := 0
  s1 : Sc := 0
  b0 : BitVec 64 := 0
  b1 : BitVec 64 := 0
  /-- The sixteen accumulator elements of the current rescale chunk. -/
  xs : Nat → ℝ := fun _ => 0
  /-- The row sum and the row maximum of each stage, read for the final stage; the maximum is
  `⊥` on a row with no unmasked key. -/
  rs0 : ℝ := 0
  rm0 : Mx := 0
  rs1 : ℝ := 0
  rm1 : Mx := 0
  /-- The eight accumulator elements of the current final chunk. -/
  ys : Nat → ℝ := fun _ => 0

/-- A state: the site, the recorded values and the sub-step. -/
structure D where
  site : Site
  v : V
  k : Fin 4 := 0

/-- A state at sub-step 0. -/
abbrev D.mk' (s : Site) (v : V) : D := ⟨s, v, 0⟩

/-- A conditional successor (both branches at sub-step 0). -/
abbrev D.ite (c : Bool) (a b : D) : D := if c = true then a else b

/-- The scale of rescale stage `st`, and its ballot. -/
def sOf (v : V) : Fin 2 → Sc | 0 => v.s0 | 1 => v.s1
def bOf (v : V) : Fin 2 → BitVec 64 | 0 => v.b0 | 1 => v.b1

/-- The row sum of final stage `st`. -/
def rsOf (v : V) : Fin 2 → ℝ | 0 => v.rs0 | 1 => v.rs1

/-- The row maximum of final stage `st`. -/
def rmOf (v : V) : Fin 2 → Mx | 0 => v.rm0 | 1 => v.rm1

/-- Record stage `st`'s scale, ballot, row sum, row maximum. -/
def setS (v : V) (x : Sc) : Fin 2 → V | 0 => { v with s0 := x } | 1 => { v with s1 := x }
def setB (v : V) (x : BitVec 64) : Fin 2 → V | 0 => { v with b0 := x } | 1 => { v with b1 := x }
def setRs (v : V) (x : ℝ) : Fin 2 → V | 0 => { v with rs0 := x } | 1 => { v with rs1 := x }
def setRm (v : V) (x : Mx) : Fin 2 → V | 0 => { v with rm0 := x } | 1 => { v with rm1 := x }

/-! ### Register values -/

/-- The thread index as `%tid.x` reads it, and the row of the thread (`tid & 127`). -/
abbrev tidW (L : Launch) (g : Nat) : BitVec 64 :=
  truncBits 32 (BitVec.ofNat 64 ((L.tidOf g).get .x))
abbrev rowW (L : Launch) (g : Nat) : BitVec 64 := andi (tidW L g) 127

/-- The warp index within the four correction warps' named barriers: `%r565`, `%r566`. -/
abbrev nb0W (L : Launch) (g : Nat) : BitVec 64 :=
  addi (andi (BitVec.ofNat 64 (g % L.block / 32)) 3) 3
abbrev nb1W (L : Launch) (g : Nat) : BitVec 64 :=
  addi (andi (BitVec.ofNat 64 (g % L.block / 32)) 3) 7

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
