-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Prologue
public import Lemmas.Flow.Regs
public import Lemmas.Arith.FastDivmod

@[expose] public section

/-! # The static schedule of the loader and the epilogue

The loader (warp 14) and the epilogue store warp (warp 13) of both CTAs of a cluster walk the
same static persistent schedule: cluster `c` (`%clusterid.x`) takes the work items
`c, c + G, c + 2G, …` below the item count (`param_13`), `G = %nclusterid.x`. Item `w` is the
query block `w % nb` of head `w / nb % H` of batch `w / nb / H`, where `nb` and `H` are the
divisors of the two `FastDivmod` parameter objects (`param_11`, `param_12`).

The launch data are the prologue's (`Common.lean`: `skOf`, `divWord`, `divShift`, `totOf`,
`clusterOf`); the registers both roles inherit are valued by the prologue's table
(`Prologue.valueOf`), which the role tables fall back to. The schedule registers the roles
compute are stated as the code's terms (`workW`, `qbW`, …, below); `LoaderWorkPre.lean` says
what they mean under `Pre`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Work
open PTX PTX.Proof

noncomputable section

/-- `seqlen_k` (`%r330`). -/
abbrev sk (L : Launch) : Nat := skOf L
/-- The query-block divisor `nb`, its multiplier and shifts (`%r331`, `%r332`, `%rs2`, `%rs3`). -/
abbrev nb (L : Launch) : Nat := divWord L "11" 0
abbrev nbMul (L : Launch) : Nat := divWord L "11" 1
abbrev nbS1 (L : Launch) : Nat := divShift L "11" 0
abbrev nbS2 (L : Launch) : Nat := divShift L "11" 1
/-- The head divisor `H`, its multiplier and shifts (`%r333`, `%r334`, `%rs4`, `%rs5`). -/
abbrev heads (L : Launch) : Nat := divWord L "12" 0
abbrev hMul (L : Launch) : Nat := divWord L "12" 1
abbrev hS1 (L : Launch) : Nat := divShift L "12" 0
abbrev hS2 (L : Launch) : Nat := divShift L "12" 1

/-- The thread's parity in its CTA pair (`%ctaid.x & 1`) and its cluster. -/
abbrev rank (L : Launch) (g : Nat) : Nat := ctaOf L g % 2
abbrev cid (L : Launch) (g : Nat) : Nat := clusterOf L g

/-- The number of clusters (`%nclusterid.x`). -/
def G (L : Launch) : Nat := L.grid / L.clusterSize.val

/-- Item `i` of the thread's cluster. -/
def work (L : Launch) (g i : Nat) : Nat := cid L g + i * G L

/-- The number of items of the thread's cluster. -/
def T (L : Launch) (g : Nat) : Nat := StaticSchedule.count (G L) (totOf L) (cid L g)

/-- The KV tiles of an item, `ceil(sk / 128)`. -/
def n (L : Launch) : Nat := (sk L + 127) / 128

/-! ## The code's integer operations

The value tables state the registers the schedule computes as these terms: each mirrors the
evaluator's rule for one 32-bit instruction on the registers' stored bits (`rd` is the read of
a register: its low 32 bits), so a segment's computed value and the table's agree by
unfolding. What the terms mean under `Pre` is proved separately (below). -/

/-- The 32-bit read of a register's stored bits. -/
abbrev rd (x : BitVec 64) : BitVec 64 := truncBits 32 x
/-- `add.s32`, `sub.s32`, `mul.lo.s32`. -/
def addW (a b : BitVec 64) : BitVec 64 := truncBits 32 (rd a + rd b)
def subW (a b : BitVec 64) : BitVec 64 := truncBits 32 (rd a - rd b)
def mulLoW (a b : BitVec 64) : BitVec 64 := truncBits 32 (rd a * rd b)
/-- `2 ^ 32` as an `Int` with the core's power instance, the one the evaluator's terms carry
(Mathlib's `Monoid` power is a different, only propositionally equal, term). -/
abbrev pow32 : Int :=
  @HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow)) 2 32
/-- `mul.hi.u32`. -/
def mulHiW (a b : BitVec 64) : BitVec 64 :=
  truncBits 32 (BitVec.ofInt 64 ((if false = true then toSigned 32 (rd a) * toSigned 32 (rd b)
    else ((rd a).toNat : Int) * ((rd b).toNat : Int)) / pow32))
/-- `shr.u32` by a register. -/
def shrW (a s : BitVec 64) : BitVec 64 := if (rd s).toNat ≥ 32 then 0 else rd a >>> (rd s).toNat
/-- `shl.b32`, `or.b32`, `xor.b32`. An immediate operand `v` is passed as `BitVec.ofInt 64 v`,
whose read is the evaluator's read of the literal. -/
def shlW (a s : BitVec 64) : BitVec 64 :=
  if (rd s).toNat ≥ 32 then 0 else truncBits 32 (rd a <<< (rd s).toNat)
def orW (a b : BitVec 64) : BitVec 64 := rd a ||| rd b
def xorW (a b : BitVec 64) : BitVec 64 := rd a ^^^ rd b
/-- `mov.b32` of a literal. -/
def immW (v : Int) : BitVec 64 := rd (BitVec.ofInt 64 v)
/-- `cvt.u32.u16` of a 16-bit register. -/
def cvtW (a : BitVec 64) : BitVec 64 := truncBits 32 (truncBits 16 a)

/-- The code's `FastDivmod` quotient of the word `x` (multiplier word `m`, shift registers
`s1`, `s2`), with the `mul.hi` operands in the order `x, m`. -/
def quotW (x m s1 s2 : BitVec 64) : BitVec 64 :=
  shrW (addW (shrW (subW x (mulHiW x m)) s1) (mulHiW x m)) s2

/-- The remainder `x - q * d` of the code (`mul.lo.s32`, `sub.s32`). -/
def remW (x q d : BitVec 64) : BitVec 64 := subW x (mulLoW q d)

/-- The stored bits of the parameter registers. -/
def nbS1W (L : Launch) : BitVec 64 := cvtW (BitVec.ofNat 64 (nbS1 L))
def nbS2W (L : Launch) : BitVec 64 := cvtW (BitVec.ofNat 64 (nbS2 L))
def hS1W (L : Launch) : BitVec 64 := cvtW (BitVec.ofNat 64 (hS1 L))
def hS2W (L : Launch) : BitVec 64 := cvtW (BitVec.ofNat 64 (hS2 L))
/-- `%nclusterid.x` as `mov.u32` stores it. -/
def GW (L : Launch) : BitVec 64 := truncBits 32 (BitVec.ofNat 64 (G L))

/-- The item index register at item `i`: the cluster index, then `add.s32` of `G` per item. -/
def workW (L : Launch) (g : Nat) : Nat → BitVec 64
  | 0 => BitVec.ofNat 64 (cid L g)
  | i + 1 => addW (workW L g i) (GW L)

/-- The quotient by `nb` of the item register, and the item's coordinates as the code
computes them. -/
def qbW (L : Launch) (g i : Nat) : BitVec 64 :=
  quotW (workW L g i) (BitVec.ofNat 64 (nbMul L)) (nbS1W L) (nbS2W L)
def batchW (L : Launch) (g i : Nat) : BitVec 64 :=
  quotW (qbW L g i) (BitVec.ofNat 64 (hMul L)) (hS1W L) (hS2W L)
def headW (L : Launch) (g i : Nat) : BitVec 64 :=
  remW (qbW L g i) (batchW L g i) (BitVec.ofNat 64 (heads L))
def mblkW (L : Launch) (g i : Nat) : BitVec 64 :=
  remW (workW L g i) (qbW L g i) (BitVec.ofNat 64 (nb L))

/-- The stage parity register at item `i`: `0`, then `xor.b32 1` per item. -/
def phaseW : Nat → BitVec 64
  | 0 => immW 0
  | i + 1 => xorW (phaseW i) (BitVec.ofInt 64 1)

/-- The item count register (as the prologue's table states it). -/
def totW (L : Launch) : BitVec 64 := BitVec.ofNat 64 (totOf L)

/-- Unfold the code's operations (and the given definitions) to the evaluator's terms, keeping
the launch constants (`nbS1W`, `GW`, …) folded: they stand in the conditions of the shifts,
where `dsimp` does not rewrite. The two sides of a table equation then agree syntactically,
and `w_rfl` closes it; an equation of a constant's first computation unfolds the constant. -/
syntax "unfold_w" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| unfold_w $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| dsimp only [quotW, remW, addW, subW, mulLoW, mulHiW, shrW, orW, shlW, xorW,
      immW, qbW, batchW, headW, mblkW, workW, phaseW, totW, b32, DType.width, DType.kind?,
      kind_u_beq_s, $extra,*])

syntax "w_rfl" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| w_rfl $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| first
      | with_reducible rfl
      | (unfold_w [$extra,*] <;> with_reducible rfl)
      | (dsimp only [GW, G, sregValue, totW, nbS1W, nbS2W, hS1W, hS2W, cvtW, b32, DType.width] <;>
          with_reducible rfl))

/-- `w_rfl`, then the unfolded equation by `rfl` at the default transparency. The reducible check
does not identify the evaluator's instances in the shifts with the table's. It is a separate
tactic because on a goal that needs arithmetic the default check recurses until the depth
limit. -/
syntax "w_rfl_deep" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| w_rfl_deep $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| first
      | w_rfl [$extra,*]
      | (unfold_w [$extra,*] <;> rfl))

theorem mulHiW_comm (a b : BitVec 64) : mulHiW a b = mulHiW b a := by
  unfold mulHiW
  simp only [Bool.false_eq_true, ↓reduceIte, mul_comm]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Work
