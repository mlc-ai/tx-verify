-- SPDX-License-Identifier: Apache-2.0
-- iface: LateValues producer=W status=proved domain=consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.FmaTotal
public import Lemmas.Flow.TypedHalfG
public import Lemmas.Flow.Regs

@[expose] public section

/-! # The values the strict windows of the softmax and epilogue need

A data lane's instruction at a pc of the softmax and the epilogue (574 and above) does not fault
on its own: the integer, move, conversion, comparison and exact floating instructions are total on
the typed registers (`Lemmas/Flow/TypedAllF.lean`), `ex2.approx` and `lg2.approx` have a row for
every operand class, and `div.full` at 600 divides by the scale register, a launch constant
(`Pre.scalePos`, `scaleVal_float`; not a field here). What is left
are the value-dependent faults (the value chain proves them) and the classes of the words the
events bring in:

* the software `exp2` (the 16 blocks at pcs `1913 + 11 i`) faults on a `+inf` input and falls
  back to the single instructions on a NaN input, so the input is a real or `-inf`;
* `rcp.approx` at 2602 faults on a zero operand (`approxExact`);
* the three `tcgen05.ld` (pcs 1265, 2260, 2607), the `bfly` shuffles of the row reductions and
  the `ld.shared` of the scratch word (pc 2252) bring in `.f32` data of four bytes that are no
  slice of a wider value (`TyG.Dat32`: a number, a zero, an infinity or a NaN), so that the
  floating instructions that read the registers find a datum. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Assumptions

/-- `t` is a state of the thread `g` between two of its events: the state after the run of a prefix
of its trace and local steps. -/
def LaneState (L : Launch) (X : Execution) (g : Nat) (t : TState) : Prop :=
  ∃ k t0, Run kernel Assumptions.all L g {} ((X.tr g).take k) (some t0) ∧
    Relation.ReflTransGen (Tau kernel Assumptions.all L g) t0 t

/-- The pcs of the `shfl.sync.bfly` of the row maxima and sums. -/
def bflyPcs : List Nat := [1838, 2234, 2242, 2244, 2246, 2248, 2253, 2255]

/-- The pcs of the `tcgen05.ld` of the softmax and the epilogue. -/
def tcLdPcs : List Nat := [1265, 2260, 2607]

/-- The operations that have no Core rule when the ideal-real rule declines them: `add`, `sub` and
`mul` (one lane or two) without a written rounding modifier (`FloatInstr.arith` needs one). -/
def declineOp : Op → Bool
  | .float f => f.rnd.isNone && (f.op == .add || f.op == .sub || f.op == .mul)
  | _ => false

/-- The pcs of the softmax and epilogue data lanes, outside the software `exp2` blocks, whose
instruction is a `declineOp` (the scan of the code, not a list). -/
def declinePc (pc : Nat) : Bool :=
  ((574 ≤ pc && pc < 2331) || (2560 ≤ pc && pc < 2853)) && !emuSites.contains pc &&
    match kernel.code[pc]? with
    | some i => declineOp i.op
    | none => false

/-- The operation is the pack `cvt.rn.bf16x2.f32`, which `bf16Exact` reads as exact and declines
on a NaN operand. -/
def packOp : Op → Bool
  | .cvt c => c.dst == .packed (.float .bf16) 2 && c.src == .float .f32 && c.rnd == some .rn
  | _ => false

/-- The pcs of the softmax and epilogue data lanes, outside the software `exp2` blocks, whose
instruction is a `packOp` (the scan of the code, not a list). -/
def packPc (pc : Nat) : Bool :=
  ((574 ≤ pc && pc < 2331) || (2560 ≤ pc && pc < 2853)) && !emuSites.contains pc &&
    match kernel.code[pc]? with
    | some i => packOp i.op
    | none => false

/-- The operations of the bias path: the pack and unpack of 16-bit halves into 32 bits and the
widening `cvt.f32.bf16`, with their source operands. A source holds a half (`TyG.Half16`: a
16-bit pattern or a bf16 number, as `Softmax.Export.bias_half`), the unpacked word two halves
(`TyG.Word32`); `TyG.halfSrcOk`. -/
def halfSrcs : Op → Option (List Opnd)
  | .move m => if (m.kind == .pack || m.kind == .unpack) && m.ty.width == 32 then some m.srcs
    else none
  | .cvt c => if c.dst == .float .f32 && c.src == .float .bf16 then some c.srcs else none
  | _ => none

/-- The pcs of the softmax and epilogue data lanes, outside the software `exp2` blocks, whose
instruction is one of the bias path (the scan of the code, not a list). -/
def halfPc (pc : Nat) : Bool :=
  ((574 ≤ pc && pc < 2331) || (2560 ≤ pc && pc < 2853)) && !emuSites.contains pc &&
    match kernel.code[pc]? with
    | some i => (halfSrcs i.op).isSome
    | none => false

/-- **The value facts of the softmax and epilogue data lanes** (index below 128 in their block). -/
structure LateValues (L : Launch) (X : Execution) : Prop where
  /-- The input of each software `exp2` block is a real or `-inf`. -/
  exp2 : ∀ g t, g % L.block < 128 → LaneState L X g t → emuSites.contains t.pc = true →
    t.sub = 0 → t.acc = [] → ∀ asg, matchEmu emuBody (kernel.code.drop t.pc) [] = some asg →
      ∃ x : EReal, readERealOpnd t .f32 (.reg (emuReg asg .x)) = some (.ok x) ∧ x ≠ ⊤
  /-- The operand of `rcp.approx` (pc 2602, register 1762) is not a zero. -/
  rcp : ∀ g t, g % L.block < 128 → LaneState L X g t → t.pc = 2602 →
    ∀ x : EReal, readERealOpnd t .f32 (.reg 1762) = some (.ok x) → x ≠ 0
  /-- The words of the `tcgen05.ld` are `.f32` data of four bytes (`TyG.Dat32`). -/
  tcLd : ∀ {g k pc a vals sh}, X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ →
    g % L.block < 128 → pc ∈ tcLdPcs → ∀ v ∈ vals, TyG.Dat32 v
  /-- The ideal-real rule does not decline the `add`, `sub` and `mul` without a rounding modifier
(no NaN operand, no `inf - inf`, no `0 * inf`): they have no Core rule to fall back to. -/
  noDecline : ∀ g t, g % L.block < 128 → LaneState L X g t → declinePc t.pc = true →
    ∀ i, kernel.code[t.pc]? = some i → execIdealFloat L g t i.op ≠ none
  /-- Both operands of a pack `cvt.rn.bf16x2.f32` read as extended reals (no NaN): the pack is
then exact and its result is a datum of four bytes. -/
  pack : ∀ g t, g % L.block < 128 → LaneState L X g t → packPc t.pc = true →
    ∀ c, kernel.code[t.pc]? = some ⟨none, .cvt c⟩ → ∀ r ∈ c.srcs, ∀ a, r = .reg a →
      ∃ x : EReal, readERealOpnd t .f32 r = some (.ok x)
  /-- The registers a pack, unpack or widening of the bias path reads hold halves, or for an unpack
a word (a bias load returns a bf16 number, `bias_half`, so the registers are not typed by bit
patterns). Producer: the value lane (`Vals.ld`/`Vals.cur`, `bias_half`). -/
  half : ∀ g t, g % L.block < 128 → LaneState L X g t → halfPc t.pc = true →
    ∀ i, kernel.code[t.pc]? = some i → ∀ srcs, halfSrcs i.op = some srcs → ∀ r, .reg r ∈ srcs →
      ∃ v, t.regs r = some v ∧ TyG.halfSrcOk i.op v
  /-- The words the `bfly` shuffles bring in are `.f32` data of four bytes (`TyG.Dat32`). -/
  bfly : ∀ {g k pc m a b c recv ok}, X.get (g, k) = some ⟨pc, .shfl m a b c recv ok⟩ →
    g % L.block < 128 → pc ∈ bflyPcs → TyG.Dat32 recv
  /-- The bytes the `ld.shared` of the scratch store (pc 2252) returns rebuild to a word that is
`.f32` data of four bytes. -/
  ld : ∀ {g k a bs}, X.get (g, k) = some ⟨2252, .rd a bs⟩ → g % L.block < 128 →
    ∃ v, rebuild 3 bs = .ok v ∧ TyG.Dat32 v

end PTX.Kernels.InklingRelDecode.Proof.Iface
