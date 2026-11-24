-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmScP
public import Kernels.InklingRelDecode.Proof.Thread.SmPst

@[expose] public section

/-! # The visibility mask applied to the pairs (pcs 1628-1755)

For each of the 32 pairs `q` four instructions unpack `%rd(499 + q)`, replace the invisible
columns by `-inf` (`selp.f32 d, a, 0fFF800000, p`, the column's predicate) and pack the two halves
again. The state `d.masked m` has the pairs `q < m` masked: its S words are the current contents
of the pair registers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-! ### The steps of one group -/

/-- `selp.f32 dst, a, imm, p`: the value of `a` where `p` holds, else the immediate. -/
theorem exec_selpI {t : TState} {dst a p imm : Nat} {va : Value} {pick : Bool}
    (hS : Assumption.SegFreePc asms t.pc) (hp : t.regs p = some (.pred pick))
    (ha : t.regs a = some va) (hva : va.bytes = 4) :
    execLocalA asms L g t (.int ⟨.selp, .float .f32, false, [some dst],
        [.reg a, .f32imm imm, .reg p]⟩) =
      .ok (PTX.next (setReg t dst (if pick then va else .bits 32 (BitVec.ofNat 64 imm)))) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  cases pick <;>
  simp [execLocal, Op.rule, IntInstr.rule, execMove, DType.width, readValue, readReg, readBits, hp,
    ha, hva, bind, Except.bind, pure, Except.pure, Value.bytes]

/-- The instruction at `pc` is `selp.f32 d, a, 0fFF800000, p`. -/
def selpAt (pc d a p : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .int i⟩ =>
    i == ⟨.selp, .float .f32, false, [some d], [.reg a, .f32imm 4286578688, .reg p]⟩
  | _ => false

theorem selpAt_spec {pc d a p : Nat} (h : selpAt pc d a p = true) :
    kernel.code[pc]? = some ⟨none, .int ⟨.selp, .float .f32, false, [some d],
      [.reg a, .f32imm 4286578688, .reg p]⟩⟩ := by
  unfold selpAt at h
  split at h
  · rename_i m hc
    rw [hc, beq_iff_eq.mp h]
  · cases h

/-! ### The groups, by index

The group `i` (pcs `1628 + 4 i` to `1631 + 4 i`) masks the pair `po i`; its temporaries are
`%r(679 + 4 i) … %r(682 + 4 i)` (ids `1141 + 4 i …`) and its predicates `mpl i` (low half) and
`mph i` (high half). -/

/-- The pair the group `i` masks. -/
def po (i : Nat) : Nat := if i = 0 then 1 else if i = 1 then 0 else i
/-- The predicate registers of the group `i`: low and high half. -/
def mpl (i : Nat) : Nat := if i = 0 then 159 else if i = 1 then 158 else 160 - 2 * i
def mph (i : Nat) : Nat := if i = 0 then 160 else if i = 1 then 161 else 161 - 2 * i

theorem mask_code : ∀ i < 32,
    unpackAt (1628 + 4 * i) (1140 + 4 * i) (1141 + 4 * i) (2447 + po i) = true ∧
    selpAt (1628 + 4 * i + 1) (1142 + 4 * i) (1141 + 4 * i) (mph i) = true ∧
    selpAt (1628 + 4 * i + 2) (1143 + 4 * i) (1140 + 4 * i) (mpl i) = true ∧
    packAt (1628 + 4 * i + 3) (2447 + po i) (1143 + 4 * i) (1142 + 4 * i) 64 = true := by
  decide +kernel

theorem mask_emu : ∀ i < 32, ∀ k < 4, Assumptions.emuSites.contains (1628 + 4 * i + k) = false := by
  decide +kernel

theorem mask_live1 : ∀ i < 32, (2447 + po i) ∈ Flow.live (1628 + 4 * i) ∧
    mpl i ∈ Flow.live (1628 + 4 * i + 2) ∧ mph i ∈ Flow.live (1628 + 4 * i + 1) ∧
    (1141 + 4 * i) ∈ Flow.live (1628 + 4 * i + 1) ∧ (1140 + 4 * i) ∈ Flow.live (1628 + 4 * i + 2) ∧
    (1142 + 4 * i) ∈ Flow.live (1628 + 4 * i + 3) ∧
    (1143 + 4 * i) ∈ Flow.live (1628 + 4 * i + 3) := by decide +kernel

theorem mask_live2 : ∀ i < 32,
    subX (Flow.live (1628 + 4 * i + 1)) (Flow.live (1628 + 4 * i)) [1140 + 4 * i, 1141 + 4 * i] =
      true ∧
    subX (Flow.live (1628 + 4 * i + 1 + 1)) (Flow.live (1628 + 4 * i + 1)) [1142 + 4 * i] = true ∧
    subX (Flow.live (1628 + 4 * i + 1 + 1 + 1)) (Flow.live (1628 + 4 * i + 1 + 1))
      [1143 + 4 * i] = true ∧
    subX (Flow.live (1628 + 4 * i + 1 + 1 + 1 + 1)) (Flow.live (1628 + 4 * i + 1 + 1 + 1))
      [2447 + po i] = true ∧
    disj (Flow.live (1628 + 4 * i + 1 + 1 + 1 + 1))
      [1140 + 4 * i, 1141 + 4 * i, 1142 + 4 * i, 1143 + 4 * i] = true := by decide +kernel

theorem mask_dist : ∀ i < 32,
    [1140 + 4 * i, 1141 + 4 * i, 1142 + 4 * i, 1143 + 4 * i, 2447 + po i].Nodup ∧
    mpl i ∉ [1140 + 4 * i, 1141 + 4 * i, 1142 + 4 * i, 1143 + 4 * i, 2447 + po i] ∧
    mph i ∉ [1140 + 4 * i, 1141 + 4 * i, 1142 + 4 * i, 1143 + 4 * i, 2447 + po i] := by
  decide +kernel

theorem mask_dead : ∀ i < 32, ∀ r ∈ Flow.live (1628 + 4 * i + 1 + 1 + 1 + 1),
    ¬ (876 ≤ r ∧ r < 876 + 64) := by decide +kernel

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
