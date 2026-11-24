-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaSource
public import Lemmas.Tcgen05.TcMmaACell

@[expose] public section

/-! # The Tensor Memory A byte of an MMA has one source value

A proof tool. An MMA that reads operand A from Tensor Memory reads byte `index` from one cell
(`aCell`), and that byte lies in the operand's extent (`aCell_index_lt`). Two A read sources
(`ReadSource .a`) of the same byte are the same write at the same cell and byte
(`aReadSource_eq`), since the source of a read is unique (`readSource_unique`). A write leaves
one value in a cell when each MMA's output layout is injective (`wrote_functional`), so the
source value of the byte is unique (`aReadSource_value_eq`). -/

namespace PTX.TcMma
open PTX AsyncCopy
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {X : Execution} {mem0 : Mem0}

/-- A byte read from Tensor Memory as operand A lies in the operand's extent. -/
theorem aCell_index_lt {s : OperandSpec} {index : Nat} {c : Cell} {p : Nat}
    (h : aCell s index = some (c, p)) : index < Operand.a.bytes s.descriptor := by
  have hb := row_bytes s.descriptor.kind
  unfold aCell at h
  dsimp only at h
  cases ha : s.aTmem with
  | none => simp [ha] at h
  | some address =>
    simp only [ha, Option.bind_some] at h
    split at h
    · rename_i hc
      have hrow := hc.2.1
      rw [hb] at hrow
      unfold Operand.bytes
      rw [Nat.mul_assoc, hb]
      exact (Nat.div_lt_iff_lt_mul (by decide)).mp hrow
    · cases h

/-- **Two A sources of the same MMA byte are the same write, at the same cell and byte**: the
cell and byte are the operand layout's (`aCell`), and the source of the cell's A read is unique
(`readSource_unique`). -/
theorem aReadSource_eq (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    {s1 s2 mma : EvId} {index : Nat} {c1 c2 : Cell} {p1 p2 : Nat}
    (ha1 : ∃ d s acc mask, X.MmaIssue mma d s acc mask ∧ aCell s index = some (c1, p1))
    (ha2 : ∃ d s acc mask, X.MmaIssue mma d s acc mask ∧ aCell s index = some (c2, p2))
    (h1 : ReadSource L X .a s1 mma c1) (h2 : ReadSource L X .a s2 mma c2) :
    c1 = c2 ∧ p1 = p2 ∧ s1 = s2 := by
  obtain ⟨d, s, acc, mask, hi, hc⟩ := ha1
  obtain ⟨d', s', acc', mask', hi', hc'⟩ := ha2
  obtain ⟨-, rfl, -, -⟩ := mmaIssue_params hi hi'
  have hcp := Option.some.inj (hc.symm.trans hc')
  simp only [Prod.mk.injEq] at hcp
  obtain ⟨rfl, rfl⟩ := hcp
  exact ⟨rfl, rfl, readSource_unique hX hg h1 h2⟩

/-- **The A byte of an MMA has one source value**, when each MMA's output layout is
injective. -/
theorem aReadSource_value_eq (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    (hinj : LayoutInjective X)
    {s1 s2 mma : EvId} {index : Nat} {c1 c2 : Cell} {p1 p2 : Nat} {v1 v2 : Value}
    (ha1 : ∃ d s acc mask, X.MmaIssue mma d s acc mask ∧ aCell s index = some (c1, p1))
    (ha2 : ∃ d s acc mask, X.MmaIssue mma d s acc mask ∧ aCell s index = some (c2, p2))
    (h1 : ReadSource L X .a s1 mma c1) (hw1 : Wrote L A X s1 c1 v1)
    (h2 : ReadSource L X .a s2 mma c2) (hw2 : Wrote L A X s2 c2 v2) : p1 = p2 ∧ v1 = v2 := by
  obtain ⟨rfl, rfl, rfl⟩ := aReadSource_eq hX hg ha1 ha2 h1 h2
  exact ⟨rfl, wrote_functional hX hg hinj hw1 hw2⟩

end
end PTX.TcMma
