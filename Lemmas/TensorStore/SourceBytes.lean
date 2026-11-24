-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.ReadReuse
public import Lemmas.Order.ReadLast

@[expose] public section

/-! # The bytes a copy tensor store writes

A proof tool. A copy store (no reduction) writes at each slot the byte it read from its shared
source there (`TensorStore.CopyOk`, `TensorStore.writeByte_read`). When that source read reads
from a write that a staging protocol orders (`SourceOrdered`: the write is visible to the read
and every other write of the byte is ordered before it or after the read), the byte written is
that write's byte (`Consistent.store_read_byte`). Two stores whose source reads of a slot have one
ordered source write therefore write the same byte there, which is how a kernel shows that such
stores are writes of the same bytes with the same value (ERR-DATA-RACE `SameValueWrites`). -/

namespace PTX
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- The byte a copy store writes at a slot is the byte it read there. -/
theorem TensorStore.writeByte_read {o : TensorStore.Observation} {x y k : Nat} {b : Byte}
    (hok : TensorStore.CopyOk o.spec o.effects) (hred : o.spec.reduce = none)
    (hw : TensorStore.writeByte o x y k = some b) :
    TensorStore.readByte o x y k = some b ∧ ∃ l, TensorStore.readLoc o.spec x y k = some l := by
  unfold TensorStore.writeByte at hw
  unfold TensorStore.readByte TensorStore.readLoc
  cases hs : TensorTransfer.slotAt o.spec.descriptor x y k with
  | none => rw [hs] at hw; cases hw
  | some slot =>
    rw [hs] at hw
    obtain ⟨-, src, hsrc, heq⟩ := hok.writes slot b hw
    rw [heq hred] at *
    exact ⟨hsrc, _, rfl⟩

/-- Write `w` is the source of read `e` at byte `l` as a staging protocol shows it: `w` covers `l`
and is visible to `e` there, and every other write of `l` is visible to `w` or `e` is visible to
it. -/
def SourceOrdered (L : Launch) (X : Execution) (e : AsyncCopy.Ref) (l : Loc) (w : AsyncCopy.Ref)
    (dst : Acc) (bs : List Byte) : Prop :=
  X.MemWrites w dst bs ∧ dst.Covers l ∧ ByteCausality L X l w e ∧
    ∀ other fp bs', X.MemWrites other fp bs' → fp.Covers l →
      other = w ∨ ByteCausality L X l other w ∨ ByteCausality L X l e other

/-- **A tensor store's source read of a slot returns the byte it writes there**, which is the byte
of the slot's ordered source write. -/
theorem Consistent.store_read_byte (hX : Consistent L K A mem0 X) {i : EvId}
    {o : TensorStore.Observation} {x y k : Nat} {b : Byte} {l : Loc} {w : AsyncCopy.Ref}
    {dst : Acc} {bs : List Byte} (ho : X.tensorStores i = some o)
    (hred : o.spec.reduce = none) (hw : TensorStore.writeByte o x y k = some b)
    (hl : TensorStore.readLoc o.spec x y k = some l)
    (hsrc : SourceOrdered L X (.async i (.read (.store x y k))) l w dst bs) :
    some b = wbyte dst bs l := by
  obtain ⟨hiss, -, hok⟩ := hX.store i o ho
  obtain ⟨hr, -⟩ := TensorStore.writeByte_read hok hred hw
  obtain ⟨addr, hissue⟩ := hiss
  have hm : X.MemReads (.async i (.read (.store x y k))) ⟨l, 1, false, false, .cta, 0, false⟩
      [some b] := ⟨o, addr, b, ho, hissue, hl, hr, rfl, rfl⟩
  have hl0 : (⟨l, 1, false, false, .cta, 0, false⟩ : Acc).loc.at 0 = l := by simp [Loc.at]
  obtain ⟨hwr, hcov, hv, hord⟩ := hsrc
  have h := read_byte_of_last_write_ordered hX hm Nat.one_pos hwr (by rw [hl0]; exact hcov)
    (by rw [hl0]; exact hv) (by rw [hl0]; exact hord)
  rw [hl0] at h
  simpa using h

end
end PTX
