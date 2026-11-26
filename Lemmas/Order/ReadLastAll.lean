-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.ReadLast

@[expose] public section

/-! # A read returns the bytes of its last write (byte causality)

The whole-footprint form of `read_byte_of_last_write_ordered`: a write `w` of the read's footprint
(same place, same size, as many bytes) that is ordered before the read at every byte, and every
write of a byte of the read being `w`, ordered before `w` or ordered after the read, gives the
read the written bytes. -/

namespace PTX
noncomputable section

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- **A read returns the bytes of its last write** (byte causality, same footprint). -/
theorem read_of_last_write_ordered (hX : Consistent L K A mem0 X) {e w : AsyncCopy.Ref}
    {a dst : Acc} {bs : List (Option Byte)} {written : List Byte} (he : X.MemReads e a bs)
    (hw : X.MemWrites w dst written) (hloc : dst.loc = a.loc) (hsize : dst.size = a.size)
    (hlen : written.length = a.size)
    (hv : ∀ k < a.size, ByteCausality L X (a.loc.at k) w e)
    (hall : ∀ k < a.size, ∀ w' dst' bytes, X.MemWrites w' dst' bytes →
      dst'.Covers (a.loc.at k) →
      w' = w ∨ ByteCausality L X (a.loc.at k) w' w ∨ ByteCausality L X (a.loc.at k) e w') :
    bs = written.map some := by
  have hbl : bs.length = a.size := (hX.rf e a bs he).1
  apply List.ext_getElem?
  intro k
  by_cases hk : k < a.size
  · have hc : dst.Covers (a.loc.at k) := by
      rw [show dst = { dst with loc := a.loc, size := a.size } by cases dst; simp_all]
      exact Acc.covers_at hk
    rw [read_byte_of_last_write_ordered hX he hk hw hc (hv k hk) (hall k hk)]
    simp only [wbyte, Loc.at, hloc, Nat.add_sub_cancel_left, List.getElem?_map,
      List.getElem?_eq_getElem (show k < written.length by omega), Option.map_some]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

end
end PTX
