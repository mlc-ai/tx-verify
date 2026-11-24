-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.Order

@[expose] public section

/-! # A read returns its last write

A proof tool for read values that needs no race freedom. Let `w` be a write of a byte that is
visible to a read of the byte, and let every write of the byte be `w`, visible to `w` or ordered
after the read. Then the read returns `w`'s byte (`read_byte_of_last_write`): the reads-from source
of the byte (MEM-READS-FROM) is a write of the byte; it is not after the read (`NoFuture`), and it
is not visible to `w`, which is visible to the read (`Hidden`), so it is `w`; and `W0` is excluded,
because `w` is visible (`Hidden`). When `w` covers the whole read with the same footprint, the read
returns `w`'s bytes (`read_of_last_write`). -/

namespace PTX
noncomputable section

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- **A read returns the byte of its last write.** -/
theorem read_byte_of_last_write_ordered (hX : Consistent L K A mem0 X)
    {e w : AsyncCopy.Ref} {a dst : Acc}
    {bs : List (Option Byte)} {written : List Byte} (he : X.MemReads e a bs) {k : Nat}
    (hk : k < a.size) (hw : X.MemWrites w dst written) (hc : dst.Covers (a.loc.at k))
    (hv : ByteCausality L X (a.loc.at k) w e)
    (hall : ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at k) →
      w' = w ∨ ByteCausality L X (a.loc.at k) w' w ∨ ByteCausality L X (a.loc.at k) e w') :
    bs[k]? = some (wbyte dst written (a.loc.at k)) := by
  have hh := hX.hidden e a bs k w dst written he hk hw hc hv
  have hrf := (hX.rf e a bs he).2 k hk
  cases hs : X.rf e k with
  | none => simp [hs] at hh
  | some source =>
    rw [hs] at hh hrf
    obtain ⟨dst', bytes, hsource, hcov, hvalue⟩ := hrf
    rcases hall source dst' bytes hsource hcov with hsame | hbefore | hafter
    · subst source
      obtain ⟨hfp, rfl⟩ := hw.unique hsource
      simp only [wbyte, ← hfp.1] at hvalue ⊢
      exact hvalue
    · exact (hh hbefore).elim
    · exact (hX.noFuture e a bs k source he hk hs hafter).elim

/-- **A read returns the byte of its last write.** -/
theorem read_byte_of_last_write (hX : Consistent L K A mem0 X) {e w : AsyncCopy.Ref} {a dst : Acc}
    {bs : List (Option Byte)} {written : List Byte} (he : X.MemReads e a bs) {k : Nat}
    (hk : k < a.size) (hw : X.MemWrites w dst written) (hc : dst.Covers (a.loc.at k))
    (hv : modelCausality L X (a.loc.at k) w e)
    (hall : ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at k) →
      w' = w ∨ modelCausality L X (a.loc.at k) w' w ∨ modelCausality L X (a.loc.at k) e w') :
    bs[k]? = some (wbyte dst written (a.loc.at k)) :=
  read_byte_of_last_write_ordered hX he hk hw hc (.direct hv) (fun src a' bytes hsrc hcov =>
    (hall src a' bytes hsrc hcov).imp id (fun h => h.imp .direct .direct))

/-- **A read returns the bytes of its last write** of the same footprint. -/
theorem read_of_last_write (hX : Consistent L K A mem0 X) {e w : AsyncCopy.Ref} {a dst : Acc}
    {bs : List (Option Byte)} {written : List Byte} (he : X.MemReads e a bs)
    (hw : X.MemWrites w dst written) (hloc : dst.loc = a.loc) (hsize : dst.size = a.size)
    (hlen : written.length = a.size)
    (hv : ∀ k < a.size, modelCausality L X (a.loc.at k) w e)
    (hall : ∀ k < a.size, ∀ w' dst' bytes, X.MemWrites w' dst' bytes →
      dst'.Covers (a.loc.at k) →
      w' = w ∨ modelCausality L X (a.loc.at k) w' w ∨ modelCausality L X (a.loc.at k) e w') :
    bs = written.map some := by
  have hbl : bs.length = a.size := (hX.rf e a bs he).1
  apply List.ext_getElem?
  intro k
  by_cases hk : k < a.size
  · have hc : dst.Covers (a.loc.at k) := by
      rw [show dst = { dst with loc := a.loc, size := a.size } by cases dst; simp_all]
      exact Acc.covers_at hk
    rw [read_byte_of_last_write hX he hk hw hc (hv k hk) (hall k hk)]
    simp only [wbyte, Loc.at, hloc, Nat.add_sub_cancel_left, List.getElem?_map,
      List.getElem?_eq_getElem (show k < written.length by omega), Option.map_some]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

end
end PTX
