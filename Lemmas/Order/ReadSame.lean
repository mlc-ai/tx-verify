-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.ReadLast

@[expose] public section

/-! # A read of a byte written by many writes with one value

A proof tool, generic over the kernel (promoted from Inkling's `Proof2/Lib/ReadSame.lean`,
request L-q). `read_byte_of_last_write` needs one last
write of the byte. When a byte is written by a class `W` of writes that all give it the value `v`
(the 128 threads of a role that store one word), with one of them visible to the read and every
write of the byte outside `W` ordered after the read, the read returns `v`
(`read_byte_of_writers`): the reads-from source of the byte is a write of the byte; it is not after
the read (`NoFuture`), so it is in `W` and gives `v`; and the initial memory is excluded because a
write of `W` is visible (`Hidden`). `read_of_writers` is the form for every byte of the read. -/

namespace PTX
noncomputable section

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- **A read returns the byte its class of writers gives.** -/
theorem read_byte_of_writers (hX : Consistent L K A mem0 X) {e : AsyncCopy.Ref} {a : Acc}
    {bs : List (Option Byte)} (he : X.MemReads e a bs) {k : Nat} (hk : k < a.size)
    (W : AsyncCopy.Ref → Prop) (v : Option Byte)
    (hvis : ∃ w dst written, W w ∧ X.MemWrites w dst written ∧ dst.Covers (a.loc.at k) ∧
      ByteCausality L X (a.loc.at k) w e)
    (hval : ∀ w dst written, W w → X.MemWrites w dst written → dst.Covers (a.loc.at k) →
      wbyte dst written (a.loc.at k) = v)
    (hall : ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at k) →
      W w' ∨ ByteCausality L X (a.loc.at k) e w') :
    bs[k]? = some v := by
  obtain ⟨w, dst, written, hW, hw, hc, hv⟩ := hvis
  have hh := hX.hidden e a bs k w dst written he hk hw hc hv
  have hrf := (hX.rf e a bs he).2 k hk
  cases hs : X.rf e k with
  | none => simp [hs] at hh
  | some source =>
    rw [hs] at hrf
    obtain ⟨dst', bytes, hsource, hcov, hvalue⟩ := hrf
    rcases hall source dst' bytes hsource hcov with hW' | hafter
    · rw [← hval source dst' bytes hW' hsource hcov]
      exact hvalue
    · exact (hX.noFuture e a bs k source he hk hs hafter).elim

/-- **A read returns the bytes its class of writers gives**, byte by byte. -/
theorem read_of_writers (hX : Consistent L K A mem0 X) {e : AsyncCopy.Ref} {a : Acc}
    {bs : List (Option Byte)} (he : X.MemReads e a bs) (W : AsyncCopy.Ref → Prop)
    (vs : List Byte) (hlen : vs.length = a.size)
    (hvis : ∀ k < a.size, ∃ w dst written, W w ∧ X.MemWrites w dst written ∧
      dst.Covers (a.loc.at k) ∧ ByteCausality L X (a.loc.at k) w e)
    (hval : ∀ k < a.size, ∀ w dst written, W w → X.MemWrites w dst written →
      dst.Covers (a.loc.at k) → wbyte dst written (a.loc.at k) = vs[k]?)
    (hall : ∀ k < a.size, ∀ w' dst' bytes, X.MemWrites w' dst' bytes →
      dst'.Covers (a.loc.at k) → W w' ∨ ByteCausality L X (a.loc.at k) e w') :
    bs = vs.map some := by
  have hbl : bs.length = a.size := (hX.rf e a bs he).1
  apply List.ext_getElem?
  intro k
  by_cases hk : k < a.size
  · obtain ⟨b, hb⟩ : ∃ b, vs[k]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [read_byte_of_writers hX he hk W (some b) (hvis k hk)
      (fun w dst written hW hw hc => (hval k hk w dst written hW hw hc).trans hb)
      (hall k hk), List.getElem?_map, hb]
    rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- **A read returns the byte its class of writers gives, with earlier writes hidden**: as
`read_byte_of_writers`, where a write outside the class may also be before the visible write
`w0` (`Hidden` excludes it as the source; `w0` need not be of the class). -/
theorem read_byte_of_writers_hidden (hX : Consistent L K A mem0 X) {e : AsyncCopy.Ref}
    {a : Acc} {bs : List (Option Byte)} (he : X.MemReads e a bs) {k : Nat} (hk : k < a.size)
    (W : AsyncCopy.Ref → Prop) (v : Option Byte) {w0 : AsyncCopy.Ref} {dst0 : Acc}
    {written0 : List Byte} (hw0 : X.MemWrites w0 dst0 written0)
    (hc0 : dst0.Covers (a.loc.at k)) (hv0 : ByteCausality L X (a.loc.at k) w0 e)
    (hval : ∀ w dst written, W w → X.MemWrites w dst written → dst.Covers (a.loc.at k) →
      wbyte dst written (a.loc.at k) = v)
    (hall : ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at k) →
      W w' ∨ ByteCausality L X (a.loc.at k) w' w0 ∨ ByteCausality L X (a.loc.at k) e w') :
    bs[k]? = some v := by
  have hh := hX.hidden e a bs k w0 dst0 written0 he hk hw0 hc0 hv0
  have hrf := (hX.rf e a bs he).2 k hk
  cases hs : X.rf e k with
  | none => simp [hs] at hh
  | some source =>
    rw [hs] at hh hrf
    obtain ⟨dst', bytes, hsource, hcov, hvalue⟩ := hrf
    rcases hall source dst' bytes hsource hcov with hW' | hbefore | hafter
    · rw [← hval source dst' bytes hW' hsource hcov]
      exact hvalue
    · exact (hh hbefore).elim
    · exact (hX.noFuture e a bs k source he hk hs hafter).elim

end
end PTX
