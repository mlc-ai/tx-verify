-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.ReadSources

@[expose] public section

/-! Reads of reused buffers.

A protocol identifies the write of the current generation and orders every other covering write
either before it or after the read. The existing RF, hidden-source and no-future constraints then
determine the read. No unique-writer assumption, global race-freedom premise or new memory rule is
required. -/
namespace PTX
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- The current generation is the source when all other generations are ordered
before its write or after the read. This applies to independent async effects too. -/
theorem read_rf_of_ordered_reuse (hX : Consistent L K A mem0 X)
    {e w : AsyncCopy.Ref} {src dst : Acc} {bs : List (Option Byte)} {written : List Byte}
    (hr : X.MemReads e src bs) {k : Nat} (hk : k < src.size)
    (hw : X.MemWrites w dst written) (hc : dst.Covers (src.loc.at k))
    (hv : modelCausality L X (src.loc.at k) w e)
    (horder : ∀ other footprint bytes, X.MemWrites other footprint bytes →
      footprint.Covers (src.loc.at k) →
      other = w ∨ modelCausality L X (src.loc.at k) other w ∨
        modelCausality L X (src.loc.at k) e other) :
    X.rf e k = some w := by
  have hhidden := hX.hidden e src bs k w dst written hr hk hw hc (.direct hv)
  cases hrf : X.rf e k with
  | none => simp [hrf] at hhidden
  | some other =>
    have hsource := (hX.rf e src bs hr).2 k hk
    rw [hrf] at hsource
    obtain ⟨footprint, bytes, hwrite, hcover, _⟩ := hsource
    rcases horder other footprint bytes hwrite hcover with heq | hbefore | hafter
    · exact congrArg some heq
    · rw [hrf] at hhidden
      exact (hhidden (.direct hbefore)).elim
    · exact (hX.noFuture e src bs k other hr hk hrf (.direct hafter)).elim

theorem read_byte_of_ordered_reuse (hX : Consistent L K A mem0 X)
    {e w : AsyncCopy.Ref} {src dst : Acc} {bs : List (Option Byte)} {written : List Byte}
    (hr : X.MemReads e src bs) {k : Nat} (hk : k < src.size)
    (hw : X.MemWrites w dst written) (hc : dst.Covers (src.loc.at k))
    (hv : modelCausality L X (src.loc.at k) w e)
    (horder : ∀ other footprint bytes, X.MemWrites other footprint bytes →
      footprint.Covers (src.loc.at k) →
      other = w ∨ modelCausality L X (src.loc.at k) other w ∨
        modelCausality L X (src.loc.at k) e other) :
    bs[k]? = some (wbyte dst written (src.loc.at k)) := by
  have hsource := (hX.rf e src bs hr).2 k hk
  rw [read_rf_of_ordered_reuse hX hr hk hw hc hv horder] at hsource
  obtain ⟨footprint, bytes, hwrite, _, hvalue⟩ := hsource
  obtain ⟨hfp, rfl⟩ := hw.unique hwrite
  simp only [wbyte, ← hfp.1] at hvalue ⊢
  exact hvalue

end
end PTX
