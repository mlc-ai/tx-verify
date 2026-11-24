-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.Order

@[expose] public section

/-! Derived RF consequences for immutable inputs and uniquely written bytes.
The program supplies the writer facts; Core permits multiple writers and reused buffers. -/
namespace PTX
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A byte with no program writer comes from W0. -/
theorem read_rf_of_no_writer (hX : Consistent L K A mem0 X)
    {e : AsyncCopy.Ref} {src : Acc} {bs : List (Option Byte)}
    (hr : X.MemReads e src bs) {k : Nat} (hk : k < src.size)
    (hn : ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers (src.loc.at k)) :
    X.rf e k = none := by
  cases hs : X.rf e k with
  | none => rfl
  | some w =>
    have hh := (hX.rf e src bs hr).2 k hk
    rw [hs] at hh
    obtain ⟨dst, bytes, hw, hc, _⟩ := hh
    exact (hn w dst bytes hw hc).elim

theorem read_initial_of_no_writer (hX : Consistent L K A mem0 X)
    {e : AsyncCopy.Ref} {src : Acc} {bs : List (Option Byte)}
    (hr : X.MemReads e src bs) {k : Nat} (hk : k < src.size) {byte : Byte}
    (hm : mem0 (src.loc.at k) = some (some byte))
    (hn : ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers (src.loc.at k)) :
    bs[k]? = some (some byte) := by
  have hh := (hX.rf e src bs hr).2 k hk
  rw [read_rf_of_no_writer hX hr hk hn] at hh
  exact hh (some byte) hm

/-- Bytes initially allocated in a footprint, resolving unspecified bytes with this
execution's existing choices. Callers establish allocation before using this list. -/
def initialBytes (mem0 : Mem0) (X : Execution) (src : Acc) : List Byte :=
  (List.range src.size).map fun k =>
    ((mem0 (src.loc.at k)).getD none).getD (X.initial (src.loc.at k))

/-- A whole allocated read-only footprint has exactly its initial contents. This is
a consequence of RF and a proved absence of writers, not a memory-model restriction. -/
theorem read_bytes_of_no_writer (hX : Consistent L K A mem0 X)
    {e : AsyncCopy.Ref} {src : Acc} {bs : List Byte}
    (hr : X.MemReads e src (bs.map some))
    (ha : ∀ k < src.size, mem0 (src.loc.at k) ≠ none)
    (hn : ∀ k < src.size, ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers (src.loc.at k)) : bs = initialBytes mem0 X src := by
  have hlen : bs.length = src.size := by simpa using (hX.rf e src _ hr).1
  apply List.ext_getElem?
  intro k
  by_cases hk : k < src.size
  · have hs := (hX.rf e src _ hr).2 k hk
    rw [read_rf_of_no_writer hX hr hk (hn k hk)] at hs
    cases hm : mem0 (src.loc.at k) with
    | none => exact (ha k hk hm).elim
    | some c =>
      have hb := hs c hm
      simp only [List.getElem?_map, Execution.initialByte] at hb
      have hout : (initialBytes mem0 X src)[k]? = some (c.getD (X.initial (src.loc.at k))) := by
        simp [initialBytes, List.getElem?_range hk, hm]
      rw [hout]
      cases hraw : bs[k]? with
      | none => simp [hraw] at hb
      | some b => simpa [hraw] using hb
  · rw [List.getElem?_eq_none (by omega),
      List.getElem?_eq_none (by simp [initialBytes]; omega)]

/-- If the program establishes a unique overlapping writer and observes it, RF must
select it. No safety or successful-result assumption is used to establish the read. -/
theorem read_byte_of_unique_writer (hX : Consistent L K A mem0 X)
    {e w : AsyncCopy.Ref} {src dst : Acc} {bs : List (Option Byte)} {written : List Byte}
    (hr : X.MemReads e src bs) {k : Nat} (hk : k < src.size)
    (hw : X.MemWrites w dst written) (hc : dst.Covers (src.loc.at k))
    (hv : modelCausality L X (src.loc.at k) w e)
    (hu : ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers (src.loc.at k) → w' = w) :
    bs[k]? = some (wbyte dst written (src.loc.at k)) := by
  have hh := hX.hidden e src bs k w dst written hr hk hw hc (.direct hv)
  have hs := (hX.rf e src bs hr).2 k hk
  cases hrf : X.rf e k with
  | none => simp [hrf] at hh
  | some w' =>
    rw [hrf] at hs
    obtain ⟨dst', bytes, hw', hc', hval⟩ := hs
    have heq := hu w' dst' bytes hw' hc'
    subst w'
    obtain ⟨hfp, rfl⟩ := hw.unique hw'
    simp only [wbyte, ← hfp.1] at hval ⊢
    exact hval

end
end PTX
