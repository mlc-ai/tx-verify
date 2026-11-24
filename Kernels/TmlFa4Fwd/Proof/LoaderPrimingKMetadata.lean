-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKPack
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingPoll

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof
open Thread.Loader (MetadataWord)
open Thread.Loader.LocalAccessCode (metadataCell metadataCellsApart DoesNotClobber)

noncomputable section

private theorem cellValueFromTrace {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i pc : Nat} {cell : Acc}
    {data : List Byte} {before after rest : List Event}
    (hTrace : (X.tr g).drop i = before ++ ⟨pc, .wr cell data⟩ :: (after ++ rest))
    (hKeep : ∀ e ∈ after, DoesNotClobber cell e) :
    PrimingCellValue X g (i + before.length + 1 + after.length) pc cell data := by
  let w := i + before.length
  have hWrite : X.get (g, w) = some ⟨pc, .wr cell data⟩ := by
    change (X.tr g)[i + before.length]? = _
    rw [← List.getElem?_drop, hTrace, List.getElem?_append_right (by omega)]
    simp
  refine ⟨w, by omega, hWrite, ?_⟩
  intro byte hb j hj dst ha hCov
  by_contra! hLater
  let offset := j - (w + 1)
  have hOffset : offset < after.length := by omega
  let e := after[offset]
  have hGet : X.get (g, j) = some e := by
    change (X.tr g)[j]? = _
    rw [show j = i + (before.length + (offset + 1)) by omega,
      ← List.getElem?_drop, hTrace, List.getElem?_append_right (by omega)]
    rw [show before.length + (offset + 1) - before.length = offset + 1 by omega]
    change (after ++ rest)[offset]? = _
    rw [List.getElem?_append_left hOffset, List.getElem?_eq_getElem hOffset]
  exact writeAccessDoesNotCover hX hGet (hKeep e (List.getElem_mem hOffset)) ha hb hCov

private def primingPageEvent (p : Params) (batch row : Nat) : List Event :=
  if row < p.kLength batch then
    [⟨503, .rd {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4}
      ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩]
  else []

private def primingMetadataStore (p : Params) (l : Launch) (g batch row : Nat)
    (slot : Fin 2) (word : MetadataWord) : Event :=
  ⟨primingMetadataPc word, .wr (metadataCell l g word slot)
    (b32 (primingMetadataValue p batch row word)).toBytes⟩

private theorem primingEvents_split (p : Params) (l : Launch) (g batch base : Nat)
    (slot : Fin 2) :
    primingScratchEvents p l g batch base slot =
      primingPageEvent p batch (base + 64 * slot.val) ++
        [primingMetadataStore p l g batch (base + 64 * slot.val) slot .page,
         primingMetadataStore p l g batch (base + 64 * slot.val) slot .row] := rfl

private theorem savedMetadataNoClobber {p : Params} {l : Launch} {g batch row : Nat}
    {slot other : Fin 2} {a b : MetadataWord} (hApart : a ≠ b ∨ slot ≠ other) :
    DoesNotClobber (metadataCell l g a slot) (primingMetadataStore p l g batch row other b) := by
  intro dst data hKind
  obtain ⟨rfl, _⟩ := Kind.wr.inj hKind
  exact metadataCellsApart hApart

private theorem primingWaitNoClobber {l : Launch} {g : Nat} {cell : Acc} {n : Nat}
    {e : Event} (hm : e ∈ List.replicate n (primingKWaitEvent l g false) ++
      [primingKWaitEvent l g true]) : DoesNotClobber cell e := by
  have hf : e = primingKWaitEvent l g false ∨ e = primingKWaitEvent l g true := by
    rcases List.mem_append.mp hm with hm | hm
    · exact .inl (List.eq_of_mem_replicate hm)
    · exact .inr (List.mem_singleton.mp hm)
  rcases hf with rfl | rfl <;> intro _ _ h <;> cases h

private theorem primingPageNoClobber {p : Params} {batch row : Nat} {cell : Acc}
    {e : Event} (hm : e ∈ primingPageEvent p batch row) :
    DoesNotClobber cell e := by
  unfold primingPageEvent at hm
  split at hm
  · obtain rfl := List.mem_singleton.mp hm
    intro _ _ h
    cases h
  · cases hm

/-- The actual priming scratch trace supplies both expected words in both slots
at the cursor following the successful K wait. -/
theorem primingMetadataFromObservedTrace {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i batch base n : Nat}
    {rest : List Event}
    (hTrace : (X.tr g).drop i = primingScratchEvents p l g batch base 0 ++
      primingScratchEvents p l g batch base 1 ++
      List.replicate n (primingKWaitEvent l g false) ++ (primingKWaitEvent l g true :: rest)) :
    ∀ slot : Fin 2, PrimingMetadataAt p l X g
      (i + (primingScratchEvents p l g batch base 0).length +
        (primingScratchEvents p l g batch base 1).length + n + 1)
      batch (base + 64 * slot.val) slot := by
  intro slot word
  -- Expose the optional global reads and the four writes in trace order.
  rw [primingEvents_split, primingEvents_split] at hTrace
  rw [primingEvents_split, primingEvents_split]
  let row0 := base + 64 * (0 : Fin 2).val
  let row1 := base + 64 * (1 : Fin 2).val
  let r0 := primingPageEvent p batch row0
  let r1 := primingPageEvent p batch row1
  let page0 := primingMetadataStore p l g batch row0 0 .page
  let rowStore0 := primingMetadataStore p l g batch row0 0 .row
  let page1 := primingMetadataStore p l g batch row1 1 .page
  let rowStore1 := primingMetadataStore p l g batch row1 1 .row
  let waits := List.replicate n (primingKWaitEvent l g false) ++ [primingKWaitEvent l g true]
  have hTrace' : (X.tr g).drop i = r0 ++ [page0, rowStore0] ++ r1 ++
      [page1, rowStore1] ++ waits ++ rest := by
    simpa only [r0, r1, page0, page1, rowStore0, rowStore1, waits, row0, row1, List.append_assoc,
      List.cons_append, List.nil_append] using hTrace
  fin_cases slot <;> cases word
  · have hCut : (X.tr g).drop i =
        r0 ++ page0 :: (([rowStore0] ++ r1 ++ [page1, rowStore1] ++ waits) ++ rest) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hTrace'
    have h := cellValueFromTrace hX hCut (by
      intro e he
      rcases List.mem_append.mp he with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · obtain rfl := List.mem_singleton.mp h
            exact savedMetadataNoClobber (Or.inl (by decide))
          · exact primingPageNoClobber h
        · simp at h
          rcases h with rfl | rfl <;> exact savedMetadataNoClobber (Or.inr (by decide))
      · exact primingWaitNoClobber h)
    convert h using 1 <;> simp [row0, row1, r0, r1, waits]; omega
  · have hCut : (X.tr g).drop i =
        (r0 ++ [page0]) ++ rowStore0 :: ((r1 ++ [page1, rowStore1] ++ waits) ++ rest) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hTrace'
    have h := cellValueFromTrace hX hCut (by
      intro e he
      rcases List.mem_append.mp he with h | h
      · rcases List.mem_append.mp h with h | h
        · exact primingPageNoClobber h
        · simp at h
          rcases h with rfl | rfl <;> exact savedMetadataNoClobber (Or.inr (by decide))
      · exact primingWaitNoClobber h)
    convert h using 1 <;> simp [row0, row1, r0, r1, waits]; omega
  · have hCut : (X.tr g).drop i =
        (r0 ++ [page0, rowStore0] ++ r1) ++ page1 :: (([rowStore1] ++ waits) ++ rest) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hTrace'
    have h := cellValueFromTrace hX hCut (by
      intro e he
      rcases List.mem_append.mp he with h | h
      · obtain rfl := List.mem_singleton.mp h
        exact savedMetadataNoClobber (Or.inl (by decide))
      · exact primingWaitNoClobber h)
    convert h using 1 <;> simp [row0, row1, r0, r1, waits]; omega
  · have hCut : (X.tr g).drop i =
        (r0 ++ [page0, rowStore0] ++ r1 ++ [page1]) ++ rowStore1 :: (waits ++ rest) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hTrace'
    have h := cellValueFromTrace hX hCut (fun _ hm => primingWaitNoClobber hm)
    convert h using 1 <;> simp [row0, row1, r0, r1, waits]; omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
