-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVFromK
import Kernels.TmlFa4Fwd.Flow.Code.Part012

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue
open Thread.Loader.LocalAccessCode

noncomputable section

/-- Facts that survive both pointer stores and the local loop between them. -/
structure PrimingVPackFrame (F : List (Nat × Value)) : Prop where
  rowAddress : ((kernel.code.drop 791).take 1).all
    (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  storePrep : ((kernel.code.drop 793).take 6).all
    (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  loopSeed : ((kernel.code.drop 800).take 2).all
    (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  nextAddress : ((kernel.code.drop 787).take 3).all
    (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  fresh : ∀ pair ∈ F, pair.1 ≠ 7601 ∧ pair.1 ≠ 7603

/-- The second scratch iteration selects the second saved page word. -/
theorem primingVSecondAddress {l : Launch} {g : Nat}
    (hStack : l.localBase + 128 ≤ 2 ^ 32) :
    Seg kernel [] l g 3 787
      [(9536, b64 1), (774, .pred false), (7295, b64 (l.localBase + 96))] 790
      (primingVScratchSlotFacts l 1 ++ [(6, .pred false)]) := by
  have hBase : l.localBase + 96 < 2 ^ 64 := by omega
  have hEnd : l.localBase + 100 < 2 ^ 64 := by omega
  intro s hs
  change ∃ u, run kernel [] l g 3 s = some u ∧ At u 790
    [(7600, b64 (l.localBase + 100)), (7599, b64 4), (9536, b64 1), (6, .pred false)]
  seg_fp hs using first | rfl | norm_bits [Nat.mod_eq_of_lt hBase, Nat.mod_eq_of_lt hEnd]

/-- The first V pointer store seeds the second scratch iteration. -/
theorem primingVLoopSeed (l : Launch) (g : Nat) :
    Seg kernel [] l g 2 800 [] 802 [(9536, b64 1), (774, .pred false)] := by
  intro s hs
  seg_fp hs using decide

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem primingVPackIteration (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g batch head row index : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads) (slot : Fin 2) {s : TState}
    {F : List (Nat × Value)} (hF : PrimingVPackFrame F) (hAbi : primingVScratchAbi p l head ⊆ F)
    (hs : At s 790 (primingVScratchSlotFacts l slot ++ (6, .pred (slot.val == 0)) :: F))
    {ending : Option TState} (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {bound : Nat} (hBound : 799 ≤ bound) (hDemand : PrefixDemand X g index bound ending)
    (hMeta : PrimingMetadataAt p l X g index batch row slot) :
    X.get (g, index) = some ⟨790, .rd (scratchWordAccess l g 2 slot)
      ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩ ∧
    X.get (g, index + 1) = some ⟨792, .rd (scratchWordAccess l g 3 slot)
      ((b32 (row % 16)).toBytes.map some)⟩ ∧
    X.get (g, index + 2) = some ⟨799, .wr (sourceScratchAccess l g slot)
      (b64 (primingVRowPointer p batch head row)).toBytes⟩ ∧
    ∃ u, At u (if slot.val == 0 then 787 else 803)
        ([(9536, b64 1), (774, .pred false)] ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 3)) ending ∧
      PrefixDemand X g (index + 3) bound ending := by
  let carry := (6, .pred (slot.val == 0)) :: F
  obtain ⟨hPage, hRow, t, hStore, hAt, hRun⟩ := primingVScratchSavedInPrefix hp hX hb hh slot
    (fun _ h => List.mem_cons_of_mem _ (hAbi h))
    (by
      intro pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · change 6 ≠ 7601 ∧ 6 ≠ 7603
        decide
      · exact hF.fresh pair hm)
    (primingKeepAppend (F := [(6, .pred (slot.val == 0))])
      (by set_option maxRecDepth 100000 in kernel_rfl) hF.rowAddress)
    (primingKeepAppend (F := [(6, .pred (slot.val == 0))])
      (by set_option maxRecDepth 100000 in kernel_rfl) hF.storePrep)
    hs hr hBound hDemand hMeta
  obtain ⟨v, hv, hV⟩ := primingVLoopSeed l g t (hAt.mono trivial)
  obtain ⟨hvA, keep⟩ := loaderLinear (regs := carry.map Prod.fst) (by decide) (by decide) hAt.1
    (primingKeepAppend (F := [(6, .pred (slot.val == 0))])
      (by set_option maxRecDepth 100000 in kernel_rfl) hF.loopSeed)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hKeep : Holds v.regs carry :=
    holdsSchedulerFrame hAt.2.2.2.2.2 keep (fun _ hm => List.mem_map_of_mem hm)
  have hAtBranch : At v 802 ([(9536, b64 1), (774, .pred false)] ++ F) :=
    hV.mono ((holds_append ..).mpr ⟨hV.2.2.2.2, hKeep.2⟩)
  obtain ⟨u, hu, hU⟩ := run_bra (A := []) (L := l) (g := g) Flow.code_802
    (slot.val == 0) hAtBranch hKeep.1 (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hAtBranch.1
    (by set_option maxRecDepth 100000 in kernel_rfl) (by decide) hu
  have hDemand' : PrefixDemand X g (index + 3) bound ending := by
    have h0 := hDemand.advance hPage ((show 790 ≤ 799 by decide).trans hBound)
    have h1 := h0.advance hRow ((show 792 ≤ 799 by decide).trans hBound)
    have h2 := h1.advance (by simpa only [Nat.add_assoc] using hStore) hBound
    simpa only [Nat.add_assoc] using h2
  exact ⟨hPage, hRow, hStore, u, hU,
    hRun.after_local_nonempty (run_rtg (run_comp hvA huA)) (hDemand'.nonempty hRun), hDemand'⟩

/-- Both second-iteration metadata words survive the first pointer store. -/
theorem primingVSecondMetadata (hX : Consistent l kernel Assumptions.all m X) {g i batch row : Nat}
    {pageAddr rowAddr : Acc} {pageBytes rowBytes : List (Option Byte)} {data : List Byte}
    (hMeta : PrimingMetadataAt p l X g i batch row 1)
    (hPage : X.get (g, i) = some ⟨790, .rd pageAddr pageBytes⟩)
    (hRow : X.get (g, i + 1) = some ⟨792, .rd rowAddr rowBytes⟩)
    (hStore : X.get (g, i + 2) = some ⟨799, .wr (sourceScratchAccess l g 0) data⟩) :
    PrimingMetadataAt p l X g (i + 3) batch row 1 := by
  intro w
  have h0 := (hMeta w).step hX hPage (by intro _ _ h; cases h)
  have h1 := h0.step hX hRow (by intro _ _ h; cases h)
  have h2 := h1.step hX (by simpa only [Nat.add_assoc] using hStore)
    (by
      intro dst bs h
      obtain ⟨rfl, _⟩ := Kind.wr.inj h
      exact metadataPointerApart (p := pointerPacket 0) (by decide) w 1 0)
  simpa only [Nat.add_assoc] using h2

def primingVPackEvents (p : Params) (l : Launch) (g batch head row : Nat)
    (slot : Fin 2) : List Event :=
  [⟨790, .rd (scratchWordAccess l g 2 slot)
     ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩,
   ⟨792, .rd (scratchWordAccess l g 3 slot) ((b32 (row % 16)).toBytes.map some)⟩,
   ⟨799, .wr (sourceScratchAccess l g slot) (b64 (primingVRowPointer p batch head row)).toBytes⟩]

/-- The first V scratch loop writes both row pointers. Each saved pointer is still the latest
write to its lane-local slot when the decoded loop reaches its exit. -/
theorem primingVPackSavedLaneInPrefix (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g i batch head : Nat} (hb : batch < p.batch)
    (hh : head < p.kvHeads) (row : Fin 2 → Nat) {s : TState} {F : List (Nat × Value)}
    (hF : PrimingVPackFrame F) (hAbi : primingVScratchAbi p l head ⊆ F)
    (hStack : (7295, b64 (l.localBase + 96)) ∈ F) (hs : At s 790 (primingVFirstScratchFacts l ++ F))
    {ending : Option TState} (hr : Run kernel Assumptions.all l g s ((X.tr g).drop i) ending)
    {bound : Nat} (hBound : 799 ≤ bound) (hDemand : PrefixDemand X g i bound ending)
    (hMeta : ∀ slot, PrimingMetadataAt p l X g i batch (row slot) slot) :
    ∃ u, At u 803 F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop (i + 6)) ending ∧
      PrefixDemand X g (i + 6) bound ending ∧
      (X.tr g).drop i = primingVPackEvents p l g batch head (row 0) 0 ++
        primingVPackEvents p l g batch head (row 1) 1 ++ (X.tr g).drop (i + 6) ∧
      ∀ slot, PrimingCellValue X g (i + 6) 799 (sourceScratchAccess l g slot)
        (b64 (primingVRowPointer p batch head (row slot))).toBytes := by
  have hHold := (holds_append ..).mp hs.2.2.2.2
  have hEntry : At s 790 (primingVScratchSlotFacts l 0 ++ (6, .pred true) :: F) :=
    hs.mono ((holds_append ..).mpr
      ⟨⟨hHold.1.1, hHold.1.2.1, hHold.1.2.2.1, trivial⟩, hHold.1.2.2.2.2.1, hHold.2⟩)
  obtain ⟨hP0, hR0, hS0, v, hV, hTail, hStill⟩ :=
    primingVPackIteration hp hX hb hh 0 hF hAbi hEntry hr hBound hDemand (hMeta 0)
  obtain ⟨t, ht, hT⟩ := primingVSecondAddress hp.localMemory.2.1 v (hV.mono
    ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.1, holds_mem hV.2.2.2.2.2.2 hStack, trivial⟩)
  obtain ⟨htA, keep⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hV.1
    hF.nextAddress (by set_option maxRecDepth 100000 in kernel_rfl) ht
  have hEnter : At t 790 (primingVScratchSlotFacts l 1 ++ (6, .pred false) :: F) :=
    hT.mono ((holds_append ..).mpr ⟨((holds_append ..).mp hT.2.2.2.2).1,
      ((holds_append ..).mp hT.2.2.2.2).2.1,
      holdsSchedulerFrame hV.2.2.2.2.2.2 keep (fun _ hm => List.mem_map_of_mem hm)⟩)
  obtain ⟨hP1, hR1, hS1, u, hU, hRest, hLater⟩ := primingVPackIteration hp hX hb hh 1 hF hAbi hEnter
    (hTail.after_local_nonempty (run_rtg htA) (hStill.nonempty hTail))
    hBound hStill (primingVSecondMetadata hX (hMeta 1) hP0 hR0 hS0)
  have hLatest0 := primingCellValue_write hS0
  have hKeep0 := hLatest0.step hX (by simpa only [Nat.add_assoc] using hP1)
    (by intro _ _ h; cases h)
  have hKeep1 := hKeep0.step hX (by simpa only [Nat.add_assoc] using hR1)
    (by intro _ _ h; cases h)
  have hKeep2 := hKeep1.step hX (by simpa only [Nat.add_assoc] using hS1)
    (by
      intro dst bs h
      obtain ⟨rfl, _⟩ := Kind.wr.inj h
      exact cellsApart (p := pointerPacket 0) (by decide))
  refine ⟨u, hU.mono hU.2.2.2.2.2.2, by simpa only [Nat.add_assoc] using hRest,
    by simpa only [Nat.add_assoc] using hLater, ?_, ?_⟩
  · have h0 := List.getElem?_eq_some_iff.mp hP0
    have h1 := List.getElem?_eq_some_iff.mp hR0
    have h2 := List.getElem?_eq_some_iff.mp hS0
    have h3 := List.getElem?_eq_some_iff.mp hP1
    have h4 := List.getElem?_eq_some_iff.mp hR1
    have h5 := List.getElem?_eq_some_iff.mp hS1
    rw [List.drop_eq_getElem_cons h0.1, h0.2, List.drop_eq_getElem_cons h1.1, h1.2,
      List.drop_eq_getElem_cons h2.1, h2.2, List.drop_eq_getElem_cons h3.1, h3.2,
      List.drop_eq_getElem_cons h4.1, h4.2, List.drop_eq_getElem_cons h5.1, h5.2]
    rfl
  intro slot
  have hSlots : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  rcases hSlots slot with rfl | rfl
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using hKeep2
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using primingCellValue_write hS1

end
end PTX.Kernels.TmlFa4Fwd.Loader
