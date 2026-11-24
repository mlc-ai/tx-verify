-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKScratch
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKReload
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderMetadataHistory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue
open Thread.Loader (MetadataWord)
open Thread.Loader.LocalAccessCode

noncomputable section

/-- The indexed store is the last one covering these bytes before the cursor. -/
def PrimingCellValue (X : Execution) (g index pc : Nat) (cell : Acc) (data : List Byte) : Prop :=
  ∃ w < index, X.get (g, w) = some ⟨pc, .wr cell data⟩ ∧
    ∀ byte < cell.size, ∀ j < index, ∀ dst, X.Access (g, j) dst true →
      dst.Covers (cell.loc.at byte) → j ≤ w

/-- Advance the cursor across an actual event that cannot overwrite the cell. -/
theorem PrimingCellValue.step {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g index pc : Nat} {cell : Acc}
    {data : List Byte} (h : PrimingCellValue X g index pc cell data) {e : Event}
    (he : X.get (g, index) = some e) (hSafe : DoesNotClobber cell e) :
    PrimingCellValue X g (index + 1) pc cell data := by
  obtain ⟨w, hBefore, hew, hLast⟩ := h
  refine ⟨w, by omega, hew, ?_⟩
  intro byte hb j hj dst ha hc
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
  · exact hLast byte hb j hlt dst ha hc
  · exact False.elim (writeAccessDoesNotCover hX he hSafe ha hb hc)

/-- Immediately after a store, its payload is the latest write to its slot. -/
theorem primingCellValue_write {X : Execution} {g index pc : Nat} {cell : Acc} {data : List Byte}
    (he : X.get (g, index) = some ⟨pc, .wr cell data⟩) :
    PrimingCellValue X g (index + 1) pc cell data :=
  ⟨index, by omega, he, fun _ _ _ hj _ _ _ => Nat.le_of_lt_succ hj⟩

def primingMetadataPc : MetadataWord → Nat
  | .page => 506
  | .row => 511

def primingMetadataValue (p : Params) (batch row : Nat) : MetadataWord → Nat
  | .page => primingScratchPage p batch row
  | .row => row % 16

/-- Both prepared metadata words of a lane's scratch slot at this cursor. -/
def PrimingMetadataAt (p : Params) (l : Launch) (X : Execution)
    (g index batch row : Nat) (slot : Fin 2) : Prop :=
  ∀ word : MetadataWord, PrimingCellValue X g index (primingMetadataPc word)
    (metadataCell l g word slot) (b32 (primingMetadataValue p batch row word)).toBytes

/-- The registers carried unchanged across both K pointer stores and their branches. -/
def primingKPackFrame (p : Params) (l : Launch) (batch head tile warp lane : Nat) :
    List (Nat × Value) :=
  [(7294, b64 (l.localBase + 64)), (7295, b64 (l.localBase + 96)),
   (7495, b64 p.kLayout.pageStride), (7493, b64 p.kLayout.rowStride),
   (7300, b64 (p.kLayout.base + 2 * (head * p.kLayout.headStride)))] ++
    primingKMaskInputs p l batch tile warp lane

/-- Decode a K metadata iteration’s first page address. -/
theorem primingKPackAddress (l : Launch) (g : Nat) (slot : Fin 2)
    (hStack : l.localBase + 128 ≤ 2 ^ 32) :
    Seg kernel [] l g 3 522
      [(9535, b64 slot.val), (773, .pred (slot.val == 0)), (7295, b64 (l.localBase + 96))] 525
      [(5, .pred (slot.val == 0)), (7535, b64 (4 * slot.val)),
       (7536, b64 (l.localBase + kvLocalOffset 3 slot))] := by
  have hIdx := slot.isLt
  have hSlot : slot.val < 2 ^ 64 := by omega
  have hShift : 4 * slot.val < 2 ^ 64 := by omega
  have hBase : l.localBase + 96 < 2 ^ 64 := by omega
  have hEnd : l.localBase + 96 + 4 * slot.val < 2 ^ 64 := by omega
  have hOff : kvLocalOffset 3 slot = 96 + 4 * slot.val := by simp [kvLocalOffset]
  rw [hOff, ← Nat.add_assoc]
  intro s hs
  seg_fp hs using
    norm_bits [Nat.mod_eq_of_lt hSlot, Nat.mod_eq_of_lt hShift, Nat.mul_comm slot.val 4,
      Nat.mod_eq_of_lt hBase, Nat.mod_eq_of_lt hEnd]

/-- Seed the first K metadata reload iteration. -/
theorem primingKPackSeed (l : Launch) (g : Nat) :
    Seg kernel [] l g 2 520 [] 522 [(9535, b64 0), (773, .pred true)] := by
  intro s hs
  seg_fp hs using decide

/-- Move the K pointer pack to the first-slot retry or post-pack check. -/
theorem primingKPackAdvance (l : Launch) (g : Nat) :
    Seg kernel [] l g 2 535 [] 537 [(9535, b64 1), (773, .pred false)] := by
  intro s hs
  seg_fp hs using decide

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Execute the lane's actual page and row reads and save its packed K source pointer. -/
theorem primingKPackIterationInPrefix {g index batch head tile warp lane row : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads) (slot : Fin 2) {s : TState}
    (hs : At s 522 ((9535, b64 slot.val) :: (773, .pred (slot.val == 0)) ::
      primingKPackFrame p l batch head tile warp lane)) {ending : Option TState} {bound : Nat}
    (hBound : 534 ≤ bound) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hDemand : PrefixDemand X g index bound ending)
    (hMeta : PrimingMetadataAt p l X g index batch row slot) :
    X.get (g, index) = some ⟨525, .rd (metadataCell l g .page slot)
      ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩ ∧
    X.get (g, index + 1) = some ⟨527, .rd (metadataCell l g .row slot)
      ((b32 (row % 16)).toBytes.map some)⟩ ∧
    X.get (g, index + 2) = some ⟨534, .wr (sourceScratchAccess l g slot)
      (b64 (primingKRowPointer p batch head row)).toBytes⟩ ∧
    ∃ u, At u (if slot.val == 0 then 522 else 538)
        ((9535, b64 1) :: (773, .pred false) :: primingKPackFrame p l batch head tile warp lane) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 3)) ending ∧
      PrefixDemand X g (index + 3) bound ending := by
  let F := primingKPackFrame p l batch head tile warp lane
  let G := (9535, b64 slot.val) :: F
  obtain ⟨t, ht, hT⟩ := primingKPackAddress l g slot hp.localMemory.2.1 s (by at_select hs)
  obtain ⟨htA, hFrame⟩ := loaderLinear (regs := G.map Prod.fst) (by decide) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) ht
  have hG : Holds s.regs G := ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.2⟩
  have hHold := holdsSchedulerFrame hG hFrame (fun _ hm => List.mem_map_of_mem hm)
  let keep := (5, .pred (slot.val == 0)) :: F
  have hAt : At t 525 (primingKScratchInputs p l head slot ++ keep) := by
    refine hT.mono ((holds_append ..).mpr ⟨?_, hT.2.2.2.2.1, hHold.2⟩)
    have hKeep := hHold.2
    exact ⟨hT.2.2.2.2.2.2.1, hKeep.1, hT.2.2.2.2.2.1,
      hKeep.2.2.1, hKeep.2.2.2.1, hKeep.2.2.2.2.1, hHold.1,
      holds_lookup hKeep (by rfl), trivial⟩
  obtain ⟨w, hBefore, hPage, hPageLast⟩ := hMeta .page
  obtain ⟨r, hRowBefore, hRow, hRowLast⟩ := hMeta .row
  obtain ⟨he0, he1, v, he2, hV, hTail⟩ :=
    primingKScratchRowSavedFrameInPrefix hp hX hb hh slot
      (by simp [keep, F, primingKPackFrame, primingKMaskInputs])
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      hAt hBound (hr.after_local_nonempty (run_rtg htA) (hDemand.nonempty hr)) hDemand
      hBefore (by omega) hPage hRow hPageLast hRowLast
  obtain ⟨z, hz, hZ⟩ := primingKPackAdvance l g v (hV.mono trivial)
  obtain ⟨hzA, hZFrame⟩ := loaderLinear (regs := keep.map Prod.fst)
    (by decide) (by decide) hV.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hz
  have hZKeep := holdsSchedulerFrame hV.2.2.2.2.2 hZFrame (fun _ hm => List.mem_map_of_mem hm)
  have hBranch : At z 537 ((9535, b64 1) :: (773, .pred false) :: F) :=
    hZ.mono ⟨hZ.2.2.2.2.1, hZ.2.2.2.2.2.1, hZKeep.2⟩
  obtain ⟨u, hu, hU⟩ := run_bra (A := []) (L := l) (g := g) Flow.code_537
    (slot.val == 0) hBranch hZKeep.1 (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hBranch.1
    (by set_option maxRecDepth 100000 in kernel_rfl) (by decide) hu
  have hNext := hDemand.advance he0 ((by decide : 525 ≤ 534).trans hBound)
  have hThird : PrefixDemand X g (index + 2) bound ending := by
    simpa only [Nat.add_assoc] using hNext.advance he1 ((by decide : 527 ≤ 534).trans hBound)
  have hAfter : PrefixDemand X g (index + 3) bound ending := by
    simpa only [Nat.add_assoc] using hThird.advance he2 hBound
  exact ⟨he0, he1, he2, u, hU,
    hTail.after_local_nonempty (run_rtg (run_comp hzA huA)) (hAfter.nonempty hTail), hAfter⟩

omit hp hX in
private theorem primingKMetadataStep {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g index batch row : Nat}
    {slot : Fin 2} (h : PrimingMetadataAt p l X g index batch row slot) {e : Event}
    (he : X.get (g, index) = some e)
    (hSafe : ∀ word, DoesNotClobber (metadataCell l g word slot) e) :
    PrimingMetadataAt p l X g (index + 1) batch row slot :=
  fun word => (h word).step hX he (hSafe word)

/-- The two metadata iterations save independent K row pointers in the lane's stack. -/
theorem primingKPackSavedCellsInPrefix {g index batch head tile warp lane : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads) {s : TState}
    (hs : At s 520 (primingKPackFrame p l batch head tile warp lane)) {ending : Option TState}
    {bound : Nat} (hBound : 534 ≤ bound)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hDemand : PrefixDemand X g index bound ending)
    (hMeta : ∀ slot : Fin 2, PrimingMetadataAt p l X g index batch
      (primingLaneRow tile (32 * warp + lane) + 64 * slot.val) slot) :
    let row := primingLaneRow tile (32 * warp + lane)
    ∃ u, At u 538 (primingKMaskInputs p l batch tile warp lane) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 6)) ending ∧
      PrefixDemand X g (index + 6) bound ending ∧
      (∀ slot : Fin 2, PrimingCellValue X g (index + 6) 534 (sourceScratchAccess l g slot)
        (b64 (primingKRowPointer p batch head (row + 64 * slot.val))).toBytes) ∧
      ∃ pre : List Event, pre.length = 6 ∧
        (X.tr g).drop index = pre ++ (X.tr g).drop (index + 6) ∧
        pre.countP Execution.isShfl = 0 ∧ pre.countP isFullWarpVote = 0 := by
  let row := primingLaneRow tile (32 * warp + lane)
  let F := primingKPackFrame p l batch head tile warp lane
  obtain ⟨t, ht, hT⟩ := primingKPackSeed l g s (hs.mono trivial)
  obtain ⟨htA, hFrame⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) ht
  have hKeep := holdsSchedulerFrame hs.2.2.2.2 hFrame (fun _ hm => List.mem_map_of_mem hm)
  have hSeed : At t 522 ((9535, b64 0) :: (773, .pred true) :: F) :=
    hT.mono ⟨hT.2.2.2.2.1, hT.2.2.2.2.2.1, hKeep⟩
  have hFirst : PrimingMetadataAt p l X g index batch row 0 := hMeta 0
  obtain ⟨he0, he1, he2, v, hV, hTail, hFirstDemand⟩ :=
    primingKPackIterationInPrefix hp hX hb hh 0 hSeed hBound
      (hr.after_local_nonempty (run_rtg htA) (hDemand.nonempty hr)) hDemand hFirst
  have hSecond : PrimingMetadataAt p l X g index batch (row + 64) 1 := hMeta 1
  have hMeta0 := primingKMetadataStep hX hSecond he0 (by intro _ _ _ h; cases h)
  have hMeta1 := primingKMetadataStep hX hMeta0 he1 (by intro _ _ _ h; cases h)
  have hMeta2 := primingKMetadataStep hX hMeta1 he2 (by
    intro word dst data hEq
    obtain ⟨rfl, _⟩ := Kind.wr.inj hEq
    exact metadataPointerApart (p := pointerPacket 0) (by decide) word 1 0)
  have hMetaNext : PrimingMetadataAt p l X g (index + 3) batch (row + 64) 1 := by
    simpa only [Nat.add_assoc] using hMeta2
  obtain ⟨he3, he4, he5, u, hU, hRest, hSecondDemand⟩ :=
    primingKPackIterationInPrefix hp hX hb hh 1 hV hBound hTail hFirstDemand hMetaNext
  have hFirstWrite := primingCellValue_write he2
  have hSave0 := hFirstWrite.step hX he3 (by intro _ _ h; cases h)
  have hSave1 := hSave0.step hX he4 (by intro _ _ h; cases h)
  have hSave2 := hSave1.step hX he5 (by
    intro dst data hEq
    obtain ⟨rfl, _⟩ := Kind.wr.inj hEq
    exact cellsApart (p := pointerPacket 0) (by decide))
  have hSave (slot : Fin 2) : PrimingCellValue X g (index + 6) 534
      (sourceScratchAccess l g slot)
      (b64 (primingKRowPointer p batch head (row + 64 * slot.val))).toBytes := by
    have hSlots : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    rcases hSlots slot with rfl | rfl
    · simpa only [Nat.add_assoc, Nat.reduceAdd, Fin.val_zero, Nat.mul_zero, Nat.add_zero]
        using hSave2
    · simpa only [Nat.add_assoc, Nat.reduceAdd, Fin.val_one, Nat.mul_one]
        using primingCellValue_write he5
  refine ⟨u, hU.mono ((holds_append ..).mp hU.2.2.2.2.2.2).2,
    by simpa only [Nat.add_assoc] using hRest,
    by simpa only [Nat.add_assoc] using hSecondDemand, hSave,
    [⟨525, .rd (metadataCell l g .page 0)
      ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩,
     ⟨527, .rd (metadataCell l g .row 0) ((b32 (row % 16)).toBytes.map some)⟩,
     ⟨534, .wr (sourceScratchAccess l g 0) (b64 (primingKRowPointer p batch head row)).toBytes⟩,
     ⟨525, .rd (metadataCell l g .page 1)
       ((b32 (primingScratchPage p batch (row + 64))).toBytes.map some)⟩,
     ⟨527, .rd (metadataCell l g .row 1) ((b32 ((row + 64) % 16)).toBytes.map some)⟩,
     ⟨534, .wr (sourceScratchAccess l g 1)
       (b64 (primingKRowPointer p batch head (row + 64))).toBytes⟩], rfl, ?_, rfl, rfl⟩
  have h0 := List.getElem?_eq_some_iff.mp he0
  have h1 := List.getElem?_eq_some_iff.mp he1
  have h2 := List.getElem?_eq_some_iff.mp he2
  have h3 := List.getElem?_eq_some_iff.mp he3
  have h4 := List.getElem?_eq_some_iff.mp he4
  have h5 := List.getElem?_eq_some_iff.mp he5
  rw [List.drop_eq_getElem_cons h0.1, h0.2, List.drop_eq_getElem_cons h1.1, h1.2,
    List.drop_eq_getElem_cons h2.1, h2.2, List.drop_eq_getElem_cons h3.1, h3.2,
    List.drop_eq_getElem_cons h4.1, h4.2, List.drop_eq_getElem_cons h5.1, h5.2]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Loader
