-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstCacheReload
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open Thread.Loader.LocalAccessCode

noncomputable section

private theorem afterKeyPackSlot {p : Params} {l : Launch}
    {g batch head tile warp lane row : Nat} (slot : Fin 2) {s : TState}
    (hs : At s 535 ((7543,b64 (primingKRowPointer p batch head row)) ::
      (5,.pred (slot.val==0)) :: primingKPackFrame p l batch head tile warp lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if slot.val==0 then 522 else 538)
        (primingKPackIterationFrame p l batch head tile warp 1 lane) := by
  let F := (5,.pred (slot.val==0)) :: primingKPackFrame p l batch head tile warp lane
  obtain ⟨z,hz,hZ⟩ := primingKPackAdvance l g s (hs.mono trivial)
  obtain ⟨hzA,hFrame⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hz
  have hF := holdsSchedulerFrame hs.2.2.2.2.2 hFrame (fun _ hm => List.mem_map_of_mem hm)
  have hBranch : At z 537 (primingKPackIterationFrame p l batch head tile warp 1 lane) :=
    hZ.mono ⟨hZ.2.2.2.2.1,hZ.2.2.2.2.2.1,hF.2⟩
  obtain ⟨u,hu,hU⟩ := run_bra (A := []) (L := l) (g := g) Flow.code_537
    (slot.val==0) hBranch hF.1 (by simp)
  have huA := (loaderLinear (regs := []) (by decide) (by decide) hBranch.1
    (by simp) (by decide) hu).1
  exact ⟨u,run_rtg (run_comp hzA huA),hU⟩

/-- Three concrete events of one K page-pointer scratch pack. -/
def primingKeyPackEvents (p : Params) (l : Launch) (g batch head row : Nat) (slot : Fin 2) :
    List Event :=
  [⟨525,.rd (scratchWordAccess l g 0 slot)
    ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩,
   ⟨527,.rd (scratchWordAccess l g 1 slot) ((b32 (row%16)).toBytes.map some)⟩,
   ⟨534,.wr (sourceScratchAccess l g slot) (b64 (primingKRowPointer p batch head row)).toBytes⟩]

private theorem dropOne {X : Execution} {g j : Nat} {e : Event}
    (he : X.get (g,j) = some e) : (X.tr g).drop j = e :: (X.tr g).drop (j+1) := by
  have h := List.getElem?_eq_some_iff.mp he
  rw [List.drop_eq_getElem_cons h.1,h.2]

/-- Every lane executes the two local reads and pointer save of this selected K slot. -/
theorem primingKeyPackSlotOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch head tile shuffles votes : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hh : head < p.kvHeads)
    (slot : Fin 2) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 522
      (primingKPackIterationFrame p l batch head tile (warpIndex l g) slot) shuffles votes ends)
    (hMeta : ∀ lane < 32, PrimingMetadataAt p l X (warpLane l g lane) (cur.pos lane) batch
      (primingLaneRow tile (32*warpIndex l g+lane)+64*slot.val) slot) :
    ∃ done : SchedulerWarpReached l X g (if slot.val==0 then 522 else 538)
      (primingKPackIterationFrame p l batch head tile (warpIndex l g) 1) shuffles votes ends,
      (∀ lane < 32, done.pos lane = cur.pos lane+3) ∧
      ∀ lane < 32,
        let thread := warpLane l g lane
        let row := primingLaneRow tile (32*warpIndex l g+lane)+64*slot.val
        (X.tr thread).drop (cur.pos lane) =
          primingKeyPackEvents p l thread batch head row slot ++
            (X.tr thread).drop (done.pos lane) := by
  classical
  let thread := warpLane l g
  let row := fun lane => primingLaneRow tile (32*warpIndex l g+lane)+64*slot.val
  let events := fun lane => primingKeyPackEvents p l (thread lane) batch head (row lane) slot
  let stop := fun lane => cur.pos lane+3
  have hLane (lane : Nat) (hl : lane < 32) : ∃ v u,
      (X.tr (thread lane)).drop (cur.pos lane) =
        events lane ++ (X.tr (thread lane)).drop (stop lane) ∧
      At u (if slot.val==0 then 522 else 538)
        (primingKPackIterationFrame p l batch head tile (warpIndex l g) 1 lane) ∧
      Run kernel Assumptions.all l (thread lane) {}
        ((X.tr (thread lane)).take (stop lane)) (some v) ∧
      Run kernel Assumptions.all l (thread lane) v
        ((X.tr (thread lane)).drop (stop lane)) (ends lane) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) v u ∧
      stop lane ≤ (X.tr (thread lane)).length ∧
      (stop lane = (X.tr (thread lane)).length → Step.Released l X (thread lane)) := by
    obtain ⟨hPage,hRow,hStore,v,hV,hPrefix,hTail⟩ :=
      primingKeyPointerStoredAtSlot hp hMax hg hw hb hh slot cur hl (hMeta lane hl)
    obtain ⟨u,hLocal,hAt⟩ := afterKeyPackSlot (g := thread lane) slot hV
    have hKept : stop lane = (cur.pos lane+2)+1 := by simp [stop,Nat.add_assoc]
    refine ⟨v,u,?_,hAt,hPrefix,hTail,hLocal,?_,?_⟩
    · rw [dropOne hPage,dropOne hRow,show cur.pos lane+1+1 = cur.pos lane+2 by omega,
        dropOne hStore,hKept]
      rfl
    · rw [hKept]; exact len_of_get hStore
    · rw [hKept]; exact releasedIfLast hStore (by intro h; cases h)
  let _ : Inhabited TState := ⟨{}⟩
  choose! v u hTrace hAt hPrefix hTail hLocal hBound hRelease using hLane
  have hOrd := cur.ordinals.advance events (fun lane hl => ⟨_,hTrace lane hl⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨⟨⟨stop,v,u,hOrd,hTail,hLocal,hAt⟩,
    fun lane hl => (cur.positive lane hl).trans_le (Nat.le_add_right _ _),hBound,hRelease,hPrefix⟩,
    fun _ _ => rfl,hTrace⟩

private theorem keyPackGet {p : Params} {l : Launch} {X : Execution}
    {thread pos batch head row : Nat} {slot : Fin 2} {tail : List Event}
    (hTrace : (X.tr thread).drop pos =
      primingKeyPackEvents p l thread batch head row slot ++ tail) :
    X.get (thread,pos) = some ⟨525,.rd (scratchWordAccess l thread 0 slot)
      ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩ ∧
    X.get (thread,pos+1) = some ⟨527,.rd (scratchWordAccess l thread 1 slot)
      ((b32 (row%16)).toBytes.map some)⟩ ∧
    X.get (thread,pos+2) = some ⟨534,.wr (sourceScratchAccess l thread slot)
      (b64 (primingKRowPointer p batch head row)).toBytes⟩ := by
  have index (k : Nat) (hk : k < 3) :
      X.get (thread,pos+k) = (primingKeyPackEvents p l thread batch head row slot)[k]? := by
    change (X.tr thread)[pos+k]? = _
    rw [← List.getElem?_drop,hTrace,List.getElem?_append_left hk]
  have hFirst := index 0 (by decide)
  rw [Nat.add_zero] at hFirst
  exact ⟨hFirst,index 1 (by decide),index 2 (by decide)⟩

/-- Both real K scratch packs write the exact pointers and preserve the first until reload. -/
theorem primingKeyPointersReadyOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch head tile shuffles votes : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hh : head < p.kvHeads) {ends : Nat → Option TState}
    (cur : PrimingKeyEmptyReady p l X g batch head tile shuffles votes ends)
    (hMeta : PrimingKeyMetadataReady cur) :
    ∃ ready : SchedulerWarpReached l X g 538
      (primingKMaskInputs p l batch tile (warpIndex l g)) shuffles votes ends,
      ∀ lane < 32, ∀ slot : Fin 2,
        let thread := warpLane l g lane
        let row := primingLaneRow tile (32*warpIndex l g+lane)+64*slot.val
        PrimingCellValue X thread (ready.pos lane) 534 (sourceScratchAccess l thread slot)
          (b64 (primingKRowPointer p batch head row)).toBytes := by
  obtain ⟨start,hStart⟩ := seedPrimingKeyPack cur
  obtain ⟨first,hFirst,hTrace₀⟩ := primingKeyPackSlotOfMaximal hp hMax hg hw hb hh 0 start
    (fun lane hl => by simpa only [hStart] using hMeta lane hl 0)
  have hNext (lane : Nat) (hl : lane < 32) :
      PrimingMetadataAt p l X (warpLane l g lane) (first.pos lane) batch
        (primingLaneRow tile (32*warpIndex l g+lane)+64*(1 : Fin 2).val) 1 := by
    obtain ⟨he₀,he₁,he₂⟩ := keyPackGet (hTrace₀ lane hl)
    intro word
    have hm := hMeta lane hl 1 word
    rw [← hStart] at hm
    have ha := hm.step hMax.1 he₀ (by intro _ _ h; cases h)
    have hb := ha.step hMax.1 he₁ (by intro _ _ h; cases h)
    have hc := hb.step hMax.1 he₂ (by
      intro dst data hEq
      obtain ⟨rfl,_⟩ := Kind.wr.inj hEq
      exact metadataPointerApart (p := pointerPacket 0) (by decide) word 1 0)
    rw [hFirst lane hl]
    exact hc
  obtain ⟨second,hSecond,hTrace₁⟩ := primingKeyPackSlotOfMaximal hp hMax hg hw hb hh 1 first hNext
  obtain ⟨out,hPos,hBefore⟩ := second.toSchedulerWarpAt.advanceLocalPreserving (pc' := 538)
    (G := primingKMaskInputs p l batch tile (warpIndex l g)) (fun lane hl => by
      have hs := second.checkpoint lane hl
      exact ⟨_,.refl,hs.mono ((holds_append ..).mp hs.2.2.2.2.2.2).2⟩)
  refine ⟨second.reframe out hPos hBefore,?_⟩
  intro lane hl slot
  change PrimingCellValue X (warpLane l g lane) (out.pos lane) 534 _ _
  rw [hPos,hSecond lane hl]
  obtain ⟨he₀,he₁,he₂⟩ := keyPackGet (hTrace₁ lane hl)
  have hSlots : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  rcases hSlots slot with rfl | rfl
  · obtain ⟨_,_,he⟩ := keyPackGet (hTrace₀ lane hl)
    have hKeep := primingCellValue_write he
    rw [show start.pos lane+2+1 = first.pos lane by rw [hFirst lane hl]] at hKeep
    have ha := hKeep.step hMax.1 he₀ (by intro _ _ h; cases h)
    have hb := ha.step hMax.1 he₁ (by intro _ _ h; cases h)
    have hc := hb.step hMax.1 he₂ (by
      intro dst data hEq
      obtain ⟨rfl,_⟩ := Kind.wr.inj hEq
      exact cellsApart (p := pointerPacket 0) (by decide))
    exact hc
  · exact primingCellValue_write he₂

end
end PTX.Kernels.TmlFa4Fwd.Loader
