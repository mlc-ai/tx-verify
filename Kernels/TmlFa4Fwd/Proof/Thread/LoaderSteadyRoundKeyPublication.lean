-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadyRoundKeyPacket
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderKeyPublicationProgress
import all Kernels.TmlFa4Fwd.Proof.LoaderSteadyOperandReload
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Flow.CountTake
import Lemmas.Flow.NthEv
import Kernels.TmlFa4Fwd.Flow.Code.Part023
import Kernels.TmlFa4Fwd.Flow.Code.Part024
import Kernels.TmlFa4Fwd.Flow.Code.Part025

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

set_option maxRecDepth 4096 in
/-- The upper half of the steady K packet reloads the second saved pointer before its first
exchange. -/
theorem steadyRoundKeyUpperOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round ordinal votes : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (steadyKeyNextPc 8)
      (fun lane => steadyRoundKeyGroupFrame p l g batch round lane 0 8) ordinal votes ends)
    (hSaved : ∀ lane < 32, PrimingCellValue X (warpLane l g lane) (cur.pos lane) 1447
      (pointerSaveAccess l (warpLane l g lane) 2 1)
      (b64 (steadyRoundKeyPointer p l g batch round lane 1)).toBytes) :
    ∃ done : SchedulerWarpReached l X g (steadyKeyNextPc 9)
        (fun lane => steadyRoundKeyGroupFrame p l g batch round lane 1 9) (ordinal+2) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let ptr := fun lane => steadyRoundKeyPointer p l g batch round lane 1
  let F := fun lane =>
    [(220,Value.pred true)] ++ steadyRoundKeyGroupFrame p l g batch round lane 0 8
  obtain ⟨masked,hMasked⟩ := cur.advanceLocalWithPosition (pc' := 1537) (G := F) (by
    intro lane hl
    have hs := cur.checkpoint lane hl
    have hRes := steadyRoundKeyLive hp (lane := lane) hb hLo hHi hTrips 8
    have hIn : At (cur.state lane) 1536
        ([(2155,b32 (steadyRoundKeyResidual p l g batch round lane))] ++
          steadyRoundKeyGroupFrame p l g batch round lane 0 8) :=
      hs.mono ⟨holds_lookup hs.2.2.2.2 rfl,hs.2.2.2.2⟩
    obtain ⟨u,hu,hU⟩ := roundStraightFrame (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl) rfl
      (liveKeyCompareCore (l := l) (g := warpLane l g lane) (steadyKeyCompareCode 8)
        hRes.1 hRes.2) hIn
    exact ⟨u,run_rtg hu,hU⟩)
  obtain ⟨rel,_,hRel⟩ := (steadyPointerReload false 1).warpReadPreservingOfMaximal hp hMax hg
    (by decide) (steadyPointerReloadCode false 1) (steadyKeyReloadAddress hp 1).1
    (steadyKeyReloadAddress hp 1).2 (by decide) ptr
    (fun lane _ => (steadyRoundKeyPointerBounds hp (round := round) (lane := lane)
      hb hLo hHi 1).1) masked
    (fun lane _ => by
      simp [F,steadyPointerReload,pointerReloadBase,steadySpillSite,steadyRoundKeyGroupFrame,
        steadyKeyPairCarry,steadyRoundKeyPacked,steadyRoundKeyCarry,steadyRoundTileFrame,
        steadyRoundFrame,steadyCacheHeadFrame,steadyRoundCarry,warmRoundCarry,openingWarmFrame,
        warmStartFrame,warmPageRoots,warmLaneRoots])
    (fun lane _ pair hm => by
      have h : ((F lane).map Prod.fst).all (fun r => decide (r ≠ 2177 ∧ r ≠ 2178)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm)))
    (fun lane hl => by rw [hMasked]; exact hSaved lane hl)
  obtain ⟨start,hStart⟩ := rel.advanceLocalWithPosition (pc' := steadyPairShufflePc false 8)
    (G := fun lane => steadyWords false 8 (ptr lane) ++ (220,.pred true) ::
      steadyKeyPairCarry l (steadyKeyStage round) (warpLane l g lane%l.block)
        (steadyRoundKeyPacked p l g batch round lane ++ steadyKeySizes 8)) (by
    intro lane hl
    have hs := rel.checkpoint lane hl
    have h := hs.2.2.2.2
    have hGF : Holds (rel.state lane).regs (steadyRoundKeyGroupFrame p l g batch round lane 0 8) :=
      h.2.2.2
    exact ⟨rel.state lane,.refl,hs.mono ⟨h.1,h.2.1,h.2.2.1,
      ((holds_append _ (steadyWords false (steadyKeySlotPair 0) _) _).mp hGF).2⟩⟩)
  obtain ⟨done,hDone⟩ := steadyRoundKeyPairAfterMaskOfMaximal hp hMax hg hb hLo hHi 1 8
    (by decide) (by decide) start
  refine ⟨done,fun lane hl pc cell data hCell => hDone lane hl ?_⟩
  rw [hStart]
  apply (hRel lane hl).2
  rw [hMasked]
  exact hCell

private theorem steadyRoundKeyHalfOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round ordinal votes first : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (slot : Fin 2) (hFirst : 2 ≤ first ∧ 8*slot.val < first)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (steadyKeyNextPc first)
      (fun lane => steadyRoundKeyGroupFrame p l g batch round lane slot first) ordinal votes ends)
    (count : Nat) (hLast : first+count ≤ 8*(slot.val+1)) :
    ∃ done : SchedulerWarpReached l X g (steadyKeyNextPc (first+count))
        (fun lane => steadyRoundKeyGroupFrame p l g batch round lane slot (first+count))
        (ordinal+2*count) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  induction count with
  | zero => exact ⟨cur,fun _ _ _ _ _ h => h⟩
  | succ k ih =>
    obtain ⟨mid,hMid⟩ := ih (by omega)
    have hSlot := slot.isLt
    let pair : Fin 16 := ⟨first+k,by omega⟩
    have hNo : pair.val ≠ 8 := by
      fin_cases slot
      · change first+k+1 ≤ 8 at hLast
        change first+k ≠ 8
        omega
      · have h := hFirst.2
        change 8 < first at h
        change first+k ≠ 8
        omega
    have hEntry : steadyKeyNextPc (first+k) = steadyKeyComparePc pair := by
      simp [steadyKeyNextPc,pair,show first+k < 16 by omega]
    obtain ⟨mid',hMid'⟩ := mid.advanceLocalWithPosition (pc' := steadyKeyComparePc pair)
      (G := fun lane => steadyRoundKeyGroupFrame p l g batch round lane slot pair.val)
      (fun lane hl => ⟨mid.state lane,.refl,hEntry ▸ mid.checkpoint lane hl⟩)
    obtain ⟨done,hDone⟩ := steadyRoundKeyNextPairOfMaximal hp hMax hg hb hLo hHi hTrips slot pair
      (by dsimp [pair]; omega) ⟨by dsimp [pair]; omega,by dsimp [pair]; omega⟩ hNo mid'
    have hN : ordinal+2*k+2 = ordinal+2*(k+1) := by omega
    rw [← hN]
    exact ⟨done,fun lane hl _ _ _ h => hDone lane hl (by rw [hMid']; exact hMid lane hl h)⟩

/-- The registers of a steady round after its K publication: the packed K carry and the
sixteen copy sizes, which the V packet reuses. -/
def steadyRoundKeyDone (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  steadyRoundKeyPacked p l g batch round lane ++ steadyKeySizes 16

/-- The steady K packet of round `round` has returned its ready arrivals for all lanes. -/
structure SteadyRoundKeyPublished (p : Params) (l : Launch) (X : Execution)
    (g batch round : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 1603 (steadyRoundKeyDone p l g batch round)
    shuffles votes ends
  rank : shuffles = primingSearchShuffleCount batch+96+64*round
  published : ∀ lane < 32, ∃ i, i+1 = reached.pos lane ∧
    X.get (warpLane l g lane,i) = some ⟨reuseArrival 2,
      .asyncArrive (readyObject l (warpLane l g lane) (kvUseStage (cacheUseOfRound round))) true⟩
  metadata : ∀ lane < 32, ∀ slot isRow,
    steadyRoundMetadata p l X g batch round lane (reached.pos lane) slot isRow

set_option maxRecDepth 4096 in
/-- The refreshed pages of steady round `round` progress through the K acquire, the pointer
saves, all K vectors, the commit and the ready arrival. -/
theorem SteadyRoundPages.keyPublishedOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hReleased : cacheUseOfRound round/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round)))
    (c : SteadyRoundPages p l X g batch round) :
    Nonempty (SteadyRoundKeyPublished p l X g batch round) := by
  classical
  obtain ⟨acq,hAcq⟩ := c.acquireKeyOfMaximal hp hMax hFrame hg hw hb hLo hHi hReleased
  obtain ⟨saved,hSaved⟩ := steadyRoundKeyPointersOfMaximal hp hMax hg hw hb hLo hHi
    (cur := acq) hAcq
  obtain ⟨first,hFirst⟩ := steadyRoundKeyFirstPairsOfMaximal hp hMax hg hb hLo hHi hTrips saved
    (fun lane hl => (hSaved lane hl).1 0)
  obtain ⟨low,hLow⟩ := steadyRoundKeyHalfOfMaximal hp hMax hg hb hLo hHi hTrips (first := 2) 0
    (by decide) first 6 (by decide)
  obtain ⟨upper,hUpper⟩ := steadyRoundKeyUpperOfMaximal hp hMax hg hb hLo hHi hTrips low
    (fun lane hl => hLow lane hl (hFirst lane hl ((hSaved lane hl).1 1)))
  obtain ⟨cur,hCur⟩ := steadyRoundKeyHalfOfMaximal hp hMax hg hb hLo hHi hTrips (first := 9) 1
    (by decide) upper 7 (by decide)
  have hCells (lane : Nat) (hl : lane < 32) (slot : Fin 2) (isRow : Bool) :
      steadyRoundMetadata p l X g batch round lane (cur.pos lane) slot isRow :=
    hCur lane hl (hUpper lane hl (hLow lane hl (hFirst lane hl ((hSaved lane hl).2 slot isRow))))
  let threads := warpLane l g
  let use := cacheUseOfRound round
  let addr := l.sharedBase+8*steadyKeyStage round
  have hStage := steadyKeyStage_lt round
  let stop := fun lane => cur.pos lane+2
  let ev : Nat → Event := fun lane =>
    ⟨1602,.asyncArrive (readyObject l (threads lane) (kvUseStage use)) true⟩
  let es : Nat → List Event := fun lane => [⟨1601,.asyncCommit⟩,ev lane]
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hWidth : addr+(copyArrivalAddress (recurringPacketSite 2)).2 < 2^32 := by
    have h := hp.shared.2.1
    change l.sharedBase+8*steadyKeyStage round+32 < 2^32
    omega
  have hAlign : addr%8 = 0 := by
    have h := hp.shared.1
    dsimp [addr]
    omega
  have hLane (lane : Nat) (hl : lane < 32) : ∃ u,
      (X.tr (threads lane)).drop (cur.pos lane) =
        es lane ++ (X.tr (threads lane)).drop (stop lane) ∧
      At u 1603 (steadyRoundKeyDone p l g batch round lane) ∧
      Run kernel Assumptions.all l (threads lane) {} ((X.tr (threads lane)).take (stop lane))
        (some u) ∧
      Run kernel Assumptions.all l (threads lane) u ((X.tr (threads lane)).drop (stop lane))
        (c.ends lane) ∧
      stop lane ≤ (X.tr (threads lane)).length ∧
      (stop lane = (X.tr (threads lane)).length → Step.Released l X (threads lane)) ∧
      X.get (threads lane,cur.pos lane+1) = some (ev lane) ∧
      ∀ slot isRow, steadyRoundMetadata p l X g batch round lane (stop lane) slot isRow := by
    have hActor := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    have hs := cur.checkpoint lane hl
    have hG := hs.2.2.2.2
    have hDone : Holds (cur.state lane).regs (steadyRoundKeyDone p l g batch round lane) :=
      ((holds_append ..).mp ((holds_append ..).mp hG).2).2
    have hAt : At (cur.state lane) (copyCommitPc (recurringPacketSite 2))
        [((copyArrivalAddress (recurringPacketSite 2)).1,b32 addr)] :=
      hs.mono ⟨holds_lookup hDone rfl,trivial⟩
    obtain ⟨hc,ha,hPast,hTail⟩ := copyCommitAndArriveOfMaximal hMax
      (g := threads lane) hActor (recurringPacketSite 2) hAt hWidth hAlign
      (cur.localSteps lane hl) (cur.recorded lane hl) (cur.continuation lane hl)
      (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl)
    have hLoc : (⟨.shared,threads lane/l.block,addr+32⟩ : Loc) =
        readyObject l (threads lane) (kvUseStage use) := by
      change _ = initObject l (threads lane/l.block) (readySlot (kvUseStage use))
      rw [readySlot_address]
      congr 1
    change X.get (threads lane,cur.pos lane+1) =
      some ⟨1602,.asyncArrive ⟨.shared,threads lane/l.block,addr+32⟩ true⟩ at ha
    rw [hLoc] at ha
    have hStop : stop lane = cur.pos lane+1+1 := rfl
    have hFrameAt : At (next (next (cur.state lane))) 1603
        (steadyRoundKeyDone p l g batch round lane) :=
      hs.next.next.mono hDone
    refine ⟨_,?_,hFrameAt,hPast,hTail,?_,?_,ha,fun slot isRow => ?_⟩
    · change (X.tr (threads lane))[cur.pos lane]? = some ⟨1601,.asyncCommit⟩ at hc
      change (X.tr (threads lane))[cur.pos lane+1]? = some (ev lane) at ha
      have hlo := List.getElem?_eq_some_iff.mp hc
      have hhi := List.getElem?_eq_some_iff.mp ha
      rw [List.drop_eq_getElem_cons hlo.1,hlo.2,List.drop_eq_getElem_cons hhi.1,hhi.2,hStop]
      rfl
    · rw [hStop]
      exact len_of_get ha
    · rw [hStop]
      exact releasedIfLast ha (by intro h; cases h)
    · rw [hStop]
      exact ((hCells lane hl slot isRow).step hMax.1 hc (by intro _ _ h; cases h)).step
        hMax.1 ha (by intro _ _ h; cases h)
  let _ : Inhabited TState := ⟨{}⟩
  choose! u hTrace hAt hPast hTail hBound hRelease hArrive hMeta using hLane
  have hOrd := cur.ordinals.advance es (fun lane hl => ⟨_,hTrace lane hl⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨⟨c.shuffles+32,c.votes,c.ends,⟨⟨stop,u,u,hOrd,hTail,fun _ _ => .refl,hAt⟩,
    fun lane hl => (cur.positive lane hl).trans_le (Nat.le_add_right _ _),
    hBound,hRelease,hPast⟩,by rw [c.rank]; omega,
    fun lane hl => ⟨cur.pos lane+1,rfl,hArrive lane hl⟩,hMeta⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
