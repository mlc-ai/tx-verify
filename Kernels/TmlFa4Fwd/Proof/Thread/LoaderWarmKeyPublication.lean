-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyUpperProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderKeyPublicationProgress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

private theorem warmKeyHalfOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch ordinal votes first : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (slot : Fin 2) (hFirst : 2 ≤ first ∧ 8*slot.val < first)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmKeyNextGroupPc first)
      (fun lane => warmKeyGroupFrame p l g batch lane slot) ordinal votes ends)
    (count : Nat) (hLast : first+count ≤ 8*(slot.val+1)) :
    ∃ done : SchedulerWarpReached l X g (warmKeyNextGroupPc (first+count))
        (fun lane => warmKeyGroupFrame p l g batch lane slot) (ordinal+2*count) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  induction count with
  | zero => exact ⟨cur,fun _ _ _ _ _ h => h⟩
  | succ k ih =>
    obtain ⟨mid,hMid⟩ := ih (by omega)
    have hSlot := slot.isLt
    let group : Fin 16 := ⟨first+k,by omega⟩
    have hNo : group.val ≠ 8 := by
      fin_cases slot
      · change first+k+1 ≤ 8 at hLast
        change first+k ≠ 8
        omega
      · have h := hFirst.2
        change 8 < first at h
        change first+k ≠ 8
        omega
    obtain ⟨done,hDone⟩ := warmKeyNextGroupOfMaximal hp hMax hg hb hLo hHi hTrips slot group
      (by dsimp [group]; omega) ⟨by dsimp [group]; omega,by dsimp [group]; omega⟩ hNo mid
    have hN : ordinal+2*k+2 = ordinal+2*(k+1) := by omega
    rw [← hN]
    exact ⟨done,fun lane hl _ _ _ h => hDone lane hl (hMid lane hl h)⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
include hp hMax hg hw hb hLo hHi hTrips

private theorem warmFirstKeyPacketsOfMaximal (c : WarmFirstPages p l X g batch) :
    Nonempty (SchedulerWarpReached l X g 1136
      (fun lane => warmKeyGroupFrame p l g batch lane 1) (c.shuffles+32) c.votes c.ends) := by
  obtain ⟨first,hFirst⟩ := c.firstTwoKeyPairsOfMaximal hp hMax hg hw hb hLo hHi hTrips
  obtain ⟨mid,hMid⟩ := warmKeyHalfOfMaximal hp hMax hg hb hLo hHi hTrips
    (first := 2) 0 (by decide) first 6 (by decide)
  obtain ⟨upper⟩ := warmKeyUpperFirstOfMaximal hp hMax hg hb hLo hHi hTrips mid
    (fun lane hl => hMid lane hl (hFirst lane hl))
  obtain ⟨done,_⟩ := warmKeyHalfOfMaximal hp hMax hg hb hLo hHi hTrips
    (first := 9) 1 (by decide) upper 7 (by decide)
  exact ⟨done⟩

/-- A warm K publication returns the full original register carry at the entrance to V. -/
theorem WarmFirstPages.publishKeyOfMaximal (c : WarmFirstPages p l X g batch) :
    ∃ done : SchedulerWarpReached l X g 1138 (warmFirstKeyCarry p l g batch)
        (c.shuffles+32) c.votes c.ends,
      ∀ lane < 32, ∃ i,
        i+1 = done.pos lane ∧ X.AsyncArrive (warpLane l g lane,i)
          (readyObject l (warpLane l g lane) 2) true := by
  classical
  obtain ⟨cur⟩ := warmFirstKeyPacketsOfMaximal hp hMax hg hw hb hLo hHi hTrips c
  let threads := warpLane l g
  let addr := l.sharedBase+16
  let stop := fun lane => cur.pos lane+2
  let ev : Nat → Event := fun lane => ⟨1137,.asyncArrive (readyObject l (threads lane) 2) true⟩
  let es : Nat → List Event := fun lane => [⟨1136,.asyncCommit⟩,ev lane]
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hWidth : addr+(copyArrivalAddress (recurringPacketSite 0)).2 < 2^32 := by
    have h := hp.shared.2.1
    change l.sharedBase+16+32 < 2^32
    omega
  have hAlign : addr%8 = 0 := by
    have h := hp.shared.1
    dsimp [addr]
    omega
  have hLane (lane : Nat) (hl : lane < 32) : ∃ u,
      (X.tr (threads lane)).drop (cur.pos lane) =
        es lane ++ (X.tr (threads lane)).drop (stop lane) ∧
      At u 1138 (warmFirstKeyCarry p l g batch lane) ∧
      Run kernel Assumptions.all l (threads lane) {} ((X.tr (threads lane)).take (stop lane))
        (some u) ∧
      Run kernel Assumptions.all l (threads lane) u ((X.tr (threads lane)).drop (stop lane))
        (c.ends lane) ∧
      stop lane ≤ (X.tr (threads lane)).length ∧
      (stop lane = (X.tr (threads lane)).length → Step.Released l X (threads lane)) ∧
      X.get (threads lane,cur.pos lane+1) = some (ev lane) := by
    have hActor := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
    have hs := cur.checkpoint lane hl
    have hAt : At (cur.state lane) (copyCommitPc (recurringPacketSite 0))
        [((copyArrivalAddress (recurringPacketSite 0)).1,b32 addr)] :=
      hs.mono ⟨holds_lookup hs.2.2.2.2 rfl,trivial⟩
    obtain ⟨hc,ha,hPast,hTail⟩ := copyCommitAndArriveOfMaximal hMax
      (g := threads lane) hActor (recurringPacketSite 0) hAt hWidth hAlign
      (cur.localSteps lane hl) (cur.recorded lane hl) (cur.continuation lane hl)
      (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl)
    have hLoc : (⟨.shared,threads lane/l.block,addr+32⟩ : Loc) =
        readyObject l (threads lane) 2 := by
      change _ = initObject l (threads lane/l.block) (readySlot 2)
      rw [readySlot_address]
      congr 1
    change X.get (threads lane,cur.pos lane+1) =
      some ⟨1137,.asyncArrive ⟨.shared,threads lane/l.block,addr+32⟩ true⟩ at ha
    rw [hLoc] at ha
    have hStop : stop lane = cur.pos lane+1+1 := rfl
    have hFrame : At (next (next (cur.state lane))) 1138 (warmFirstKeyCarry p l g batch lane) := by
      exact hs.next.next.mono hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    refine ⟨_,?_,hFrame,hPast,hTail,?_,?_,ha⟩
    · change (X.tr (threads lane))[cur.pos lane]? = some ⟨1136,.asyncCommit⟩ at hc
      change (X.tr (threads lane))[cur.pos lane+1]? = some (ev lane) at ha
      have hlo := List.getElem?_eq_some_iff.mp hc
      have hhi := List.getElem?_eq_some_iff.mp ha
      rw [List.drop_eq_getElem_cons hlo.1,hlo.2,List.drop_eq_getElem_cons hhi.1,hhi.2,hStop]
      rfl
    · rw [hStop]
      exact len_of_get ha
    · rw [hStop]
      exact releasedIfLast ha (by intro h; cases h)
  let _ : Inhabited TState := ⟨{}⟩
  choose! u hTrace hAt hPast hTail hBound hRelease hArrive using hLane
  have hOrd := cur.ordinals.advance es (fun lane hl => ⟨_,hTrace lane hl⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨⟨⟨stop,u,u,hOrd,hTail,fun _ _ => .refl,hAt⟩,
    fun lane hl => (cur.positive lane hl).trans_le (Nat.le_add_right _ _),
    hBound,hRelease,hPast⟩,fun lane hl => ⟨cur.pos lane+1,rfl,1137,hArrive lane hl⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
