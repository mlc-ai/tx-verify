-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstKeyReleaseProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseCapacity
import Kernels.TmlFa4Fwd.Proof.MmaInitialReadyRelease

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof Prologue
open PTX.Kernels.TmlFa4Fwd.Mma
open Observation (readyObject emptyObject)

private theorem releaseSiteNotFirst {form : ReleaseForm} (h : form ≠ .firstKey) :
    (slotWait (releaseIndex form)).pc ≠ readyHead 0 := by
  cases form <;> first | exact (h rfl).elim | decide

private theorem usePositiveOfLaterReadySite {use site : Nat}
    (hSite : ReadyUseSite use site) (hne : site ≠ readyHead 0) : 0 < use := by
  rcases hSite with ⟨h,_⟩ | ⟨_,h,_⟩ | ⟨_,h⟩
  · exact (hne h).elim
  · exact h
  · omega

/-- A delivered reuse release for slot one implies the first V acquire in each MMA lane. -/
theorem EmptyReleaseAt.peerFirstValueAcquire {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner g peer k : Nat} (release : EmptyReleaseAt l X (emptyObject l owner 1) g k)
    (hPeer : SameWarp l g peer) :
    ∃ j, ReadyPoll l X peer j 1 0 true .cta ∧ (atPrefix l X peer j).kvAcquires 1 = 0 := by
  have hForm : release.form ≠ .firstKey := by
    intro h
    have he := release.issue
    rw [h] at he
    have hEq := initialEmptyReleaseAddress hp hX he release.target
    have hAbs := congrArg Loc.addr hEq
    change l.sharedBase+64 = l.sharedBase+56 at hAbs
    omega
  have hw : warpIndex l peer = 12 := hPeer.2.symm.trans (release.issue.issuerWarp hp hX)
  obtain ⟨index,loc,parity,hGet,_,_⟩ := release.issue.readyOccurrence hp hX hPeer
  let site := (slotWait (releaseIndex release.form)).pc
  let ev : Event := ⟨site,.wait loc parity true true .cta⟩
  have hMark : readyEvent ev = some (loc,parity) := by
    have hTag : (List.finRange 4).any (fun i => readyHead i == site) = true := by
      have hAll : ∀ f : Fin 4,
          (List.finRange 4).any (fun i => readyHead i == (slotWait f).pc) = true := by decide
      exact hAll _
    simp [ev,readyEvent,hTag]
  obtain ⟨slot,hLoc⟩ := readySlotOfProjection hp hX hw hGet hMark
  have hPoll : ReadyPoll l X peer index slot parity true .cta := by
    refine ⟨ev,hGet,?_⟩
    simp [ev,hLoc]
  obtain ⟨tag,hRead,hSite⟩ := hPoll.useSite hp hX hw
  have hTag : site = tag := congrArg Event.pc (Option.some.inj (hGet.symm.trans (hLoc ▸ hRead)))
  have hBefore : 0 < (((X.tr peer).take index).filterMap readyEvent).length :=
    usePositiveOfLaterReadySite hSite (hTag ▸ releaseSiteNotFirst hForm)
  have hCount : (((X.tr peer).take (index+1)).filterMap readyEvent).length =
      (((X.tr peer).take index).filterMap readyEvent).length+1 := by
    rw [List.take_add_one,show (X.tr peer)[index]? = some ev from hGet]
    simp [hMark]
  obtain ⟨j,_,hj,hOrdinal⟩ :=
    readyPollAtOrdinalBefore hp hX hPeer.1.2.1 hw (use := 1) (stop := index+1) (by omega)
  exact ⟨j,hj,initialValueReadyPhaseZero hp hX hPeer.1.2.1 hw hOrdinal⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
