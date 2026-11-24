-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.FirstCacheAcquire
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReadyFaults
import Lemmas.Protocol.GatedFaults

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.AsyncCopy PTX.MBarrier Prologue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem cacheReadyProducer (hp : Pre p l m) {cta : Nat} (hCta : cta < l.grid) (slot : Fin 3)
    (hDelivered : ∀ {g : Nat}, g < l.threads → 14 ≤ warpIndex l g → g / l.block = cta →
      ∀ lane < 32, ∃ i,
        let thread := warpLane l g lane
        X.AsyncArrive (thread,i) (Thread.Loader.readyObject l thread slot) true ∧
          X.async.arrived (thread,i) = true) (lane : Fin 64) :
    ∃ issue, issue.1 = Thread.Loader.producer l cta lane ∧
      X.AsyncArrive issue (initObject l cta (Loader.readySlot slot)) true ∧
      X.async.arrived issue = true := by
  let g := Thread.Loader.producer l cta lane
  have hOffset : 448 + lane.val < 512 := by have := lane.isLt; omega
  have hg : g < l.threads := by
    change cta*l.block+448+lane.val < l.grid*l.block
    rw [hp.block]
    omega
  have hOwner : g / l.block = cta := by
    change (cta*l.block+448+lane.val)/l.block = cta
    rw [hp.block]
    omega
  have hWarp : 14 ≤ warpIndex l g := by
    unfold warpIndex
    change 14 ≤ (cta*l.block+448+lane.val)%l.block/32
    rw [hp.block]
    omega
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g (laneOf l g) = g := by
    unfold warpLane laneOf
    have hle : g%l.block%32 ≤ g := (Nat.mod_le ..).trans (Nat.mod_le ..)
    omega
  obtain ⟨i,hi,hDone⟩ := hDelivered hg hWarp hOwner _ hLane
  rw [hSelf] at hi hDone
  unfold Thread.Loader.readyObject at hi
  rw [hOwner] at hi
  exact ⟨(g,i),rfl,hi,hDone⟩

/-- Sixty-four distinct loader arrivals advance the selected cache-ready object. -/
theorem cacheReadyPhaseOfDelivered (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (hCta : cta < l.grid) (slot : Fin 3)
    (hDelivered : ∀ {g : Nat}, g < l.threads → 14 ≤ warpIndex l g → g / l.block = cta →
      ∀ lane < 32, ∃ i,
        let thread := warpLane l g lane
        X.AsyncArrive (thread,i) (Thread.Loader.readyObject l thread slot) true ∧
          X.async.arrived (thread,i) = true) :
    let log := X.objects (initObject l cta (Loader.readySlot slot))
    ∃ s, stateBefore log log.length = some s ∧ 0 < s.phase := by
  classical
  let loc := initObject l cta (Loader.readySlot slot)
  let log := X.objects loc
  choose issue hLane hArrive hArrived using cacheReadyProducer hp hCta slot hDelivered
  have hRec (lane : Fin 64) :
      ∃ r ∈ log, r.id = .async (issue lane) .arriveOn ∧ r.action = .arrive 1 0 := by
    have ha := objectAction_noinc_arriveOn (hArrive lane) (hArrived lane)
    obtain ⟨r,hr,hId⟩ := (hX.tma.2.2.1 loc).2.2 _ _ ha
    have hAction := ((hX.tma.2.2.1 loc).2.1 r hr).1
    rw [hId,ha] at hAction
    exact ⟨r,hr,hId,(Option.some.inj hAction).symm⟩
  obtain ⟨r0,hr0,-,-⟩ := hRec 0
  have hObj := Loader.actualReadyHistoryObject hp hX slot hr0
  have hLog := X.objects_checked hX loc
  obtain ⟨init,hInit,hAction,hClean,_⟩ := hObj.init r0 hr0
  have hLen : 0 < log.length := (List.getElem?_eq_some_iff.mp hInit).1
  obtain ⟨st,hState,hExpected⟩ := ObjectInit.checked_expected_after_init hLog hObj.noInval
    hInit hAction hClean hLen (Nat.le_refl _)
  have hTx : st.tx = 0 := MbarRing.tx_zero_of hX hObj.noInval
    (fun r hr c tx ha => by
      obtain ⟨k,hk⟩ := List.getElem?_of_mem hr
      exact (hObj.arrive_source hk ha).2.1)
    (fun r hr n ha => by
      cases hObj.source r hr with
      | init h | poll h | arriveOn _ _ _ h => rw [ha] at h; cases h)
    (Nat.le_refl _) hState
  have hPending := stateBefore_pending_pos hLog hState hTx
  have hUnits : 64 ≤ unitsBefore log log.length := by
    let id (lane : Fin 64) := Ref.async (issue lane) .arriveOn
    have hInj : Function.Injective id := by
      intro a b hab
      have h := congrArg (fun r : Ref => r.issuer.1) hab
      change (issue a).1 = (issue b).1 at h
      rw [hLane, hLane] at h
      apply Fin.ext
      unfold Thread.Loader.producer Loader.readyProducer at h
      omega
    have hCard : (Finset.univ.image id).card = 64 := by
      rw [Finset.card_image_of_injective _ hInj,Finset.card_univ,Fintype.card_fin]
    have hSubset : Finset.univ.image id ⊆ ((log.filter countedArrive).map Record.id).toFinset := by
      intro d hd
      obtain ⟨lane,_,rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨r,hr,hId,ha⟩ := hRec lane
      have hBlock : 0 < l.block := by rw [hp.block]; decide
      have hMem : r ∈ X.objects (Thread.Loader.readyObject l (cta*l.block) slot) := by
        unfold Thread.Loader.readyObject
        rw [Nat.mul_div_cancel _ hBlock]
        exact hr
      have hFault := (Protocol.LoaderReady.readyHistoryClean hp hX (cta*l.block) slot hMem).1
      exact List.mem_toFinset.mpr (List.mem_map.mpr
        ⟨r,List.mem_filter.mpr ⟨hr,countedArrive_iff.mpr ⟨hFault,1,0,ha⟩⟩,hId⟩)
    have hCount := (Finset.card_le_card hSubset).trans (List.toFinset_card_le _)
    rw [hCard,List.length_map] at hCount
    unfold unitsBefore
    rw [List.take_length,arrivalUnits_eq_length
      (fun r hr c tx _ ha => by
        obtain ⟨k,hk⟩ := List.getElem?_of_mem hr
        exact (hObj.arrive_source hk ha).1)]
    exact hCount
  have hBalance := ((hLog.accounted hObj.noInval (Nat.le_refl _)).2 st hState).2
  rw [hExpected,hObj.noIncrement] at hBalance
  change unitsBefore log log.length + st.pending = 64 * (st.phase + 1) + 0 at hBalance
  exact ⟨st,hState,by omega⟩

/-- Every selected request's 64 first K arrivals advance the ready object past phase zero. -/
theorem selectedCacheReadyPhaseOfMaximal (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {cta batch : Nat}
    (hCta : cta < l.grid) (hBatch : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads) :
    let log := X.objects (initObject l cta (Loader.readySlot 0))
    ∃ s, stateBefore log log.length = some s ∧ 0 < s.phase := by
  apply cacheReadyPhaseOfDelivered hp hMax.1 hCta 0
  intro g hg hw hOwner lane hl
  obtain ⟨i,hArrive,hArrived,_⟩ := selectedCacheKeyPacketDeliveredOfMaximal hp hMax hFrame
    hg hw hBatch (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi) lane hl
  exact ⟨i,hArrive,hArrived⟩

end PTX.Kernels.TmlFa4Fwd.Progress
