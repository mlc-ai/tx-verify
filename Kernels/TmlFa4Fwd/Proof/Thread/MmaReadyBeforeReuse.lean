-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseCapacity
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyShuffleAlignment
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof PTX.Flow Prologue
open PTX.Kernels.TmlFa4Fwd.Mma
open Observation (emptyObject readyObject)

/-- The physical empty-slot release certifies the matched or any earlier
ready generation in every participating MMA lane. -/
theorem EmptyReleaseAt.peerReadyThroughOrdinal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner g peer k gen : Nat} {slot : Fin 3}
    (release : EmptyReleaseAt l X (emptyObject l owner slot) g k)
    (hPeer : SameWarp l g peer) (hGen : gen ≤ release.ordinal) :
    ∃ j, ReadyPoll l X peer j slot (gen%2) true .cta ∧
      (atPrefix l X peer j).kvAcquires slot = gen := by
  let gate := releaseIndex release.form
  let site := (electSite (commitElection (releaseCommitSite gate))).pc
  let stop := release.index-1
  obtain ⟨hPositive,inst,leader,hElect⟩ := readyReleaseElection hp hX gate release.issue
  obtain ⟨cut,hPartners⟩ := ElectOrd.partner hX hPeer hElect (fullMember l peer)
  have hPair := hPartners
  obtain ⟨pc,pc',mask,mask',label,lead,lead',ha,hb⟩ := hPartners
  have hFirst : pc = site := congrArg Event.pc (Option.some.inj (ha.symm.trans hElect))
  have hEqual := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ ha hb hPeer).1
  have hSecond : pc' = site := hEqual.symm.trans hFirst
  have hBounds : 2145 ≤ site ∧ site < 2768 := by
    have hAll : ∀ i : Fin 4,
        let s := (electSite (commitElection (releaseCommitSite i))).pc
        2145 ≤ s ∧ s < 2768 := by decide
    exact hAll gate
  have hAvoid (i : Fin 4) : site ≠ (slotWait i).pc+1 := by
    have hAll : ∀ i j : Fin 4,
        (electSite (commitElection (releaseCommitSite i))).pc ≠ (slotWait j).pc+1 := by decide
    exact hAll gate i
  have hCount (i : Fin 4) :
      ((X.tr g).take stop).countP (readyAtSite i) =
        ((X.tr peer).take cut).countP (readyAtSite i) := by
    have hEq := ElectOrd.siteOrdinal_eq hX (· == (slotElect i).pc) hPeer
      (fun _ _ _ _ _ _ he => (Thread.actualFullElectionMask hX he).symm ▸ fullMember l peer)
      (fun _ _ _ _ _ _ he => (Thread.actualFullElectionMask hX he).symm ▸ fullMember l g)
      hPair
    rw [readyBalanceAtEvent hp hX i ha (hFirst.symm ▸ hBounds.1) (hFirst.symm ▸ hBounds.2)
          (hFirst.symm ▸ hAvoid i),
        readyBalanceAtEvent hp hX i hb (hSecond.symm ▸ hBounds.1) (hSecond.symm ▸ hBounds.2)
          (hSecond.symm ▸ hAvoid i)]
    rw [hFirst,hSecond,hEq]
  have hSamePrefix : (((X.tr g).take stop).filterMap readyEvent).length =
      (((X.tr peer).take cut).filterMap readyEvent).length := by
    rw [readyProjectionCount,readyProjectionCount,hCount 0,hCount 1,hCount 2,hCount 3]
  have hw := release.issue.issuerWarp hp hX
  have hwPeer : warpIndex l peer = 12 := hPeer.2.symm.trans hw
  let use := (((X.tr g).take release.matched.wait).filterMap readyEvent).length
  obtain ⟨pcWait,hWait,_⟩ := release.matched.ready.useSite hp hX hw
  have hRank := release.matched.ready.exactOccurrence hp hX hw
  dsimp only at hRank
  rw [← readyUsesAtPrefix hp hX hPeer.1.1 hw release.matched.wait] at hRank
  change release.matched.slot.val = use%3 ∧ release.ordinal = use/3 ∧ _ at hRank
  have hUse : 3*gen+slot.val ≤ use := by
    have hs := release.matchedSlot
    have hv := congrArg Fin.val hs
    omega
  have hMark : readyEvent ⟨pcWait,
      .wait (readyObject l g release.matched.slot) release.matched.parity true true .cta⟩ =
        some (readyObject l g release.matched.slot,release.matched.parity) := by
    have hSite := congrArg Event.pc (Option.some.inj
      (hWait.symm.trans release.matched.readyForm))
    change pcWait = (slotWait gate).pc at hSite
    rw [hSite]
    have hTag : ∀ i : Fin 4,
        (List.finRange 4).any (fun j => readyHead j == (slotWait i).pc) = true := by decide
    simp [readyEvent,hTag]
  have hNext : (((X.tr g).take (release.matched.wait+1)).filterMap readyEvent).length =
      use+1 := by
    rw [List.take_add_one,show (X.tr g)[release.matched.wait]? = some _ from hWait]
    simp [List.filterMap_append,hMark,use]
  have hBefore : release.matched.wait < stop := by
    have h := release.matched.earlier
    have hNe : release.matched.wait ≠ stop := by
      intro hEq
      rw [hEq] at hWait
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj (hWait.symm.trans hElect)))
    dsimp [stop] at hNe ⊢
    omega
  have hMono := ((List.take_sublist_take_left (l := X.tr g)
    (show release.matched.wait+1 ≤ stop by omega)).filterMap readyEvent).length_le
  rw [hNext,hSamePrefix] at hMono
  let sought := 3*gen+slot.val
  obtain ⟨j,_,hFound,hOrdinal⟩ := readyPollAtOrdinalBefore hp hX hPeer.1.2.1 hwPeer
    (use := sought) (stop := cut) (by dsimp [sought]; omega)
  have hSlot : readyStage sought = slot := by
    apply Fin.ext
    change sought%3 = slot.val
    dsimp [sought]
    have hS := slot.isLt
    omega
  have hDivision : sought/3 = gen := by
    dsimp [sought]
    have hS := slot.isLt
    omega
  have hPhase := hFound.exactOccurrence hp hX hwPeer
  dsimp only at hPhase
  rw [← readyUsesAtPrefix hp hX hPeer.1.2.1 hwPeer j,hOrdinal,hDivision] at hPhase
  have hWord : readyWord sought = gen%2 := by
    change sought/3%2 = _
    rw [hDivision]
  rw [hSlot,hWord] at hFound
  exact ⟨j,hFound,hSlot ▸ hPhase.2.1⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
