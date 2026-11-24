-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningValueAcquire
public import Kernels.TmlFa4Fwd.Proof.Progress.FirstCacheReadyPhase
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOpeningValueRelease
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningCacheReady
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.MBarrier Prologue Thread.Output

/-- For each selected request both opening V packets arrive, advancing its ready object. -/
theorem selectedValueReadyPhaseOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {cta batch : Nat} (hCta : cta < l.grid) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1)*p.heads) :
    let log := X.objects (initObject l cta (Loader.readySlot 1))
    ∃ s, stateBefore log log.length = some s ∧ 0 < s.phase := by
  apply cacheReadyPhaseOfDelivered hp hMax.1 hCta 1
  intro g hg hw hOwner lane hl
  have hWarp := warpIndex_lt hp g
  have hLower : tilePrefix p batch*p.heads ≤ g/l.block := hOwner.symm ▸ hLo
  have hUpper : g/l.block < tilePrefix p (batch+1)*p.heads := hOwner.symm ▸ hHi
  by_cases hFirst : warpIndex l g = 14
  · obtain ⟨i,hPub,hDelivered⟩ :=
      (openingValuePacketPublishedByFirstLoaderOfMaximal hp hMax hFrame hg hFirst hb
        hLower hUpper).1 lane hl
    exact ⟨i,hPub.arrive,hDelivered⟩
  · have hSecond : warpIndex l g = 15 := by omega
    obtain ⟨i,hPub,hDelivered⟩ :=
      (openingValuePacketPublishedBySecondLoaderOfMaximal hp hMax hFrame hg hSecond hb
        hLower hUpper).1 lane hl
    exact ⟨i,hPub.arrive,hDelivered⟩

/-- An active CTA's opening V object is ready, or this MMA lane has consumed its
first V packet. A later phase requires an actual release from the same MMA warp. -/
theorem openingValueReadyPhaseOrAcquireOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {g batch : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    (let log := X.objects (Thread.Loader.readyObject l g 1)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 1) ∨
    ∃ j, Thread.Mma.ReadyPoll l X g j 1 0 true .cta ∧
      (Thread.Mma.atPrefix l X g j).kvAcquires 1 = 0 := by
  obtain ⟨s,hs,hPhase⟩ :=
    selectedValueReadyPhaseOfMaximal hp hMax hFrame (NamedBar.cta_lt hg) hb hLo hHi
  by_cases h : s.phase = 1
  · exact .inl ⟨s,hs,h⟩
  have hLate : 1 < s.phase := by omega
  obtain ⟨issue,hPub,hPositive⟩ := positivePublicationOfAdvancedReady hp hMax.1 1 hs hLate
  let n := Protocol.LoaderReady.generation l X issue 1 - 1
  have hGen : Protocol.LoaderReady.generation l X issue 1 = n+1 := by dsimp [n]; omega
  obtain ⟨guard,peer,_,release,_,_⟩ :=
    Protocol.LoaderReady.actualReleaseForNextPublicationExact hp hMax.1 hPub hGen
  have hCta : g/l.block = peer/l.block := by
    rw [Protocol.LoaderReady.publicationCta hp hMax.1 hPub,← guard.issuer,
      release.issuerCta hp hMax.1]
  have hWarp : SameWarp l peer g :=
    ⟨⟨PTX.Proof.event_thread_lt hMax.1 release.issue,hg,hCta.symm⟩,
      (release.issue.issuerWarp hp hMax.1).trans hw.symm⟩
  exact .inr (release.peerFirstValueAcquire hp hMax.1 hWarp)

end PTX.Kernels.TmlFa4Fwd.Progress
