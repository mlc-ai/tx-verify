-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringCacheCohorts
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyBeforeReuse

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.MBarrier
open Prologue (warpIndex)
open Thread.Loader (readyObject)
open Thread.Mma (ReadyPoll atPrefix)

/-- With the producer cohort delivered, either its ready generation is available
or each MMA lane has already recorded that exact acquire. -/
theorem readyPhaseOrAcquiredOfDeliveredCohort {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g gen : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) {slot : Fin 3}
    (hDelivered : DeliveredCohort l X g slot gen) :
    (let log := X.objects (readyObject l g slot)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = gen+1) ∨
    ∃ j, ReadyPoll l X g j slot (gen%2) true .cta ∧
      (atPrefix l X g j).kvAcquires slot = gen := by
  obtain ⟨s,hPhase,hLower⟩ := readyPhaseOfDeliveredCohort hp hX hDelivered
  by_cases hExact : s.phase = gen+1
  · exact .inl ⟨s,hPhase,hExact⟩
  obtain ⟨issue,hPub,hGen⟩ := laterPublicationOfReadyPhase hp hX (gen := gen) slot hPhase (by omega)
  let prior := generation l X issue slot-1
  obtain ⟨guard,peer,_,release,hRank,_⟩ := actualReleaseForNextPublicationExact hp hX hPub
    (show generation l X issue slot = prior+1 by dsimp [prior]; omega)
  have hCta : g/l.block = peer/l.block := by
    rw [publicationCta hp hX hPub,← guard.issuer,release.issuerCta hp hX]
  have hSame : SameWarp l peer g :=
    ⟨⟨PTX.Proof.event_thread_lt hX release.issue,hg,hCta.symm⟩,
      (release.issue.issuerWarp hp hX).trans hw.symm⟩
  exact .inr (release.peerReadyThroughOrdinal hp hX hSame (by dsimp [prior] at hRank; omega))

/-- A lane still waiting to consume the delivered generation can successfully
poll the current phase. A later phase would require that lane's recorded acquire. -/
theorem readyPhaseOfUnconsumedCohort {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g gen : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) {slot : Fin 3}
    (hDelivered : DeliveredCohort l X g slot gen)
    (hCursor : (atPrefix l X g (X.tr g).length).kvAcquires slot = gen) :
    let log := X.objects (readyObject l g slot)
    ∃ s, stateBefore log log.length = some s ∧ s.phase%2 ≠ gen%2 := by
  rcases readyPhaseOrAcquiredOfDeliveredCohort hp hX hg hw hDelivered with
    ⟨s,hState,hPhase⟩ | ⟨j,hAcquired,hPrior⟩
  · exact ⟨s,hState,by omega⟩
  · have hMore := hAcquired.step.1
    obtain ⟨e,he,_⟩ := hAcquired
    have hMono := MbarRing.Poll.okPolls_mono (readyObject l g slot) (X.tr g)
      (show j+1 ≤ (X.tr g).length from PTX.len_of_get he)
    have hCounter := fun n => Thread.Mma.kvAcquireCount l g ((X.tr g).take n) slot
    have hShort := hCounter (j+1)
    have hLong := hCounter (X.tr g).length
    change (atPrefix l X g (j+1)).kvAcquires slot = _ at hShort
    change (atPrefix l X g (X.tr g).length).kvAcquires slot = _ at hLong
    unfold readyObject at hMono
    rw [← hShort, ← hLong] at hMono
    omega

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
