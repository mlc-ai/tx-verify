-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RecurringCacheAcquire
public import Kernels.TmlFa4Fwd.Proof.MmaReadySegments
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketPlane
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyBacking
import Kernels.TmlFa4Fwd.Proof.LoaderProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.MBarrier
open Prologue (warpIndex)
open Thread.Loader (producer readyObject recurringPublicationMark recurringUseBefore)
open Thread.Mma (atPrefix)

/-- The concrete arrived-on operations issued by one cache packet, at their
logical producer generation. -/
def IssuedCohort (l : Launch) (X : Execution) (owner : Nat) (slot : Fin 3)
    (gen : Nat) : Prop :=
  ∀ lane : Fin 64, ∃ issue, issue.1 = producer l (owner/l.block) lane ∧
    X.AsyncArrive issue (readyObject l owner slot) true ∧ generation l X issue slot = gen

/-- Under the existing output-frame condition, maximality finishes the actual
ordinary copies tracked by the given arrive-on, then delivers the arrival. -/
theorem drainedCachePublication {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {owner : Nat} {slot : Fin 3} {issue : EvId}
    (hArrive : X.AsyncArrive issue (readyObject l owner slot) true) :
    X.async.arrived issue = true := by
  cases hPending : X.async.arrived issue
  · apply (hMax.not_grows (pending_cpAsyncArrive_extendsInOrder Assumptions.wfStep
      hMax.1 hArrive hPending ?_)).elim
    intro copy hTrack
    obtain ⟨spec,hCopy,_⟩ := hTrack.2.2.1
    cases hWritten : (X.async.copies copy).writeBytes with
    | some => rfl
    | none =>
      have hShape := actualCopyShape hMax.1 hCopy
      have hSafe := Thread.Loader.ordinaryCopyBacked hp hMax.1 hFrame hCopy
      apply (hMax.not_grows (pending_cpAsync_extendsInOrder Assumptions.wfStep
        hMax.1 hCopy hShape.completion hShape.whole hShape.noData hWritten
        (Loader.noCopyGroupWait hMax.1 hCopy) hShape.srcSize ?_ ?_)).elim
      · intro k hk
        obtain ⟨b,hb⟩ := (hSafe k hk).2.1
        simp [hb]
      · exact fun k hk => (hSafe k hk).2.2
  · rfl

theorem IssuedCohort.deliveredOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {owner gen : Nat} {slot : Fin 3}
    (hIssued : IssuedCohort l X owner slot gen) : DeliveredCohort l X owner slot gen := by
  intro lane
  obtain ⟨issue,hProducer,hArrive,hRank⟩ := hIssued lane
  exact ⟨issue,hProducer,hArrive,drainedCachePublication hp hMax hFrame hArrive,hRank⟩

/-- The actual producer trace counts suffice to recover the complete issued
cohort. The nth recurring arrival has the exact slot and generation of its
logical use, after the two priming packets. -/
theorem issuedCohortOfRecurringCounts {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g use : Nat}
    (hUse : 2 ≤ use)
    (hProducer : ∀ lane : Fin 64, use-1 ≤
      (X.tr (producer l (g/l.block) lane)).countP recurringPublicationMark) :
    IssuedCohort l X g (Mma.readyStage use) (use/3) := by
  intro lane
  let loader := producer l (g/l.block) lane
  obtain ⟨j,e,hGet,hMark,hPrior⟩ := MbarRing.Slot.exists_nth_countP recurringPublicationMark
    (xs := X.tr loader) (c := use-2) (by have := hProducer lane; dsimp [loader]; omega)
  have hOrdinal : recurringUseBefore X (loader,j) = use := by
    change 2 + ((X.tr loader).take j).countP recurringPublicationMark = use
    omega
  have hEvent : X.get (loader,j) = some e := hGet
  obtain ⟨hArrive,hRank⟩ := Thread.Loader.recurringPublicationAtUse hp hX hEvent hMark
  rw [hOrdinal] at hArrive hRank
  have hSlot : Loader.kvUseStage use = Mma.readyStage use := rfl
  rw [hSlot] at hArrive hRank
  have hProducerCta : loader/l.block = g/l.block := by
    have hLane := lane.isLt
    dsimp only [loader, producer, Loader.readyProducer]
    rw [hp.block]
    omega
  refine ⟨(loader,j),rfl,?_,hRank⟩
  unfold readyObject at hArrive ⊢
  rwa [hProducerCta] at hArrive

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
