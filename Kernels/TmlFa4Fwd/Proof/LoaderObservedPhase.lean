-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyArrival
public import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
public import Lemmas.Protocol.CpAsyncPhase
public import Lemmas.MBarrier.MBarrierAddress
public import Lemmas.Execution.ShapeExecution

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.MBarrier PTX.MbarRing PTX.AsyncCopy

noncomputable section
open Classical

/-- The successful observation of a completed ready phase witnesses 64 actual
loader arrivals. Every copy tracked by one of these records is visible to the
CTA acquire. The history index identifies the phase across parity wraparound. -/
theorem readyPhaseObserved {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {cta j phase pc parity : Nat}
    (stage : Fin 3) {wait : EvId} {poll : Record Ref}
    (hOwner : wait.1 / l.block = cta)
    (hWait : X.get wait = some ⟨pc,
      .wait (Prologue.initObject l cta (readySlot stage)) parity true true .cta⟩)
    (hObject : NoIncObject X (Prologue.initObject l cta (readySlot stage)) 64)
    (hRecord : (X.objects (Prologue.initObject l cta (readySlot stage)))[j]? = some poll)
    (hPoll : poll.id = .thread wait) (hSuccess : poll.reply.waited = some true)
    (hObserved : observedAt (X.objects (Prologue.initObject l cta (readySlot stage))) j =
      some phase) :
    let loc := Prologue.initObject l cta (readySlot stage)
    let positions := (Finset.range (X.objects loc).length).filter
      (UnitArrivalIn (X.objects loc) phase)
    positions.card = 64 ∧
    ∀ q ∈ positions,
      q < j ∧ ∃ (issue : EvId) (arrivalPc : Nat),
        X.get issue = some ⟨arrivalPc, .asyncArrive loc true⟩ ∧
        (∃ packet : Fin 6, arrivalPc = copyCommitPc packet + 1) ∧
        ∀ copy, TracksCpAsync X copy issue → AsyncFinished l X copy (.write .copy) wait := by
  dsimp only
  let loc := Prologue.initObject l cta (readySlot stage)
  have hChecked := X.objects_checked hX loc
  obtain ⟨state, hState, hPhase⟩ := hChecked.observed_phase hRecord hSuccess hObserved
  have hJ : j ≤ (X.objects loc).length := ((List.getElem?_eq_some_iff.mp hRecord).1).le
  refine ⟨hObject.completed_count hX hJ hState (by omega), ?_⟩
  intro q hQ
  obtain ⟨hIn, hArrival⟩ := Finset.mem_filter.mp hQ
  obtain ⟨r, tx, hR, hAction, hClean, hAt⟩ := hArrival
  have hQJ := hChecked.phase_before_observation hObject.noInval
    (Finset.mem_range.mp hIn).le hAt hRecord hSuccess hObserved
  obtain ⟨_, rfl, issue, hId, ⟨arrivalPc, hIssue⟩, _⟩ := hObject.arrive_source hR hAction
  obtain ⟨hSites, _, _, hCTA⟩ := actualAsyncArrival hX hIssue
  have hCta : issue.1 / l.block = wait.1 / l.block := by
    rw [hOwner, ← hCTA]
    rfl
  refine ⟨hQJ, issue, arrivalPc, hIssue, hSites, ?_⟩
  intro copy hTracks
  have hCopied : copy.1 = issue.1 := hTracks.1
  have hScope : ScopesMeet l .cluster copy.1 .cta wait.1 := by
    rw [hCopied]
    have hi := event_thread_lt hX hIssue
    have hw := event_thread_lt hX hWait
    exact ⟨⟨hi, hw, congrArg l.clusterOfCta hCta⟩, ⟨hw, hi, hCta.symm⟩⟩
  exact hObject.observes_copy hX hR hClean hAction hId hRecord hPoll hSuccess
    hAt hObserved hWait hTracks hScope

end
end PTX.Kernels.TmlFa4Fwd.Loader
