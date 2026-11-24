-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.Async
public import Lemmas.Step.BulkWait
public import Lemmas.Step.BulkWaitReady

@[expose] public section

/-! # Progress at a bulk-group wait

A consumer waits, after each slice of its epilogue and once more before it leaves, for its TMA
stores to complete (`cp.async.bulk.wait_group`). A pending consumer at such a site, whose last event
is released, performs the wait (a counted extension, `Step.BulkWait.bulk_wait_counted_extension`,
`bulk_next_steps`). The wait blocks until the stores it covers are complete: that is the readiness
of the wait as the thread's last event, which the release of its next event demands. A wait that is
not ready has a store it covers open (`Step.BulkWait.ready_of_drained`; the kernel issues no linear
copy): an obligation of rank 1, below every thread that has made an event (`bulk_unready_steps`,
`threadTime_pos`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread that has made an event has a positive time: only the prologue's first site, before
any event, has time 0, and every exit-stage time is above `exitBase`, which is positive. -/
theorem threadTime_pos (ht : ThreadFacts L X) (hub : ¬ HasUb X) {g : Nat} (hg : g < L.threads)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hne : X.tr g ≠ []) : 1 ≤ threadTime L X g := by
  unfold threadTime
  rw [hσ]
  cases ho : d.exitOff with
  | some o => simp only [ho]; unfold exitBase; omega
  | none =>
    simp only [ho]
    rcases d with ⟨site, w⟩ | (l | m | sc | c)
    · cases site
      case shfl =>
        exact absurd (ht.coll_before hg (fun k pc f h => hub ⟨(g, k), pc, f, h⟩) hσ rfl) hne
      all_goals simp only [ThreadD.vtime, Prologue.Site.vtime]; omega
    · obtain ⟨site, _, _, _, _, _⟩ := l
      cases site <;> simp only [ThreadD.exitOff, Loader.exitOff, reduceCtorEq] at ho <;>
        simp only [ThreadD.vtime, Loader.vtime, ringAt, blockAt] <;> omega
    · obtain ⟨site, _, _, _, _, _, _, _⟩ := m
      cases site <;> simp only [ThreadD.exitOff, Mma.exitOff, reduceCtorEq] at ho <;>
        simp only [ThreadD.vtime, Mma.vtime, ringAt, blockAt] <;> omega
    · obtain ⟨site, _, _, _, _⟩ := sc
      cases site <;> simp only [ThreadD.exitOff, Scheduler.exitOff, reduceCtorEq] at ho <;>
        simp only [ThreadD.vtime, Scheduler.vtime, blockAt] <;> omega
    · rcases c with ⟨site⟩
      cases site <;> simp only [ThreadD.exitOff, Consumer.exitOff, reduceCtorEq] at ho <;>
        simp only [ThreadD.vtime, Consumer.vtime, blockAt] <;> omega

/-- **Progress at a bulk-group wait that is not ready.** A thread whose last event is a bulk-group
wait that is not ready, and whose machine goes on after it (`hlive`), has an open store obligation,
of rank 1, below its own. -/
theorem bulk_unready_steps (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {pc : Nat}
    {mode : BulkGroup.WaitMode} {n : Nat}
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bulkWait mode n⟩)
    (hnr : ¬ Ready L X (g, (X.tr g).length - 1))
    (hlive : Frame.stateAt (code L) X g (X.tr g).length ≠ none) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X (.thread g) := by
  have hX := hmax.1
  have hrel : ¬ Step.Released L X g := fun hr => hnr (hr.ready pc _ hlast rfl)
  refine .inr ⟨X, .store, hmax, fun hall => hnr (Step.BulkWait.ready_of_drained hX hlast hall
    fun i s hc _ => ?_), ?_⟩
  · obtain ⟨pci, he⟩ := hc
    have hgi : i.1 < L.threads := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.state_of_noUb ht.sound hX ht.tracked hub he
    exact ((ht.ring_event hgi he hσ).copy s rfl).elim
  · have hne : X.tr g ≠ [] := by
      intro h0
      have := len_of_get hlast
      simp [h0] at this
    obtain ⟨d, hσ⟩ : ∃ d, Frame.stateAt (code L) X g (X.tr g).length = some (some d) := by
      cases hσ : Frame.stateAt (code L) X g (X.tr g).length with
      | none => exact absurd hσ hlive
      | some σ =>
        cases σ with
        | none => exact absurd hσ (ht.tracked g _ hp.1)
        | some d => exact ⟨d, rfl⟩
    have := threadTime_pos ht hub hp.1 hσ hne
    simp only [rank, hrel, ite_false]
    omega

/-- **Progress at a bulk-group wait.** A pending consumer at a slice's drain or at its final drain,
whose last event is released, performs the wait. -/
theorem bulk_next_steps (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))))
    (hs : (∃ k, c.site = .drain k) ∨ c.site = .finalDrain) (hrel : Step.Released L X g) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X (.thread g) := by
  obtain ⟨t, hrun⟩ := Frame.run_some hmax.1 hub hp
  obtain ⟨t1, u, mode, n, hl, he⟩ := ht.bulk_fire hp.1 hσ hs hrun
  have hne : X.tr g ≠ [] := by
    intro h0
    simp only [Frame.stateAt, h0, List.take_nil] at hσ
    cases hσ
  exact .inl (Step.BulkWait.bulk_wait_counted_extension hmax.1 hp.1 hne hrel
    (fun a ha => prod_wfFree a ha _) hrun hl he)

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
