-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderTasks
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerSites
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerCount
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerExit
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked
public import Kernels.Fp16Gemm8192.Proof.Thread.ExitSite

@[expose] public section

/-! # Thread facts at the acknowledgement waits

The facts of `ThreadFacts` about the exit stages (`exit_event_state`), the leader scheduler's
acknowledgement wait (`sched_ack_wait_site`, `sched_ack_claims`) and the loader's counts by site
(`loader_count_ok`). Each is read off the thread's run: the machine fires each event from the
state of its site (`Code.fired_site`), and the run invariants of the roles give the rest. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A scheduler's wait on the acknowledgement barrier is its acknowledgement poll. -/
theorem sched_ack_site_of_wait (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {sd : Scheduler.D} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.sched sd))))
    (hk : e.kind = .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) p ok acq sc) :
    sd.site = .ackWait := by
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  rcases Scheduler.wait_site (g := g) (d := sd) hpre hinv.1 hat hc hfire hk with
    ⟨h, -, -⟩ | ⟨-, hm, -⟩
  · exact h
  · exfalso
    simp only [Scheduler.respBar, Bar.loc, Bar.off] at hm
    have := congrArg Loc.addr hm
    simp only at this
    omega

/-- The scheduler at its acknowledgement wait: each of its earlier successful response polls was
followed by a read of a response that claims a CTA. -/
theorem sched_claims_of (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    (hg : g < L.threads) {sd : Scheduler.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))))
    (hs : sd.site = .ackWait) :
    ∀ j pc p acq sc, j + 1 < (X.tr g).length →
      (X.tr g)[j]? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      ∃ pcr, ∃ src : Acc, ∃ bs rr, (X.tr g)[j + 1]? = some ⟨pcr, .rd src bs⟩ ∧
        src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr := by
  have hσ' : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.sched sd))) := by
    unfold Frame.stateAt at hσ
    rw [List.take_length] at hσ
    exact hσ
  have hinv := Scheduler.run_end hpre hX hg hσ'
  have hlive : Scheduler.D.Live sd := by
    simp [Scheduler.D.Live, hs]
  intro j pc p acq sc hj hw
  obtain ⟨pcr, src, bs, rr, h1, h2, h3, h4, h5⟩ :=
    hinv.stop.2.2 j pc p acq sc hj hw hlive
  exact ⟨pcr, src, bs, rr, h1, ⟨h2, h3⟩, h4, h5⟩

/-- The loader's counts at its trace's end, by its site. -/
theorem loader_count_ok_of (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    (hg : g < L.threads) {l : Loader.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l)))) :
    (∀ b, l.site = .wait b → okPolls (clcResp L g) (X.tr g) = loaderCount L g (X.tr g) / 128) ∧
    (∀ b j, l.site = .load b j →
      okPolls (clcResp L g) (X.tr g) = (loaderCount L g (X.tr g) - 1) / 128) ∧
    (∀ b, l.site = .arrive b →
      okPolls (clcResp L g) (X.tr g) = (loaderCount L g (X.tr g) - 1) / 128) ∧
    (l.site = .clcWait → okPolls (clcResp L g) (X.tr g) + 1 = loaderCount L g (X.tr g) / 128) ∧
    ((l.site = .clcLoad ∨ l.site = .clcStatus ∨ l.site = .clcFirst ∨ l.site = .clcFence ∨
        l.site = .ack) → okPolls (clcResp L g) (X.tr g) = loaderCount L g (X.tr g) / 128) ∧
    (∀ i, l.site = .drain i → okPolls (clcResp L g) (X.tr g) = loaderCount L g (X.tr g) / 128) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hσ' : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take (X.tr g).length) =
      some (some (.inr (.loader l))) := by
    unfold Frame.stateAt at hσ
    exact hσ
  have c := LoaderTasks.run hpre hg htr (X.tr g).length (.inr (.loader l)) hσ'
  rw [List.take_length] at c
  have h := c.resp
  unfold LoaderTasks.CountOK at h
  refine ⟨fun b hb => ?_, fun b j hb => ?_, fun b hb => ?_, fun hb => ?_, fun hb => ?_,
    fun i hi => ?_⟩
  · simp only [hb, loaderCount_eq] at h ⊢
    exact h
  · simp only [hb, loaderCount_eq] at h ⊢
    exact h
  · simp only [hb, loaderCount_eq] at h ⊢
    exact h
  · simp only [hb, loaderCount_eq] at h ⊢
    exact h
  · rcases hb with hb | hb | hb | hb | hb <;> simp only [hb, loaderCount_eq] at h ⊢ <;> exact h
  · simp only [hi, loaderCount_eq] at h ⊢
    exact h

end
end PTX.Kernels.Fp16Gemm8192.Proof
