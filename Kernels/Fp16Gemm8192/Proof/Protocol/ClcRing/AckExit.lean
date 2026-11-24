-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # A no-claim query is a successful poll followed by a read of a response that claims nothing

The query of a response reports the response its thread read right after its latest successful
poll of its CTA's response barrier (`ThreadFacts.clc_query`). So a trace with a query that names
no first CTA has a successful poll whose read decodes to a response that claims no CTA.

The exit lemma (`noclaim_lt`): a thread that has read such a response polled its response barrier
for the last time at a count `c0` that exceeds every count of the leader scheduler's response polls
whose read claims a CTA (`ThreadFacts.sched_ack_claims`), since the readers read the same response
at the same count (`AllResponsesAgree`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A no-claim query is preceded, by two events, by a successful response poll and a read of the
response it reports. -/
theorem noClaim_before (ht : ThreadFacts L X) {g i pc : Nat} {q : ClcQuery} {r : ClcResponse}
    (hg : g < L.threads) (hi : X.get (g, i) = some ⟨pc, .clcQuery q r⟩) :
    ∃ (j : Nat) (pc' p : Nat) (acq : Bool) (sc : MbarScope) (pcr : Nat) (src : Acc)
      (bs : List (Option Byte)), j + 2 ≤ i ∧
      X.get (g, j) = some ⟨pc', .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some r := by
  obtain ⟨st, hst⟩ := ht.query_role hg hi
  obtain ⟨j, pc', p, acq, sc, pcr, src, bs, -, hjk, hw, hr, hsf, hres⟩ :=
    ht.clc_query hg hi hst rfl
  exact ⟨j, pc', p, acq, sc, pcr, src, bs, hjk, hw, hr, hsf, hres⟩

/-- A successful poll on `m` is a wait on `m` that succeeds. -/
theorem okPoll_exists {m : Loc} {e : Event} (h : okPoll m e = true) :
    ∃ pc p acq sc, e = ⟨pc, .wait m p true acq sc⟩ := by
  obtain ⟨pc, kind⟩ := e
  cases kind
  case wait target p ok acq sc =>
    cases ok
    · simp [okPoll, sourceWaitSuccess] at h
    · simp only [okPoll, sourceWaitSuccess, decide_eq_true_eq] at h
      subst h
      exact ⟨pc, p, acq, sc, rfl⟩
  all_goals simp [okPoll, sourceWaitSuccess] at h

/-- A successful poll count is reached at a successful poll of the trace: the `n`-th successful poll
of `m` is an event of the trace, after `n - 1` earlier successful polls. -/
theorem exists_count_poll (m : Loc) (es : List Event) (n : Nat) (hn : 0 < n)
    (hle : n ≤ okPolls m es) :
    ∃ j e, es[j]? = some e ∧ okPolls m (es.take j) + 1 = n ∧ okPoll m e = true := by
  induction es generalizing n with
  | nil =>
    exfalso
    simp [okPolls] at hle
    omega
  | cons e es ih =>
    by_cases he : okPoll m e = true
    · by_cases h1 : n = 1
      · subst h1
        exact ⟨0, e, by simp, by simp [okPolls], he⟩
      · obtain ⟨j, e', hj, hc, hok⟩ := ih (n - 1) (by omega)
          (by simp only [okPolls, List.countP_cons, he, ite_true] at hle ⊢; omega)
        refine ⟨j + 1, e', by simpa using hj, ?_, hok⟩
        simp only [okPolls, List.take_succ_cons, List.countP_cons, he, ite_true] at hc ⊢
        omega
    · have he' : okPoll m e = false := by simpa using he
      obtain ⟨j, e', hj, hc, hok⟩ := ih n hn
        (by simp only [okPolls, List.countP_cons, he', Bool.false_eq_true, ite_false] at hle ⊢
            omega)
      refine ⟨j + 1, e', by simpa using hj, ?_, hok⟩
      simp only [okPolls, List.take_succ_cons, List.countP_cons, he', Bool.false_eq_true,
        ite_false] at hc ⊢
      omega

/-- **The exit lemma.** Let `b` read, after its successful response poll `j`, a response that claims
no CTA, and let `g` be a leader scheduler at its acknowledgement wait. Then the poll count of `b`
at `j` (with the poll itself) exceeds the successful response polls of `g`: the response at that
count would be a claiming read of `g` (its own response polls are followed by claiming reads,
`sched_ack_claims`) if `g` had polled that many times, and the readers of one cluster read the
same response at the same count (`AllResponsesAgree`). -/
theorem noclaim_lt (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) {g b : Nat}
    {sd : Scheduler.D} (hg : g < L.threads)
    (hcl : g / L.block / 2 = b / L.block / 2)
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))))
    (hsd : sd.site = .ackWait)
    (hgpoll : ∀ j pc p acq sc,
      (X.tr g)[j]? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      j + 1 < (X.tr g).length)
    {j pcb p pcr : Nat} {acq : Bool} {sc : MbarScope} {src : Acc} {bs : List (Option Byte)}
    {rr : ClcResponse}
    (hbw : (X.tr b)[j]? = some ⟨pcb, .wait (Bar.loc L (b / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    (hbr : (X.tr b)[j + 1]? = some ⟨pcr, .rd src bs⟩)
    (hbsrc : src.SameFootprint ⟨⟨.shared, b / L.block, L.sharedBase + 144⟩, 16, false, false, .cta,
      0, false⟩)
    (hrr : Flow.responseOf bs = some rr) (hnc : ¬ Loader.claims rr) :
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) <
      okPolls (Bar.loc L (b / L.block) ⟨.clc, 0, true⟩) ((X.tr b).take j) + 1 := by
  by_contra hle
  have hle' : okPolls (Bar.loc L (b / L.block) ⟨.clc, 0, true⟩) ((X.tr b).take j) + 1 ≤
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by omega
  obtain ⟨jg, eg, hjg, hcg, hokg⟩ := exists_count_poll (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
    (X.tr g) (okPolls (Bar.loc L (b / L.block) ⟨.clc, 0, true⟩) ((X.tr b).take j) + 1)
    (by omega) hle'
  obtain ⟨pcg, pg, acqg, scg, rfl⟩ := okPoll_exists hokg
  have hjlt := hgpoll jg pcg pg acqg scg hjg
  obtain ⟨pcr', src', bs', rr', h1, h2, h3, h4⟩ :=
    ht.sched_ack_claims hg hσg hsd jg pcg pg acqg scg hjlt hjg
  have hagree := hag (g / L.block / 2) g b jg j pcg pcb pg p pcr' pcr acqg acq scg sc src' src bs'
    bs rfl hcl.symm hjg hbw (by omega) h1 h2 hbr hbsrc
  rw [hagree, hrr] at h3
  have hrr_eq : rr = rr' := Option.some.inj h3
  exact hnc (by rw [hrr_eq]; exact h4)

end
end PTX.Kernels.Fp16Gemm8192.Proof
