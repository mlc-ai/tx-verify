-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.BarTime
public import Kernels.Fp16Gemm8192.Proof.Progress.ClusterStage
public import Lemmas.Step.CtaBarNamed

@[expose] public section

/-! # The blocker of a named barrier wait: a participant that has not arrived

A consumer `g` whose last event is its `N`-th arrival on its group's barrier (the CLC barrier or the
output barrier), not released, and a thread `h` of the same warp group of the same CTA with fewer
arrivals on it (`bar_lag_blocker`). The thread `h` is a thread of `g`'s cluster, which has not
exited (the cluster's exit would have made `g`'s two cluster arrivals), so it is not canceled and
pending. Its next event is earlier in the rank table:

* outside its exit stage, it has made at most `N - 1` arrivals, so its time is at most that of the
  barrier's `N`-th arrival, below `g`'s (`bar_vtime_le`, `bar_vtime_lt`);
* in its exit stage it has read, as its last response, a response claiming no CTA, after a
  successful poll that `g`, which has polled at least `N` times and read the same response
  (`AllResponsesAgree`), also made and then read as claiming (`ThreadFacts.cons_claims`): a
  contradiction. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The id of a group's CLC barrier (`clc`) or output barrier. -/
def barId (clc : Bool) (q : Nat) : Nat := if clc then q + 1 else q + 10

/-- A trace's arrivals on its group's barrier. -/
def barCount (clc : Bool) (q : Nat) (es : List Event) : Nat :=
  es.countP (Execution.isBarId (barId clc q))

theorem holds_le_tileOpen (c : Consumer.D) : Consumer.holds c ≤ Consumer.tileOpen c := by
  unfold Consumer.holds Consumer.tileOpen
  cases c.site <;> simp

/-- **A consumer's barrier arrivals** at its trace's end, for the group's barrier of the kind. -/
theorem barFact_of (ht : ThreadFacts L X) {h q : Nat} {c : Consumer.D} (clc : Bool)
    (hh : h < L.threads) (hσ : Frame.stateAt (code L) X h (X.tr h).length =
      some (some (.inr (.cons c))))
    (hq : Consumer.tidOf L h / 32 / 4 = q) :
    BarFact clc c (consCount L h (X.tr h)) (barCount clc q (X.tr h)) ∧
      c.started + Consumer.holds c ≤ consCount L h (X.tr h) := by
  obtain ⟨h1, h2, h3⟩ := ht.cons_bars hh hσ
  refine ⟨?_, h3⟩
  cases clc
  · simp only [BarFact, barCount, barId, Bool.false_eq_true, ↓reduceIte]
    rw [← hq]
    rw [Consumer.outBars_eq] at h2
    exact h2
  · simp only [BarFact, barCount, barId, ↓reduceIte]
    rw [← hq]
    exact h1

/-- A trace's successful polls of a barrier before a position are at most those of the trace. -/
theorem okPolls_take_le' (m : Loc) (es : List Event) (k : Nat) :
    okPolls m (es.take k) ≤ okPolls m es :=
  (List.take_sublist k es).countP_le

/-- The successful polls up to just after a poll are one more than those before it. -/
theorem okPolls_take_succ' (m : Loc) (es : List Event) {j : Nat} {e : Event}
    (hj : es[j]? = some e) :
    okPolls m (es.take (j + 1)) = okPolls m (es.take j) + (if okPoll m e then 1 else 0) := by
  rw [List.take_add_one, hj]
  exact okPolls_snoc m _ e

/-- A consumer in an exit-stage site has no tile open, and holds no accumulator and no response. -/
theorem exit_counts (c : Consumer.D) (hx : Consumer.exitOff c ≠ none) :
    Consumer.tileOpen c = 0 ∧ Consumer.holds c = 0 ∧ c.clcHold = 0 ∧ c.inEpi = 0 ∧
      c.outPhase = 0 := by
  unfold Consumer.exitOff at hx
  unfold Consumer.tileOpen Consumer.holds Consumer.D.clcHold Consumer.D.inEpi Consumer.D.outPhase
  cases hs : c.site <;> simp_all

/-- **A consumer in its exit stage cannot be behind a consumer that has polled further.** Its
response polls are `T`; a consumer `g` of its cluster with more than `T` successful response polls
has read a claiming response at the poll the exit stage's consumer read as claiming no CTA. -/
theorem exit_excluded (ht : ThreadFacts L X) (hagree : AllResponsesAgree L X) {g h : Nat}
    {cg ch : Consumer.D} (hg : g < L.threads) (hh : h < L.threads)
    (hsame : h / L.block / 2 = g / L.block / 2)
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons cg))))
    (hσh : Frame.stateAt (code L) X h (X.tr h).length = some (some (.inr (.cons ch))))
    (hx : Consumer.exitOff ch ≠ none)
    (hlt : consCount L h (X.tr h) <
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g))
    (hub : ¬ HasUb X) : False := by
  have hub' : ∀ k pc f, X.get (h, k) ≠ some ⟨pc, .ub f⟩ :=
    fun k pc f hk => hub ⟨(h, k), pc, f, hk⟩
  obtain ⟨hx1, hx2, -⟩ := exit_counts ch hx
  have hcons := ht.cons_tiles hh hub' hσh
  rw [hx1, hx2] at hcons
  obtain ⟨j, pc, p, acq, sc, pcr, src, bs, rr, hwj, hrj, hsf, hresp, hcl2⟩ :=
    ht.cons_exit_read hh hσh hx
  have hpoll_j : okPoll (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩)
      ⟨pc, .wait (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ = true := by
    simp [okPoll, sourceWaitSuccess]
  have hjk := okPolls_take_succ' (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) hwj
  rw [hpoll_j] at hjk
  simp only [ite_true] at hjk
  have hle := okPolls_take_le' (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) (j + 1)
  -- the poll of `g` with the same ordinal, which is not `g`'s latest
  have hr_lt : okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) ((X.tr h).take j) + 1 <
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
    omega
  obtain ⟨jm, e, hjm, hokm, hordm⟩ := NamedBar.exists_ordinal
    (okPoll (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)) (X.tr g)
    (r := okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) ((X.tr h).take j))
    (show _ < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) by omega)
  obtain ⟨pcm, km⟩ := e
  obtain ⟨pm, acqm, scm, hkm⟩ := okPoll_wait_form hokm
  dsimp only at hkm
  subst hkm
  -- another poll follows it, so its read is in the trace
  have hnext : jm + 1 < (X.tr g).length := by
    by_contra hnl
    push Not at hnl
    have h1 := okPolls_take_succ' (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) hjm
    have h2 : okPoll (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
        ⟨pcm, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) pm true acqm scm⟩ = true := hokm
    rw [h2, List.take_of_length_le hnl] at h1
    simp only [ite_true] at h1
    have h3 : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take jm) =
        okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) ((X.tr h).take j) := hordm
    omega
  obtain ⟨pcr2, src2, bs2, hrd2, hsf2⟩ := ht.poll_read hg (j := jm) (pc := pcm) (p := pm)
    (acq := acqm) (sc := scm) hjm hnext
  have hordeq : okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) ((X.tr h).take j) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take jm) := hordm.symm
  have hbs := hagree (g / L.block / 2) h g j jm pc pcm p pm pcr pcr2 acq acqm sc scm src src2 bs
    bs2 hsame rfl hwj hjm hordeq hrj hsf hrd2 hsf2
  subst hbs
  have hlt' : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take jm) + 1 <
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
    rw [← hordeq]
    exact hr_lt
  exact hcl2 (ht.cons_claims hg hσg jm pcm pm acqm scm pcr2 src2 bs rr
    (by rw [List.take_length]; exact hjm) (by rw [List.take_length]; exact hrd2) hsf2 hresp
    (by rw [List.take_length]; exact hlt'))

theorem barTime_ge (clc : Bool) (m : Nat) : 114 ≤ barTime clc m := by
  cases clc
  · simp [barTime, outBarTime, blockAt, blockSpan]; omega
  · simp [barTime, clcBarTime, blockAt, blockSpan]

/-- **A participant of a group's barrier that has made fewer arrivals blocks the thread that has
made `N`.** A thread `h` of the warp group of a consumer `g`, in `g`'s CTA, whose arrivals on the
group's barrier are fewer than the `N` of `g`, which has not exited and is in its task loop, is
pending and has a smaller rank. -/
theorem bar_lag_blocker (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hX : Consistent L kernel Prod mem0 X) (hagree : AllResponsesAgree L X)
    (hexit : ClusterExitAll L X) {g h q : Nat} {clc : Bool} {cg : Consumer.D}
    (hg : g < L.threads) (hh : h < L.threads) (hne : X.tr g ≠ [])
    (hcta : h / L.block = g / L.block)
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons cg))))
    (hxg : Consumer.exitOff cg = none) (hs0 : cg.site ≠ .setMaxReg)
    (hqg : Consumer.tidOf L g / 32 / 4 = q) (hqh : Consumer.tidOf L h / 32 / 4 = q)
    (hcl1 : clArrives (X.tr g) = 1) (hrel : ¬ Step.Released L X g)
    {N : Nat} (hN : barCount clc q (X.tr g) = N) (hN1 : 1 ≤ N)
    (hlag : barCount clc q (X.tr h) < N) :
    Descent.Obl L X (.thread h) ∧ rank L X (.thread h) < rank L X (.thread g) := by
  have hclu : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block) := by rw [hcta]
  have hnoexit : ∀ pc, (X.tr h).getLast? ≠ some ⟨pc, .exit⟩ := by
    intro pc hl
    have := hexit h pc hh hl g hg hclu.symm
    omega
  refine ⟨⟨hh, not_canceled_of_peer hX hg hne hclu, hnoexit⟩, ?_⟩
  have hub' : ∀ (y : Nat), ∀ k pc f, X.get (y, k) ≠ some ⟨pc, .ub f⟩ :=
    fun y k pc f hk => hub ⟨(y, k), pc, f, hk⟩
  -- the time of `g`
  obtain ⟨hfg, hTg⟩ := barFact_of ht clc hg hσg hqg
  rw [hN] at hfg
  have hgt : threadTime L X g = Consumer.vtime (consCount L g (X.tr g)) cg :=
    threadTime_of hσg hxg
  have hlow := bar_vtime_lt (clc := clc) hxg hs0 hTg hfg (m := N - 1) (by omega)
  have hrg : rank L X (.thread g) = threadTime L X g + 1 := by simp [rank, hrel]
  have hrh := rank_thread_le (L := L) (X := X) (g := h)
  have h114 := barTime_ge clc (N - 1)
  suffices hlt : threadTime L X h < threadTime L X g by omega
  have hwg := ht.role_warp hg (le_refl _) hσg
  simp only [roleWarp] at hwg
  have hq2 : q < 2 := by
    simp only [Consumer.tidOf] at hqg
    omega
  cases hσh : Frame.stateAt (code L) X h (X.tr h).length with
  | none =>
    have : threadTime L X h = 0 := by simp [threadTime, hσh]
    omega
  | some σ =>
    cases σ with
    | none => exact absurd hσh (ht.tracked h _ hh)
    | some d =>
      cases d with
      | inl p =>
        have hex : ThreadD.exitOff (Sum.inl p) = none := rfl
        have := threadTime_of (L := L) (X := X) hσh hex
        have h56 := Prologue.site_vtime_le p.site
        simp only [ThreadD.vtime] at this
        omega
      | inr r =>
        have hrw := ht.role_warp hh (le_refl _) hσh
        cases r with
        | loader l => simp only [roleWarp] at hrw; simp only [Consumer.tidOf] at hqh; omega
        | mma m => simp only [roleWarp] at hrw; simp only [Consumer.tidOf] at hqh; omega
        | sched s => simp only [roleWarp] at hrw; simp only [Consumer.tidOf] at hqh; omega
        | cons ch =>
          by_cases hxh : Consumer.exitOff ch = none
          · obtain ⟨hfh, hTh⟩ := barFact_of ht clc hh hσh hqh
            have hup := bar_vtime_le (clc := clc) hxh hTh hfh (m := N - 1) (by omega)
            have hht : threadTime L X h = Consumer.vtime (consCount L h (X.tr h)) ch :=
              threadTime_of hσh hxh
            omega
          · exfalso
            refine exit_excluded ht hagree hg hh (by omega) hσg hσh hxh ?_ hub
            -- the exit stage's consumer has polled fewer times than `g`
            obtain ⟨hfh, -⟩ := barFact_of ht clc hh hσh hqh
            obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := exit_counts ch hxh
            have hcg := ht.cons_tiles hg (fun k pc f hk => hub ⟨(g, k), pc, f, hk⟩) hσg
            have hho := holds_le_tileOpen cg
            have hphase := outPhase_le cg
            cases clc <;> simp only [BarFact, Bool.false_eq_true, ↓reduceIte] at hfh hfg <;> omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
