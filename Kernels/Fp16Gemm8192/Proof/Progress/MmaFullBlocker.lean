-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.MmaFullArith
public import Kernels.Fp16Gemm8192.Proof.Progress.Descent

@[expose] public section

/-! # The MMA full blocker, per execution

An MMA thread `g` of a leader CTA, stopped at a failed poll of slot `s`'s full barrier whose phase
`u` has the poll's parity, has `D = 4 u + s` commits (`mma_rank`, `mma_full_count`). The input-full
blocker (`InputFullBlocked`) names one of four things: a tensor copy on the barrier that is not
notified (rank 1), an elected warp-11 loader of the cluster whose issues on the barrier fall short
of `u + 1` rounds, an elected warp-11 loader of the leader CTA whose arrivals fall short of `u + 1`,
or an unelected warp-11 lane of the cluster (time at most 56).

A blocking loader is not in its exit stage: the counts of an exit-stage loader contradict its
shortfall, since the MMA thread has polled no more responses than the loader (`mma_polls_le_exit`,
`elected_loader_iss`, `elected_loader_arr`). Otherwise the loader's time is at most `ringAt D + 8`,
below the MMA's block `ringAt D + 10` (`vtime_of_issues`, `vtime_of_arrivals`). A thread outside its
exit stage whose time is at most `B` ranks at most `B + 1` (`rank_le_of_state`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

/-- The ring's time is above 58. -/
theorem ringAt_pos_58 (K : Nat) : 58 < ringAt K := by
  unfold ringAt blockAt blockSpan
  omega

/-- The full barrier of slot `s` that an MMA thread of `g`'s CTA polls. -/
abbrev mmaFullLoc (L : Launch) (g : Nat) (s : Fin 4) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩

/-- A loader's empty barrier is the input empty barrier of its CTA. -/
theorem emptyLoc_eq_inputEmpty (L : Launch) (cta : Nat) (s : Fin 4) :
    InputRing.emptyLoc L cta s = inputEmpty L cta s := by
  simp only [InputRing.emptyLoc, inputEmpty, Bar.loc, Bar.off]
  congr 1
  omega

/-- A loader not in its exit stage has no exit offset. -/
theorem exitOff_loader_none {l : Loader.D} (h : l.site.done = false) : Loader.exitOff l = none := by
  obtain ⟨site, m, n, q, cp, resp, x⟩ := l
  cases site <;> simp_all [Loader.exitOff, Loader.Site.done]

/-- The exit stage's sites. -/
theorem exit_site_of_done {l : Loader.D} (h : l.site.done = true) :
    l.site = .exitArrive ∨ l.site = .exitWait ∨ l.site = .exit := by
  obtain ⟨site, m, n, q, cp, resp, x⟩ := l
  cases site <;> simp_all [Loader.Site.done]

/-- A prologue time is at most 56. -/
theorem prologue_vtime_le (s : Prologue.Site) : Prologue.Site.vtime s ≤ 56 := by
  cases s with
  | init i =>
    have hi := i.isLt
    show 4 + 2 * i.val ≤ 56
    omega
  | shfl => decide
  | elect => decide
  | alloc => decide
  | allocWrite => decide
  | warpBar => decide
  | fence => decide
  | fenceInit => decide
  | arrive => decide
  | wait => decide
  | setMaxReg => decide
  | roleElect => decide

/-- **A thread outside its exit stage ranks at most one above its time.** A thread whose state is
`none` (dead) has time zero. -/
theorem rank_le_of_state {L : Launch} {X : Execution} {g B : Nat}
    (h : Frame.stateAt (code L) X g (X.tr g).length = none ∨
      ∃ d, Frame.stateAt (code L) X g (X.tr g).length = some (some d) ∧ d.exitOff = none ∧
        d.vtime L g (X.tr g) ≤ B) :
    rank L X (.thread g) ≤ B + 1 := by
  refine le_trans rank_thread_le ?_
  rcases h with h | ⟨d, hd, he, hv⟩
  · simp [threadTime, h]
  · rw [threadTime_of hd he]
    omega

/-- **A thread whose trace is not empty, and whose cluster has every arrival, is pending** unless it
has exited: an exit would make its cluster's arrivals two. -/
theorem pending_of_cluster {L : Launch} {X : Execution} (hce : ClusterExitAll L X) {g h : Nat}
    (hg : g < L.threads) (hh : h < L.threads)
    (hc : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block))
    (hclg : clArrives (X.tr g) = 1) (hne : X.tr h ≠ []) : Frame.Pending L X h := by
  refine ⟨hh, fun hcan => hne hcan.1, fun pc hl => ?_⟩
  have h2 := hce h pc hh hl g hg hc.symm
  omega

/-- The ordinal of a successful poll: the `r`-th successful poll of `m` is an event of the trace,
and the successful polls before it are `r`. -/
theorem okPolls_ordinal' {m : Loc} (es : List Event) {r : Nat} (hr : r < okPolls m es) :
    ∃ j e, es[j]? = some e ∧ okPoll m e = true ∧ okPolls m (es.take j) = r := by
  induction es generalizing r with
  | nil => simp [okPolls] at hr
  | cons a t ih =>
    by_cases ha : okPoll m a = true
    · have e2 : okPolls m (a :: t) = okPolls m t + 1 := by simp [okPolls, ha]
      cases r with
      | zero =>
        refine ⟨0, a, by simp, ha, ?_⟩
        simp [okPolls]
      | succ r =>
        have hr' : r < okPolls m t := by
          rw [e2] at hr
          omega
        obtain ⟨j, e, hj, he, hjr⟩ := ih hr'
        have e1 : okPolls m (a :: t.take j) = okPolls m (t.take j) + 1 := by
          simp [okPolls, ha]
        refine ⟨j + 1, e, by simpa using hj, he, ?_⟩
        rw [List.take_succ_cons, e1, hjr]
    · have ha' : okPoll m a = false := by simpa using ha
      have e2 : okPolls m (a :: t) = okPolls m t := by simp [okPolls, ha']
      have hr' : r < okPolls m t := by
        rw [e2] at hr
        exact hr
      obtain ⟨j, e, hj, he, hjr⟩ := ih hr'
      have e1 : okPolls m (a :: t.take j) = okPolls m (t.take j) := by simp [okPolls, ha']
      refine ⟨j + 1, e, by simpa using hj, he, ?_⟩
      rw [List.take_succ_cons, e1]
      exact hjr

/-- **An exit-stage loader's response polls bound the MMA's.** The loader's last response poll is
read claimless, and the MMA thread, polling the same response with a poll after it, reads it
claiming: so the MMA thread has not polled more responses than the loader. -/
theorem mma_polls_le_exit {L : Launch} {X : Execution} (ht : ThreadFacts L X)
    (hag : AllResponsesAgree L X) {g h : Nat} {mm : Mma.D} {l : Loader.D}
    (hg : g < L.threads) (hh : h < L.threads) (hcl : h / L.block / 2 = g / L.block / 2)
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma mm))))
    (hσh : Frame.stateAt (code L) X h (X.tr h).length = some (some (.inr (.loader l))))
    (hdisj : (∃ i : Fin 4, l.site = .drain i) ∨ l.site = .exitArrive ∨ l.site = .exitWait ∨
      l.site = .exit)
    (hpos : 0 < okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h)) :
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) ≤
      okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨j, pc, p, acq, sc, pcr, a, bs, rr, hwj, hrj, ha, hsz, hresp, hncl, hcnt⟩ :=
    ht.loader_exit_claim hh hσh hdisj hpos
  have hr_lt : okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) ((X.tr h).take j) <
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
    omega
  obtain ⟨jm, e, hjm, hokm, hordm⟩ :=
    okPolls_ordinal' (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) hr_lt
  obtain ⟨pcm, km⟩ := e
  obtain ⟨pm, acqm, scm, hkm⟩ := okPoll_wait_form hokm
  dsimp only at hkm
  subst hkm
  have hcount : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take jm) + 1 <
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
    omega
  obtain ⟨pcr2, a2, bs2, rr2, hrd2, ha2, hs2, hresp2, hcl2⟩ :=
    ht.mma_claims_before hg hσg jm pcm pm acqm scm hjm hcount
  have hbs := hag (h / L.block / 2) h g j jm pc pcm p pm pcr pcr2 acq acqm sc scm a a2 bs bs2 rfl
    hcl.symm hwj hjm (by omega) hrj ⟨ha, hsz⟩ hrd2 ⟨ha2, hs2⟩
  have hrr : rr = rr2 := by
    rw [hbs] at hresp
    exact Option.some.inj (hresp.symm.trans hresp2)
  exact hncl (by rw [hrr]; exact hcl2)

/-- **An elected loader of the cluster, short of issues on the barrier.** Its exit stage is excluded
by the counts of the exit stage and the response polls; otherwise its time is at most the MMA's
block. -/
theorem elected_loader_iss {L : Launch} {X : Execution} (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hce : ClusterExitAll L X) (hag : AllResponsesAgree L X) {g h : Nat} {mm : Mma.D} {s : Fin 4}
    {u : Nat} (hg : g < L.threads) (hh : h < L.threads)
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma mm))))
    (hclg : clArrives (X.tr g) = 1)
    (hcl : h / L.block / 2 = g / L.block / 2)
    (hcc : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block))
    (hw : h % L.block / 32 = 11)
    (hel : ∃ j pc mask inst, X.Elect (h, j) pc mask inst (laneOf L h))
    (hD : mmaCount L g (X.tr g) = 4 * u + s.val)
    (htask : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) =
      mmaCount L g (X.tr g) / 128 + 1)
    (hI : (X.tr h).countP (issuesTo (InputRing.fullLoc L (g / L.block / 2) s)) < 3 * (u + 1)) :
    ∃ o', Descent.Obl L X o' ∧ rank L X o' < ringAt (mmaCount L g (X.tr g)) + 10 := by
  have hs4 := s.isLt
  have hel' := hel
  obtain ⟨j, pc, mask, inst, hj⟩ := hel
  have hXh : X.tr h ≠ [] := by
    intro he
    have hj' : (X.tr h)[j]? = some ⟨pc, .elect mask inst (laneOf L h)⟩ := hj
    rw [he] at hj'
    simp at hj'
  have hpend := pending_of_cluster hce hg hh hcc hclg hXh
  have hnoub : ∀ k pc' f, X.get (h, k) ≠ some ⟨pc', .ub f⟩ :=
    fun k pc' f hk => hub ⟨(h, k), pc', f, hk⟩
  have hfo : Loader.fullOf L h s = InputRing.fullLoc L (g / L.block / 2) s := by
    simp only [Loader.fullOf, hcl]
  rcases hσh : Frame.stateAt (code L) X h (X.tr h).length with _ | o
  · refine ⟨.thread h, hpend, ?_⟩
    have h1 := rank_le_of_state (B := 0) (Or.inl hσh)
    have h2 := ringAt_pos_58 (mmaCount L g (X.tr g))
    omega
  · cases o with
    | none => exact absurd hσh (ht.tracked h _ hh)
    | some d =>
      cases d with
      | inl p =>
        refine ⟨.thread h, hpend, ?_⟩
        have h1 := rank_le_of_state (B := 56) (Or.inr ⟨.inl p, hσh, rfl, prologue_vtime_le p.site⟩)
        have h2 := ringAt_pos_58 (mmaCount L g (X.tr g))
        omega
      | inr r =>
        have hrw := ht.role_warp hh (le_refl _) hσh
        cases r with
        | mma m =>
          simp only [roleWarp] at hrw
          omega
        | sched sd =>
          simp only [roleWarp] at hrw
          omega
        | cons c =>
          simp only [roleWarp] at hrw
          omega
        | loader l =>
          by_cases hdone : l.site.done = true
          · -- the exit stage: its counts and the MMA's response polls give a contradiction
            exfalso
            obtain ⟨hK0, hR0⟩ := ht.loader_elected_exit hh hw hel' hσh hdone
            have hex := (ht.loader_exit_exact hh hnoub hσh hdone hK0).1 s
            have hT := ht.loader_exit_tasks hh hσh hdone hK0
            have hRa := (ht.loader_rank hh hσh).1 s
            have hpoll := mma_polls_le_exit ht hag hg hh hcl hσg hσh
              (by rcases exit_site_of_done hdone with h1 | h1 | h1
                  · exact Or.inr (Or.inl h1)
                  · exact Or.inr (Or.inr (Or.inl h1))
                  · exact Or.inr (Or.inr (Or.inr h1)))
              hR0
            have hex' : (X.tr h).countP (issuesTo (Loader.fullOf L h s)) + 3 =
                3 * okPolls (InputRing.emptyLoc L (h / L.block) s) (X.tr h) := hex
            rw [emptyLoc_eq_inputEmpty, hfo] at hex'
            have hM := htask
            omega
          · have hdf : l.site.done = false := by simpa using hdone
            refine ⟨.thread h, hpend, ?_⟩
            have hq8 := ht.loader_q8 hh hσh
            have hK := ht.loader_site_count hh hσh
            have hex := (ht.loader_exact hh hnoub hσh hdf).1 s
            have hRa := (ht.loader_rank hh hσh).1 s
            have hex' : (X.tr h).countP (issuesTo (Loader.fullOf L h s)) +
                Loader.remaining l s + 3 * Loader.drained l s =
                3 * okPolls (InputRing.emptyLoc L (h / L.block) s) (X.tr h) := hex
            rw [emptyLoc_eq_inputEmpty, hfo] at hex'
            have hv := vtime_of_issues (l := l) (K := loaderCount L h (X.tr h))
              (D := mmaCount L g (X.tr g)) (I := (X.tr h).countP
                (issuesTo (InputRing.fullLoc L (g / L.block / 2) s)))
              (u := u) (s := s) hD hdf hq8 hK (by rw [hex', hRa]) hI
            have h1 := rank_le_of_state (B := ringAt (mmaCount L g (X.tr g)) + 8)
              (Or.inr ⟨.inr (.loader l), hσh, exitOff_loader_none hdf, hv⟩)
            omega

/-- **An elected loader of the leader CTA, short of arrivals on the barrier.** Its exit stage is
excluded as in `elected_loader_iss`; otherwise its time is at most the MMA's block. -/
theorem elected_loader_arr {L : Launch} {X : Execution} (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hce : ClusterExitAll L X) (hag : AllResponsesAgree L X) {g h : Nat} {mm : Mma.D} {s : Fin 4}
    {u : Nat} (hg : g < L.threads) (hh : h < L.threads)
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma mm))))
    (hclg : clArrives (X.tr g) = 1)
    (hcl : h / L.block / 2 = g / L.block / 2) (hlh : h / L.block % 2 = 0)
    (hcc : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block))
    (hw : h % L.block / 32 = 11)
    (hel : ∃ j pc mask inst, X.Elect (h, j) pc mask inst (laneOf L h))
    (hD : mmaCount L g (X.tr g) = 4 * u + s.val)
    (htask : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) =
      mmaCount L g (X.tr g) / 128 + 1)
    (hA : arrivals (InputRing.fullLoc L (g / L.block / 2) s) (X.tr h) < u + 1) :
    ∃ o', Descent.Obl L X o' ∧ rank L X o' < ringAt (mmaCount L g (X.tr g)) + 10 := by
  have hs4 := s.isLt
  have hel' := hel
  obtain ⟨j, pc, mask, inst, hj⟩ := hel
  have hXh : X.tr h ≠ [] := by
    intro he
    have hj' : (X.tr h)[j]? = some ⟨pc, .elect mask inst (laneOf L h)⟩ := hj
    rw [he] at hj'
    simp at hj'
  have hpend := pending_of_cluster hce hg hh hcc hclg hXh
  have hnoub : ∀ k pc' f, X.get (h, k) ≠ some ⟨pc', .ub f⟩ :=
    fun k pc' f hk => hub ⟨(h, k), pc', f, hk⟩
  have hfo : Loader.fullOf L h s = InputRing.fullLoc L (g / L.block / 2) s := by
    simp only [Loader.fullOf, hcl]
  have hleader : Loader.leader L h = true := by simp [Loader.leader, hlh]
  rcases hσh : Frame.stateAt (code L) X h (X.tr h).length with _ | o
  · refine ⟨.thread h, hpend, ?_⟩
    have h1 := rank_le_of_state (B := 0) (Or.inl hσh)
    have h2 := ringAt_pos_58 (mmaCount L g (X.tr g))
    omega
  · cases o with
    | none => exact absurd hσh (ht.tracked h _ hh)
    | some d =>
      cases d with
      | inl p =>
        refine ⟨.thread h, hpend, ?_⟩
        have h1 := rank_le_of_state (B := 56) (Or.inr ⟨.inl p, hσh, rfl, prologue_vtime_le p.site⟩)
        have h2 := ringAt_pos_58 (mmaCount L g (X.tr g))
        omega
      | inr r =>
        have hrw := ht.role_warp hh (le_refl _) hσh
        cases r with
        | mma m =>
          simp only [roleWarp] at hrw
          omega
        | sched sd =>
          simp only [roleWarp] at hrw
          omega
        | cons c =>
          simp only [roleWarp] at hrw
          omega
        | loader l =>
          by_cases hdone : l.site.done = true
          · exfalso
            obtain ⟨hK0, hR0⟩ := ht.loader_elected_exit hh hw hel' hσh hdone
            have hex := (ht.loader_exit_exact hh hnoub hσh hdone hK0).2 hleader s
            have hT := ht.loader_exit_tasks hh hσh hdone hK0
            have hRa := (ht.loader_rank hh hσh).1 s
            have hpoll := mma_polls_le_exit ht hag hg hh hcl hσg hσh
              (by rcases exit_site_of_done hdone with h1 | h1 | h1
                  · exact Or.inr (Or.inl h1)
                  · exact Or.inr (Or.inr (Or.inl h1))
                  · exact Or.inr (Or.inr (Or.inr h1)))
              hR0
            have hex' : arrivals (Loader.fullOf L h s) (X.tr h) + 1 =
                okPolls (InputRing.emptyLoc L (h / L.block) s) (X.tr h) := hex
            rw [emptyLoc_eq_inputEmpty, hfo] at hex'
            have hM := htask
            omega
          · have hdf : l.site.done = false := by simpa using hdone
            refine ⟨.thread h, hpend, ?_⟩
            have hq8 := ht.loader_q8 hh hσh
            have hK := ht.loader_site_count hh hσh
            have hex := (ht.loader_exact hh hnoub hσh hdf).2 hleader s
            have hRa := (ht.loader_rank hh hσh).1 s
            have hex' : arrivals (Loader.fullOf L h s) (X.tr h) +
                (if Loader.pending l s then 1 else 0) + Loader.drained l s =
                okPolls (InputRing.emptyLoc L (h / L.block) s) (X.tr h) := hex
            rw [emptyLoc_eq_inputEmpty, hfo] at hex'
            have hv := vtime_of_arrivals (l := l) (K := loaderCount L h (X.tr h))
              (D := mmaCount L g (X.tr g)) (A := arrivals (InputRing.fullLoc L (g / L.block / 2) s)
                (X.tr h))
              (u := u) (s := s) hD hdf hq8 hK (by rw [hex', hRa]) hA
            have h1 := rank_le_of_state (B := ringAt (mmaCount L g (X.tr g)) + 8)
              (Or.inr ⟨.inr (.loader l), hσh, exitOff_loader_none hdf, hv⟩)
            omega

/-- **The MMA full blocker, per execution.** An MMA thread of a leader CTA, stopped at a failed poll
of slot `s`'s full barrier whose phase has the poll's parity, has an open obligation of rank below
its block `ringAt D + 10`, `D` its commits. -/
theorem mma_full_blocked_of {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (ht : ThreadFacts L X) (hub : ¬ HasUb X) (hIF : InputFullBlocked L X)
    (hag : AllResponsesAgree L X) (hce : ClusterExitAll L X)
    {g : Nat} {mm : Mma.D} {s : Fin 4} {pc : Nat} {sc : MbarScope} {before : MBarrier.State}
    (hg : g < L.threads) (hσ : Frame.stateAt (code L) X g (X.tr g).length =
      some (some (.inr (.mma mm))))
    (hσp : Frame.stateAt (code L) X g ((X.tr g).length - 1) = some (some (.inr (.mma mm))))
    (hs : mm.site = .full s)
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait (mmaFullLoc L g s) (mm.fp % 2) false true sc⟩)
    (hstate : MBarrier.stateBefore (X.objects (mmaFullLoc L g s))
      (X.objects (mmaFullLoc L g s)).length = some before)
    (hpar : before.phase % 2 = mm.fp % 2) :
    ∃ o', Descent.Obl L X o' ∧ rank L X o' < ringAt (mmaCount L g (X.tr g)) + 10 := by
  have hub' : ∀ k pc' f, X.get (g, k) ≠ some ⟨pc', .ub f⟩ :=
    fun k pc' f hk => hub ⟨(g, k), pc', f, hk⟩
  have hlead : g / L.block % 2 = 0 := by
    have h0 := ht.mma_lead hg hσ
    unfold Mma.Lead at h0
    rcases h0 with h1 | h1 | h1 | h1
    · rw [hs] at h1
      cases h1
    · rw [hs] at h1
      cases h1
    · rw [hs] at h1
      cases h1
    · exact h1
  have hfl : InputRing.fullLoc L (g / L.block / 2) s = mmaFullLoc L g s := by
    have h2 : 2 * (g / L.block / 2) = g / L.block := by omega
    simp only [InputRing.fullLoc, mmaFullLoc, h2]
  have hlast' : (X.tr g).getLast? =
      some ⟨pc, .wait (InputRing.fullLoc L (g / L.block / 2) s) (mm.fp % 2) false true sc⟩ := by
    rw [hfl]
    exact hlast
  have hstate' : MBarrier.stateBefore (X.objects (InputRing.fullLoc L (g / L.block / 2) s))
      (X.objects (InputRing.fullLoc L (g / L.block / 2) s)).length = some before := by
    rw [hfl]
    exact hstate
  obtain ⟨hph, hcases⟩ := hIF g mm s pc sc before hg hlead hσ hs hlast' hstate' hpar
  have hfull := ht.mma_full_count hg hub' hσ hs
  have hrk := (ht.mma_rank hg hσ).2
  simp only [hs] at hrk
  have htask := ht.mma_task_count hg hσ
  simp only [hs] at htask
  have hclg : clArrives (X.tr g) = 1 := by
    have h1 := ht.cl_phase hg hσ
    simpa [ThreadD.clPhase, hs] using h1
  have hu : before.phase = (mmaCount L g (X.tr g) + 3 - s.val) / 4 := by
    rw [hph, hfl]
    exact hfull
  have hD : mmaCount L g (X.tr g) = 4 * before.phase + s.val := by
    have hs4 := s.isLt
    have h1 := hrk.1
    have h2 := hrk.2
    omega
  have hcc : ∀ h', h' / L.block / 2 = g / L.block / 2 →
      L.clusterOfCta (h' / L.block) = L.clusterOfCta (g / L.block) := by
    intro h' hh'
    simp only [clusterOfCta_eq hpre]
    exact hh'
  rcases hcases with ⟨i, mapAddress, s', hti, _, hnot⟩ |
      ⟨h, hh, hcl, hw, hel, hI⟩ | ⟨h, hh, hcl, hw, hel, hA⟩ | ⟨h, hh, hcl, hw, hnoel⟩
  · -- a tensor copy on the barrier is issued and not notified
    refine ⟨.tensor, ?_, ?_⟩
    · simp only [Descent.Obl]
      intro hall
      obtain ⟨obs, hobs, hn⟩ := hall i mapAddress s' hti
      exact hnot ⟨obs, hobs, hn⟩
    · have h1 := ringAt_pos_58 (mmaCount L g (X.tr g))
      simp only [rank]
      omega
  · -- an elected loader of the cluster has issued fewer copies than the phase
    exact elected_loader_iss ht hub hce hag hg hh hσ hclg hcl (hcc h hcl) hw hel hD htask
      hI
  · -- an elected loader of the leader CTA has arrived fewer times than the phase
    have hcl' : h / L.block / 2 = g / L.block / 2 := by rw [hcl]
    have hlh : h / L.block % 2 = 0 := by rw [hcl]; exact hlead
    exact elected_loader_arr ht hub hce hag hg hh hσ hclg hcl' hlh (hcc h hcl') hw hel hD htask
      hA
  · -- an unelected warp-11 lane of the cluster: its time is at most 56
    have hcl' : h / L.block / 2 = g / L.block / 2 := hcl
    obtain ⟨d, hσd, ⟨p, rfl⟩, hexo, hv⟩ := ht.loader_unelected hh hw hnoel
    have hev : X.get (g, (X.tr g).length - 1) = some
      ⟨pc, .wait (mmaFullLoc L g s) (mm.fp % 2) false true sc⟩ := by
      show (X.tr g)[(X.tr g).length - 1]? = _
      rw [← List.getLast?_eq_getElem?]
      exact hlast
    have hXh : X.tr h ≠ [] := ht.cluster_started hg hev hσp hh (hcc h hcl')
    have hpend := pending_of_cluster hce hg hh (hcc h hcl') hclg hXh
    refine ⟨.thread h, hpend, ?_⟩
    have h1 := rank_le_of_state (B := 56) (Or.inr ⟨.inl p, hσd, hexo, hv⟩)
    have h2 := ringAt_pos_58 (mmaCount L g (X.tr g))
    omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
