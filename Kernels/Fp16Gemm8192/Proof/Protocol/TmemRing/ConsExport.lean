-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Exit
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.ConsBlocker
public import Kernels.Fp16Gemm8192.Proof.Protocol.RingRecords
public import Kernels.Fp16Gemm8192.Proof.Protocol.Elected

@[expose] public section

/-! # Who blocks a consumer at its accumulator-full wait (the export `ConsAccBlockedX`)

A consumer `g` stopped at a failed poll of its accumulator-full barrier finds the barrier at its
successful polls `T` (`cons_phase`), and the cluster's commits are notified (`hall`) or one is open.
With every commit notified, the leader lane `h` of the producer warp commits at most `T`
(`commits_le_phase`). Its state gives the rank: unelected, or working with its tasks `N ≤ T`
(`mma_vtime_le`), or stopped. A finished producer would have committed all its tasks, `P`
(`finished_acc_count`, `mma_exit_acc`), with `P` successful response polls; the consumer's
`T + 1` successful response polls are at most `P` (`clc_count_le`): a contradiction. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow MBarrier AsyncCopy

noncomputable section

set_option maxRecDepth 100000

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The last of `n + 1` successes of a predicate is at an index whose prefix has `n` of them. -/
theorem exists_last_success {α : Type} (p : α → Bool) :
    ∀ (es : List α) (n : Nat), es.countP p = n + 1 →
      ∃ j, ∃ hj : j < es.length, p (es[j]'hj) = true ∧ (es.take j).countP p = n
  | [], _, h => by simp at h
  | e :: es, n, h => by
    by_cases hp : p e = true
    · cases n with
      | zero => exact ⟨0, by simp, by simpa using hp, by simp⟩
      | succ m =>
        have hes : es.countP p = m + 1 := by
          rw [List.countP_cons] at h
          simp only [hp, ite_true] at h
          omega
        obtain ⟨j, hj, hpj, hc⟩ := exists_last_success p es m hes
        refine ⟨j + 1, by simp only [List.length_cons]; omega, by simpa using hpj, ?_⟩
        rw [List.take_succ_cons, List.countP_cons, hp, hc]
        simp only [ite_true]
    · have hes : es.countP p = n + 1 := by
        rw [List.countP_cons] at h
        have hf : p e = false := by simpa using hp
        simp only [hf, Bool.false_eq_true, ite_false, add_zero] at h
        exact h
      obtain ⟨j, hj, hpj, hc⟩ := exists_last_success p es n hes
      refine ⟨j + 1, by simp only [List.length_cons]; omega, by simpa using hpj, ?_⟩
      have hf : p e = false := by simpa using hp
      rw [List.take_succ_cons, List.countP_cons, hf, hc]
      simp only [Bool.false_eq_true, ite_false, add_zero]

/-- **The counting bound on a consumer's successful response polls.** A consumer `g` of CTA
`g / L.block` in the cluster of thread `h` polls the response barrier successfully at `j`, and the
leader thread `h` polls it at `jh` and then reads a response claiming no CTA: the consumer's polls
before `j` are at most `h`'s polls before `jh`. -/
theorem clc_count_le (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) {g h : Nat}
    (hcl : g / L.block / 2 = h / L.block / 2) {j jh : Nat}
    (hgj : ∃ pc p acq sc, X.get (g, j) =
      some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    (hhj : ∃ pc p acq sc, X.get (h, jh) =
      some ⟨pc, .wait (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    (hhr : ∃ pcr src bs rr, X.get (h, jh + 1) = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, h / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr) :
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) ≤
      okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) ((X.tr h).take jh) := by
  obtain ⟨pc, p, acq, sc, hgj⟩ := hgj
  obtain ⟨pch, ph, acqh, sch, hhj⟩ := hhj
  obtain ⟨pcr, srch, bsh, rr, hhr, hsf, hrr, hnc⟩ := hhr
  obtain ⟨i, s, tg, r, hi, hi1, hi2, hcount, hobs, hres, -⟩ :=
    hv (g / L.block / 2) g j pc p acq sc rfl hgj
  obtain ⟨f, sf, tgf, rf, hf, hf1, hf2, hfcount, hfobs, hfres, hfread⟩ :=
    hv (g / L.block / 2) h jh pch ph acqh sch hcl.symm hhj
  -- the failed read decodes to the failed response `rf`
  have hbs := hfread pcr srch bsh hhr hsf
  have hrf : rr = rf := by
    have h1 := hrr
    rw [hbs, responseOf_clc] at h1
    exact (Option.some.inj h1).symm
  have hnc' : ¬ Loader.claims rf := hrf ▸ hnc
  -- the consumer's request and the failed request, with their CTAs in the cluster
  obtain ⟨s1, tg1, hiss1, hct1, -⟩ := hobs.2.2.choose_spec.clc
  obtain ⟨s2, tg2, hiss2, hct2, -⟩ := hfobs.2.2.choose_spec.clc
  obtain ⟨pci, hei⟩ := hiss1
  have hprod := (ClcRing.issue_facts hpre hX ht hei hct1 rfl).1
  have hei' : X.get (ClcRing.producer L X (g / L.block / 2), i.2) =
      some ⟨pci, .clcIssue s1 tg1⟩ := by
    rw [← hprod]
    exact hei
  have hcta' : ∃ c' ∈ tg2, c' / 2 = g / L.block / 2 := ⟨h / L.block, hct2, hcl.symm⟩
  have hA := ClcRing.issues_le_failed hpre hX ht hv (c := g / L.block / 2) hei' hct1 rfl
    (i := f) (s := s2) (tg' := tg2) (r := rf) hiss2 hcta' hfres hnc'
  unfold ClcRing.issuesBefore at hA
  rw [← hprod, hcount, hfcount] at hA
  exact hA

/-- The commit targets of every thread's accumulator commits, from the thread facts. -/
theorem acc_targets (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {j : Fin 2} :
    ∀ (h k pc : Nat) (sp : TcCommit.Spec) (r : Fin 16), h < L.threads →
      X.get (h, k) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = Bar.loc L (h / L.block) ⟨.acc, j.val, true⟩ → r.val < 2 →
      TcCommit.target sp r = some (Bar.loc L (h / L.block + r.val) ⟨.acc, j.val, true⟩) := by
  intro h k pc sp r hh hget hmb hr
  obtain ⟨d, hd⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
  exact ht.acc_commit_ranks r hh hget hd rfl hmb hr

/-- With every input commit of a finished producer, its task count is its successful response polls.
-/
theorem mmaCount_div_eq (L : Launch) (h : Nat) (es : List Event)
    (hfin : ∀ s : Fin 4, es.countP (commitsTo (inputEmpty L (h / L.block) s)) =
      32 * okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) es) :
    mmaCount L h es / 128 = okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) es := by
  unfold mmaCount
  simp only [hfin]
  simp
  omega

/-- **A finished producer contradicts a blocked consumer.** A finished leader lane `h` made `P`
successful response polls, the last one reading a response that claims no CTA, and committed `P`
tasks to the buffer (`hN`, `hfin`). A consumer `g` of the cluster at tile `T` has `T + 1` successful
response polls (`hTg`), at most the lane's `P - 1` before its last one (`clc_count_le`), and its
accumulator commits are at most `T` (`hNT`): `P ≤ T < P`. -/
theorem finished_false {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hv : ReaderValues L X) {g h T : Nat} (hcl : g / L.block / 2 = h / L.block / 2) {j : Fin 2}
    (hTg : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) = T + 1)
    (hfinh : ∃ j' pc' p' acq' sc' pcr, ∃ src : Acc, ∃ bs rr,
      okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) ((X.tr h).take j') + 1 =
        okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) ∧
      X.get (h, j') = some ⟨pc', .wait (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) p' true acq' sc'⟩ ∧
      X.get (h, j' + 1) = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, h / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr)
    (hfin : ∀ s : Fin 4, (X.tr h).countP (commitsTo (inputEmpty L (h / L.block) s)) =
      32 * okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h))
    (hN : (X.tr h).countP (commitsTo (Bar.loc L (h / L.block) ⟨.acc, j.val, true⟩)) =
      mmaCount L h (X.tr h) / 128)
    (hNT : (X.tr h).countP (commitsTo (Bar.loc L (h / L.block) ⟨.acc, j.val, true⟩)) ≤ T) :
    False := by
  obtain ⟨j', pc', p', acq', sc', pcr, src, bs, rr, hcnt, hhj, hhr, hsf, hrr, hnc⟩ := hfinh
  obtain ⟨jg, hjg, hokg, hcntg⟩ :=
    exists_last_success (okPoll (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩))
    (X.tr g) T hTg
  obtain ⟨pcg, pg, acqg, scg, hgj⟩ := okPoll_wait_form hokg
  have hgj' : X.get (g, jg) =
    some ⟨pcg, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) pg true acqg scg⟩ := by
    show (X.tr g)[jg]? = _
    rw [List.getElem?_eq_getElem hjg, hgj]
  have hle := clc_count_le hpre hX ht hv hcl ⟨pcg, pg, acqg, scg, hgj'⟩
    ⟨pc', p', acq', sc', hhj⟩ ⟨pcr, src, bs, rr, hhr, hsf, hrr, hnc⟩
  have hTg' : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take jg) = T := hcntg
  have hmm : mmaCount L h (X.tr h) =
      128 * okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) := by
    unfold mmaCount
    simp only [hfin]
    simp
    omega
  have hNP : mmaCount L h (X.tr h) / 128 =
      okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) := by
    rw [hmm]
    omega
  rw [hNP] at hN
  omega

/-- **The consumer's accumulator-full wait blocker** (the export `ConsAccBlockedX`). -/
theorem cons_acc_blocked_x (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X)
    (hub : ∀ g k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) : ConsAccBlockedX L X := by
  intro g c pc sc before hg hσ hs hlast hstate hpar
  have hb : L.block = 384 := hpre.block
  have hwarp := ht.role_warp hg (le_refl _) hσ
  simp only [roleWarp] at hwarp
  have hw2 : g % L.block / 32 / 4 < 2 := by omega
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hlen : (X.tr g).length - 1 = ys.length := by
    rw [hys]
    simp
  have hget : X.get (g, (X.tr g).length - 1) = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩) c.ap false true sc⟩ :=
        by
    change (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?, hlast]
  -- the state before the failed poll
  obtain ⟨d, hd⟩ : ∃ d, Frame.stateAt (code L) X g ((X.tr g).length - 1) = some (some d) := by
    obtain ⟨d, hσ'⟩ := Frame.event_state ht.sound hX ht.tracked hget nofun
    exact ⟨d, hσ'⟩
  obtain ⟨c', hc'⟩ : ∃ c', Frame.stateAt (code L) X g ((X.tr g).length - 1) =
      some (some (.inr (.cons c'))) :=
    ht.cons_acc_state hg (by omega) hget rfl
  -- the consumer's phase and tiles
  have hT := cons_phase hpre hX ht hg (c := g / L.block / 2) (j := ⟨g % L.block / 32 / 4, hw2⟩)
    (k := ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩) rfl rfl (by simp only; omega) hd hlast
    hstate hpar
  have hT' : before.phase = consCount L g (X.tr g) := by
    rw [consCount_eq_own hX ht hg hw2]
    exact hT
  have hPT := ht.cons_tiles hg (fun k pc' f => hub g k pc' f) hσ
  simp only [Consumer.tileOpen, Consumer.holds, hs] at hPT
  have hTg : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) =
      consCount L g (X.tr g) + 1 := by
    omega
  -- every commit notified, or one open
  by_cases hall : ∀ i s r m, X.Commit i s → TcCommit.target s r = some m → r ∈ X.tcNotified i
  swap
  · left
    push Not at hall
    exact hall
  -- the consumer's cluster: its leader CTA, and the producer warp of its buffer
  have hgrid : g / L.block < L.grid := by
    have hg' : g < L.grid * L.block := hg
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact hg'
  have hcl_of : ∀ h : Nat, h / L.block / 2 = g / L.block / 2 →
      L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block) := by
    intro h hh
    rw [clusterOfCta_eq hpre, clusterOfCta_eq hpre]
    omega
  by_cases hun : ∃ h, h < L.threads ∧ h / L.block = g / L.block / 2 * 2 ∧
      h % L.block / 32 = 8 + g % L.block / 32 / 4 ∧
      ∀ j' pc' mask inst leader, ¬ X.Elect (h, j') pc' mask inst leader
  · -- an unelected lane of the producer warp
    obtain ⟨h, hh, hhc, hhw, hne⟩ := hun
    have hl' : h / L.block % 2 = 0 := by omega
    have hw' : h % L.block / 32 = 8 ∨ h % L.block / 32 = 9 := by omega
    obtain ⟨d', hd', hx', hv'⟩ := ht.mma_unelected hh hl' hw' hne
    have htr : X.tr h ≠ [] :=
      ht.cluster_started hg hget hc' hh (hcl_of h (by omega))
    have hne' : ∀ pc', (X.tr h).getLast? ≠ some ⟨pc', .exit⟩ := by
      intro pc' hlast'
      rw [ht.exited_state hh hlast'] at hd'
      cases hd'
    refine Or.inr (Or.inl ⟨h, hh, hhc, hhw, htr, hne', d', hd', hx', ?_⟩)
    exact le_trans hv' (le_trans (by norm_num) (Nat.le_add_left 4160 _))
  · -- every lane of the producer warp is elected: take the elected lane
    push Not at hun
    have hbpos : 0 < L.block := by omega
    obtain ⟨r0, hr0⟩ : ∃ r0, r0 = (8 + g % L.block / 32 / 4) * 32 := ⟨_, rfl⟩
    have hr0lt : r0 < L.block := by
      rw [hr0]
      omega
    obtain ⟨h0, hh0⟩ : ∃ h0, h0 = r0 + g / L.block / 2 * 2 * L.block := ⟨_, rfl⟩
    have hh0c : h0 / L.block = g / L.block / 2 * 2 := by
      rw [hh0, Nat.add_mul_div_right _ _ hbpos, Nat.div_eq_of_lt hr0lt, zero_add]
    have hh0w : h0 % L.block / 32 = 8 + g % L.block / 32 / 4 := by
      rw [hh0, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr0lt, hr0]
      omega
    have hh0lt : h0 < L.threads := by
      have hdiv : h0 / L.block < L.grid := by
        rw [hh0c]
        omega
      have hlt := (Nat.div_lt_iff_lt_mul hbpos).1 hdiv
      unfold Launch.threads
      exact hlt
    obtain ⟨j0, pc0, mask0, inst0, leader0, hel0⟩ := hun h0 hh0lt hh0c hh0w
    obtain ⟨h1, j1, hh1, hsame, hel1'⟩ := elected_of_elect hpre hX hel0
    have hc1 : h1 / L.block = g / L.block / 2 * 2 := by
      have e : h0 / L.block = h1 / L.block := hsame.1.2.2
      rw [← e, hh0c]
    have hw1' : h1 % L.block / 32 = 8 + g % L.block / 32 / 4 := by
      have e : h0 % L.block / 32 = h1 % L.block / 32 := hsame.2
      rw [← e, hh0w]
    have hl1 : h1 / L.block % 2 = 0 := by omega
    have hw1 : h1 % L.block / 32 = 8 ∨ h1 % L.block / 32 = 9 := by omega
    have hh1c : h1 / L.block = g / L.block / 2 * 2 := hc1
    have hh1w : h1 % L.block / 32 = 8 + g % L.block / 32 / 4 := hw1'
    have hcl' : g / L.block / 2 = h1 / L.block / 2 := by omega
    have htr1 : X.tr h1 ≠ [] :=
      ht.cluster_started hg hget hc' hh1 (hcl_of h1 hcl'.symm)
    have hstate' : stateBefore (X.objects (Bar.loc L (h1 / L.block +
        (⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2).val)
          ⟨.acc, (⟨g % L.block / 32 / 4, hw2⟩ : Fin 2).val, true⟩))
        (X.objects (Bar.loc L (h1 / L.block +
          (⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2).val)
            ⟨.acc, (⟨g % L.block / 32 / 4, hw2⟩ : Fin 2).val, true⟩)).length = some before := by
      have e : h1 / L.block + g / L.block % 2 = g / L.block := by omega
      simp only [e]
      exact hstate
    have hNT := commits_le_phase hpre hX ht hX.tma.2.2.1 (j := ⟨g % L.block / 32 / 4, hw2⟩)
      (acc_targets hX ht) hall hh1 hl1 hstate'
    rw [hT'] at hNT
    have hst := ht.mma_elect_state hh1 hl1 hw1 hel1'
    rcases hst with hnone | ⟨m, hm⟩
    · -- the lane stopped: finished (with its exit) or pending without one
      by_cases hex : ∃ pc', (X.tr h1).getLast? = some ⟨pc', .exit⟩
      · obtain ⟨pc', hlast'⟩ := hex
        have hN := ht.mma_exit_acc hh1 hw1 hlast'
        rcases ht.mma_leader hh1 hl1 hw1 hel1' with ⟨m', hm', -⟩ |
          ⟨hfin, j', pcj, pj, acqj, scj, pcr, src, bs, rr, hcnt, hgj, hread, hsf, hrr, hnc⟩ |
          ⟨-, hnex⟩
        · rw [hnone] at hm'
          cases hm'
        · exfalso
          have hidx : h1 % L.block / 32 % 2 = g % L.block / 32 / 4 := by omega
          rw [hidx] at hN
          exact finished_false hpre hX ht hv hcl' hTg
            ⟨j', pcj, pj, acqj, scj, pcr, src, bs, rr, hcnt, hgj, hread, hsf, hrr, hnc⟩ hfin hN hNT
        · exact absurd hlast' (hnex pc')
      · push Not at hex
        exact Or.inr (Or.inr ⟨h1, hh1, hh1c, hh1w, htr1, hnone, hex⟩)
    · by_cases hx : Mma.exitOff m = none
      · -- a working lane: its accumulator commits are at most its phase, so its rank is bounded
        have hne1 : ∀ pc', (X.tr h1).getLast? ≠ some ⟨pc', .exit⟩ := by
          intro pc' hlast'
          rw [ht.exited_state hh1 hlast'] at hm
          cases hm
        refine Or.inr (Or.inl ⟨h1, hh1, hh1c, hh1w, htr1, hne1, .inr (.mma m), hm, hx, ?_⟩)
        have hacc := (ht.mma_acc_count hh1 (fun k pc' f => hub h1 k pc' f) hm).1
        have hmw : m.w = h1 % L.block / 32 := by
          have hrw := ht.role_warp hh1 (le_refl _) hm
          simp only [roleWarp] at hrw
          exact hrw.1
        have hidx : m.w % 2 = g % L.block / 32 / 4 := by omega
        rw [hidx] at hacc
        have hvt := mma_vtime_le hacc hx
        have hNT' : (X.tr h1).countP
            (commitsTo (Bar.loc L (h1 / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩)) ≤
            consCount L g (X.tr g) := hNT
        have hmono : blockAt ((X.tr h1).countP
            (commitsTo (Bar.loc L (h1 / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩))) ≤
            blockAt (consCount L g (X.tr g)) := by
          unfold blockAt blockSpan
          omega
        show Mma.vtime _ m ≤ _
        omega
      · -- an exit-stage lane: it finished, and contradicts the consumer's blocked tile
        rcases ht.mma_leader hh1 hl1 hw1 hel1' with ⟨m', hm', hx', -⟩ |
          ⟨hfin, j', pcj, pj, acqj, scj, pcr, src, bs, rr, hcnt, hgj, hread, hsf, hrr, hnc⟩ |
          ⟨hnone', -⟩
        · rw [hm] at hm'
          cases hm'
          exact absurd hx' hx
        · exfalso
          have hN0 := finished_acc_count ht hh1 (fun k pc' f => hub h1 k pc' f) hm hx hfin
          have hidx : m.w % 2 = g % L.block / 32 / 4 := by
            have hrw := ht.role_warp hh1 (le_refl _) hm
            simp only [roleWarp] at hrw
            omega
          rw [hidx] at hN0
          have hN := hN0.trans (mmaCount_div_eq L h1 (X.tr h1) hfin).symm
          exact finished_false hpre hX ht hv hcl' hTg
            ⟨j', pcj, pj, acqj, scj, pcr, src, bs, rr, hcnt, hgj, hread, hsf, hrr, hnc⟩ hfin hN hNT
        · rw [hm] at hnone'
          cases hnone'

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
