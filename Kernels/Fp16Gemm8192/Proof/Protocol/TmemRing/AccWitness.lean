-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Blocker
public import Kernels.Fp16Gemm8192.Proof.Protocol.Exit.ClusterAll

@[expose] public section

/-! # The accumulator-empty witness of an MMA leader's failed poll

`acc_blocker` gives a consumer of the buffer that has arrived as many times as the barrier's
phase. Here that consumer is shown to be a thread of the cluster, in the buffer's warp group,
outside its exit stage and not exited (`accEmptyWitness`, the per-execution statement
`AccEmptyWitness`). The exit-stage case is excluded by the claimless response a consumer reads
there (`cons_exit_read`): its response poll count equals its arrivals, and the MMA leader, which
reads the same responses (`AllResponsesAgree`) and claims each of them (`MmaWorkingClaims`), cannot
have read that response. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A successful poll's ordinal: the `r`-th successful poll of `m` (counting from zero) is an event
of the trace, and the successful polls before it are `r`. -/
theorem okPolls_ordinal {m : Loc} (es : List Event) {r : Nat} (hr : r < okPolls m es) :
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

/-- The successful polls of a prefix one event longer: one more when the event is a successful
poll. -/
theorem okPolls_take_succ {m : Loc} (es : List Event) {j : Nat} {e : Event}
    (hj : es[j]? = some e) :
    okPolls m (es.take (j + 1)) = okPolls m (es.take j) + (if okPoll m e then 1 else 0) := by
  rw [List.take_add_one, hj]
  exact okPolls_snoc m _ e

/-- The successful polls of a prefix are at most those of the whole trace. -/
theorem okPolls_take_le {m : Loc} (es : List Event) (k : Nat) :
    okPolls m (es.take k) ≤ okPolls m es := by
  have h := congrArg (okPolls m) (List.take_append_drop k es)
  unfold okPolls at h ⊢
  rw [List.countP_append] at h
  omega

/-- A consumer in an exit-stage site has no tile open, and holds no accumulator. -/
theorem exit_counts {c : Consumer.D} (hx : Consumer.exitOff c ≠ none) :
    Consumer.tileOpen c = 0 ∧ Consumer.holds c = 0 := by
  unfold Consumer.exitOff at hx
  unfold Consumer.tileOpen Consumer.holds
  cases hs : c.site <;> simp_all

/-- **A consumer in its exit stage is not the blocker.** Its response polls are its arrivals,
which are the barrier's phase, while the MMA leader, which is at its accumulator-empty wait with
one more response poll than its phase, reads the response the consumer reads claimless, and claims
every response it reads. -/
theorem exit_excluded {L : Launch} {X : Execution}
    (ht : ThreadFacts L X) (hub : ¬ HasUb X) (hagree : AllResponsesAgree L X)
    (hcl : MmaWorkingClaims L X) {g : Nat} {mm : Mma.D} (hg : g < L.threads)
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma mm))))
    (hs : mm.site = .accWait) (hlead : g / L.block % 2 = 0)
    {h : Nat} {c : Consumer.D} (hh : h < L.threads) (hsame : h / L.block / 2 = g / L.block / 2)
    (hwg : h % L.block / 32 / 4 = mm.w % 2) {before : Nat}
    (hP : arrivals (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩) (X.tr h) = before)
    (hPg : before + 1 = okPolls (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩) (X.tr g))
    (hσh : Frame.stateAt (code L) X h (X.tr h).length = some (some (.inr (.cons c))))
    (hx : Consumer.exitOff c ≠ none) : False := by
  have hub' : ∀ k pc f, X.get (h, k) ≠ some ⟨pc, .ub f⟩ :=
    fun k pc f hk => hub ⟨(h, k), pc, f, hk⟩
  have hgg : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩ :=
    fun k pc f hk => hub ⟨(g, k), pc, f, hk⟩
  -- the consumer's counts at its exit stage: its response polls are its arrivals
  have hcons := ht.cons_tiles hh hub' hσh
  have hcount := ht.cons_acc_count hh hσh
  have hloc : Bar.loc L (2 * (h / L.block / 2)) ⟨.acc, Consumer.tidOf L h / 32 / 4, false⟩ =
      Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩ := by
    have h1 : 2 * (h / L.block / 2) = g / L.block := by omega
    have h2 : Consumer.tidOf L h / 32 / 4 = mm.w % 2 := hwg
    rw [h1, h2]
  obtain ⟨hx1, hx2⟩ := exit_counts hx
  rw [hcount, hloc, hP] at hcons
  have hokh : okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) = before := by
    omega
  -- the consumer's claimless read, after its `j`-th successful response poll
  obtain ⟨j, pc, p, acq, sc, pcr, src, bs, rr, hwj, hrj, hsf, hresp, hcl2⟩ :=
    ht.cons_exit_read hh hσh hx
  have hpoll_j : okPoll (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩)
      ⟨pc, .wait (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ = true := by
    simp [okPoll, sourceWaitSuccess]
  have hjk := okPolls_take_succ (m := Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) hwj
  have hjk' : okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) ((X.tr h).take (j + 1)) =
      okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) ((X.tr h).take j) + 1 := by
    rw [hjk, hpoll_j]
    simp
  have hle := okPolls_take_le (m := Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) (X.tr h) (j + 1)
  -- the MMA leader's response polls: one more than its phase, and one more after its claims
  have hmc := ht.mma_acc_count hg hgg hσg
  have hmc2 := hmc.2
  simp [hs] at hmc2
  have hcl' := hcl g mm hg hσg hs
  have hgo : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) = before + 2 := by
    rw [hcl'.2]
    omega
  have hr_lt : okPolls (Bar.loc L (h / L.block) ⟨.clc, 0, true⟩) ((X.tr h).take j) <
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
    omega
  -- the MMA leader's successful response poll with the same ordinal
  obtain ⟨jm, e, hjm, hokm, hordm⟩ :=
    okPolls_ordinal (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) hr_lt
  obtain ⟨pcm, km⟩ := e
  obtain ⟨pm, acqm, scm, hkm⟩ := okPoll_wait_form hokm
  dsimp only at hkm
  subst hkm
  -- this poll is not the MMA leader's latest: the consumer's poll before its read is below the
  -- phase
  have hcnt : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take jm) + 1 <
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
    omega
  obtain ⟨pcr2, src2, bs2, rr2, hrd2, hsf2, hresp2, hclaim2⟩ :=
    hcl'.1 jm pcm pm acqm scm hjm hcnt
  have hbs := hagree (g / L.block / 2) h g j jm pc pcm p pm pcr pcr2 acq acqm sc scm src src2 bs bs2
    hsame rfl hwj hjm hordm.symm hrj hsf hrd2 hsf2
  have hrr : rr = rr2 := by
    have h3 : Flow.responseOf bs2 = some rr := by
      rw [← hbs]
      exact hresp
    exact Option.some.inj (h3.symm.trans hresp2)
  exact hcl2 (by rw [hrr]; exact hclaim2)

/-- **The accumulator-empty witness.** At a failed poll of an MMA leader's accumulator-empty
barrier whose phase is not ready for its parity, the MMA thread has polled successfully once more
than the barrier's phase; and a consumer of its cluster in the buffer's warp group has arrived on
the barrier as many times as the phase, and has not exited nor entered its exit stage. -/
theorem accEmptyWitness {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hub : ¬ HasUb X) (hagree : AllResponsesAgree L X) (hcl : MmaWorkingClaims L X) :
    AccEmptyWitness L X := by
  intro g mm pc sc before hg hlead hσg hs hlast hstate hpar
  have hexit := clusterExitAll hpre hX ht
  -- the MMA thread's warp is warp 8 or 9 of its CTA
  have hwarp := ht.role_warp hg (le_refl _) hσg
  simp only [roleWarp] at hwarp
  obtain ⟨hwmm, hwr⟩ := hwarp
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he] at hlast
    simp at hlast
  have hget : X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩) mm.ap false true sc⟩ := by
    change (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  -- the state before the failed poll is a state of the thread (not undefined behaviour)
  obtain ⟨d, hd⟩ : ∃ d, Frame.stateAt (code L) X g ((X.tr g).length - 1) = some (some d) := by
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget nofun
    exact ⟨d, hσ⟩
  have hj : mm.w % 2 < 2 := Nat.mod_lt _ (by decide)
  have hc : g / L.block = 2 * (g / L.block / 2) := by omega
  have hw : g % L.block / 32 = 8 + mm.w % 2 := by omega
  obtain ⟨hT, b, hbarr⟩ :=
    TmemRing.acc_blocker hpre hX ht hg (j := ⟨mm.w % 2, hj⟩) hc hw hd hlast hstate hpar
  have hT' : before.phase + 1 = okPolls (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩)
    (X.tr g) :=
    hT
  -- the consumer `k` of the buffer, in the leader's cluster and the buffer's warp group
  have hb256 : 256 ≤ L.block := by
    rw [hpre.block]
    norm_num
  have hblock : 0 < L.block := by omega
  have hdiv := TmemRing.consumerOf_div hb256 (g / L.block / 2) ⟨mm.w % 2, hj⟩ b
  have hmod := TmemRing.consumerOf_mod hb256 (g / L.block / 2) ⟨mm.w % 2, hj⟩ b
  generalize TmemRing.consumerOf L (g / L.block / 2) ⟨mm.w % 2, hj⟩ b = k at hdiv hmod hbarr
  have hdiv' : k / L.block = 2 * (g / L.block / 2) + b.val / 128 := hdiv
  have hmod' : k % L.block = 128 * (mm.w % 2) + b.val % 128 := hmod
  have hbarr' : Flow.arrivals (Bar.loc L (g / L.block) ⟨.acc, mm.w % 2, false⟩) (X.tr k) =
      before.phase := hbarr
  have hb1 := b.isLt
  have hgrid : g / L.block < L.grid := by
    have : g < L.grid * L.block := hg
    rw [Nat.div_lt_iff_lt_mul hblock]
    exact this
  rw [hpre.grid] at hgrid
  have hkd : k / L.block < L.grid := by
    rw [hdiv', hpre.grid]
    omega
  have hk : k < L.threads := (Nat.div_lt_iff_lt_mul hblock).mp hkd
  have hsame : k / L.block / 2 = g / L.block / 2 := by
    rw [hdiv']
    omega
  have hwg : k % L.block / 32 / 4 = mm.w % 2 := by
    rw [hmod']
    omega
  have hk32 : k % L.block / 32 < 8 := by
    rw [hmod']
    omega
  -- the consumer has not exited: its exit would make its cluster's arrivals two, while the
  -- MMA thread's are its phase one
  have hnx : ∀ pc', (X.tr k).getLast? ≠ some ⟨pc', .exit⟩ := by
    intro pc' hx
    have h2 := hexit k pc' hk hx g hg (by
      rw [clusterOfCta_eq hpre, clusterOfCta_eq hpre]
      omega)
    have h1 := ht.cl_phase hg hσg
    simp [ThreadD.clPhase, hs] at h1
    omega
  -- the consumer is outside its exit stage: a consumer in its exit stage is excluded
  have hexo : ∀ d', Frame.stateAt (code L) X k (X.tr k).length = some (some d') → d'.exitOff =
    none := by
    intro d' hd'
    cases d' with
    | inl p => rfl
    | inr r =>
      have hrw := ht.role_warp hk (le_refl _) hd'
      cases r with
      | loader l =>
        simp only [roleWarp] at hrw
        exact absurd hrw (by omega)
      | mma m' =>
        simp only [roleWarp] at hrw
        exact absurd hrw.2 (by omega)
      | sched s =>
        simp only [roleWarp] at hrw
        exact absurd hrw (by omega)
      | cons c =>
        by_contra hne'
        exact exit_excluded ht hub hagree hcl hg hσg hs hlead hk hsame hwg hbarr' hT' hd' hne'
  exact ⟨hT', k, hk, hsame, hwg, hbarr', hnx, hexo⟩

end

end PTX.Kernels.Fp16Gemm8192.Proof
