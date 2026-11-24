-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetimeLoads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetimeGemm
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreReleaseTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaGemmTrace
import Lemmas.Flow.NthEv

public section

/-! # Shared lifetime, including an unobserved PV notification -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime

open PTX PTX.Flow PTX.AsyncCopy Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
include hpre hX hs

private theorem earlier_pv_issue {g i j : Nat} {s : TcCommit.Spec} {d q : Wg1Mma.D}
    (hi : X.Commit (g, i) s) (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.mma q))) (hLess : d.i < q.i)
    : i < j := by
  have hg := Frame.lt_of_get hX hi.choose_spec
  let tr := (hs g hg).machine.produces (hX.thr g hg)
  let slot := rawSlot d.i
  let tick := Wg1MmaGemmTrace.Stream.pv.tick L g slot
  have hdCount := Wg1MmaGemmTrace.pv_commits_before_block hpre hg slot tr hd
  have hqCount := Wg1MmaGemmTrace.pv_commits_before_block hpre hg slot tr hq
  by_contra hn
  have hm := countP_take_mono tick (X.tr g) (show j ≤ i by omega)
  change ((X.tr g).take j).countP tick ≤ ((X.tr g).take i).countP tick at hm
  rw [hqCount, hdCount] at hm
  change (q.i + (1 - d.i % 2)) / 2 ≤ (d.i + (1 - d.i % 2)) / 2 at hm
  omega

omit hpre hX hs in
/-- The predecessor order extends the existing barrier path to the same exiting thread. -/
private theorem record_exit_order_of_commit_next {g i j : Nat} {rank : Fin 16}
    (hX : Consistent L kernel Assumptions.all mem0 X) {tag : Nat} {sp : TcCommit.Spec}
    (he : X.get (g, i) = some ⟨tag, .tc (.commit sp)⟩)
    (hs : Assumptions.all.any (·.commitInOrder tag) = true)
    (hij : i < j) (hj : ∃ sp', X.Commit (g, j) sp')
    (hBetween : ∀ k, i < k → k < j → ¬ ∃ sp', X.Commit (g, k) sp')
    (hNext : RecordExitOrder L X (.async (g, j) (.tcNotify rank)) (ctaOf L g)) :
    RecordExitOrder L X (.async (g, i) (.tcNotify rank)) (ctaOf L g) := by
  obtain ⟨hp, finish, m, hf, hPath⟩ := hNext
  have hw := hX.asm Assumptions.commitOrder (by simp [Assumptions.all])
  have hSite := hs
  rw [Assumptions.all_commitInOrder] at hSite
  have hPrev : X.RefPresent (.async (g, i) (.tcNotify rank)) :=
    hw g i j tag sp rank he hSite hij hj hBetween hp
  have hEdge : CommitNext Assumptions.all X (.async (g, i) (.tcNotify rank))
      (.async (g, j) (.tcNotify rank)) :=
    ⟨rfl, rfl, hij, hPrev, hp, ⟨tag, sp, he, hs⟩, hj, hBetween⟩
  exact ⟨hPrev, finish, m, hf, .head (.inr (.inr ⟨rfl, rfl, .inl hEdge⟩))
    (.head (.inl (DepStep.node (L := L) hp)) hPath)⟩

/-- All earlier commits of the MMA lane have an exit path. Directly observed query and QK
notifications close their own paths. A PV notification can inherit the next commit's path. -/
private theorem commit_exit_order_through_final (ht : Frame.Tracked (Machine.code P L) X)
    {g last : Nat} (hx : CtaExited L X (ctaOf L g)) (hLast : ∃ sp, X.Commit (g, last) sp)
    (hFinal : RecordExitOrder L X (.async (g, last) (.tcNotify 0)) (ctaOf L g)) :
    ∀ i ≤ last, (∃ sp, X.Commit (g, i) sp) →
      RecordExitOrder L X (.async (g, i) (.tcNotify 0)) (ctaOf L g) := by
  classical
  have go (n : Nat) : ∀ i ≤ last, last - i = n → (∃ sp, X.Commit (g, i) sp) →
      RecordExitOrder L X (.async (g, i) (.tcNotify 0)) (ctaOf L g) := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hLe hDist hCommit
      rcases Nat.eq_or_lt_of_le hLe with rfl | hlt
      · exact hFinal
      obtain ⟨sp, he⟩ := hCommit
      have hg := Frame.lt_of_get hX he.choose_spec
      obtain ⟨role, _, hState, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hg).machine ht
        he.choose_spec (by simp)
      have hSite := RingCommitEvents.commit_site hf rfl
      cases role <;> try exact hSite.elim
      rename_i d
      obtain ⟨sp', hk, _, hTargets⟩ := RingCommitEvents.commit_issue hpre hg hSite hf
      have heq : sp = sp' := TcKind.commit.inj (Kind.tc.inj hk)
      subst sp'
      have hTarget : TcCommit.target sp 0 = some sp.mbar := by rw [hTargets]; rfl
      rcases hSite with hQuery | hQk | hPv
      · exact query_commit_exit_order hpre hX hs ht he hState hQuery hTarget hx
      · exact qk_commit_exit_order hpre hX hs ht he hState hQk hTarget hx
      have hExists : ∃ j, i < j ∧ ∃ sp, X.Commit (g, j) sp := ⟨last, hlt, hLast⟩
      let j := Nat.find hExists
      have hJ := Nat.find_spec hExists
      have hjl : j ≤ last := Nat.find_min' hExists ⟨hlt, hLast⟩
      have hBetween (k : Nat) (hik : i < k) (hkj : k < j) :
          ¬ ∃ sp, X.Commit (g, k) sp :=
        fun h => Nat.find_min hExists hkj ⟨hik, h⟩
      have hIJ : i < j := hJ.1
      have hNext := ih (last - j) (by omega) j hjl rfl hJ.2
      exact record_exit_order_of_commit_next hX he.choose_spec
        (RingCommitEvents.pv_commit_order_selected hf hPv) hJ.1 hJ.2 hBetween hNext
  exact fun i hi hc => go (last - i) i hi rfl hc

private theorem penultimate_pv_finished (ht : Frame.Tracked (Machine.code P L) X) {g i : Nat}
    {d : Wg1Mma.D} {sp : TcCommit.Spec} {m : Loc} {rank : Fin 16} (hi : X.Commit (g, i) sp)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hSite : d.site = .pvCommit) (hTarget : TcCommit.target sp rank = some m)
    (hPenultimate : d.i + 2 = Wg1Mma.blocks P L g) (hx : CtaExited L X (ctaOf L g)) :
    SharedFinished L kernel Assumptions.all X (.async (g, i) (.tcNotify rank)) (ctaOf L g) := by
  have hg := Frame.lt_of_get hX hi.choose_spec
  obtain ⟨_, hf⟩ := ((hs g hg).machine.produces (hX.thr g hg)).fired_at hi.choose_spec hd
  obtain ⟨sp', hk, _, hRanks⟩ := RingCommitEvents.commit_issue hpre hg (.inr (.inr hSite)) hf
  have hEqual : sp = sp' := TcKind.commit.inj (Kind.tc.inj hk)
  subst sp'
  have hrank : rank = 0 := by
    rw [hRanks] at hTarget
    split at hTarget
    · assumption
    · cases hTarget
  subst rank
  obtain ⟨owner, release, _, hCta, hDealloc⟩ :=
    dealloc_of_cta_exited hpre hX hs ht (NamedBar.cta_lt hg) hx
  obtain ⟨closing, _, tail, _, hBar, hTail, hClose⟩ :=
    ScoreReleaseTrace.barrier_before_dealloc hpre hX hs ht hDealloc
  obtain ⟨issuer, hIssuer⟩ :=
    GemmRing.exists_issuer (cta := ctaOf L owner) hpre hX (fun t ht' => (hs t ht').machine)
  have hgEq := hIssuer g i d hCta.symm hd (by simp [hSite])
  subst issuer
  obtain ⟨_, _, last, tag, _, spec, r, q, _, _, hLast, hTarget', _, hPv, hIdx, hQ, _, _⟩ :=
    StageAfterPv.final_commit_before_closing hpre hX hs ht hIssuer hBar hTail hClose
  have hOwner := Frame.lt_of_get hX hBar
  obtain ⟨_, hfClose⟩ :=
    ((hs owner hOwner).machine.produces (hX.thr owner hOwner)).fired_at hBar hTail
  have hInv : Wg0.Inv P L owner tail := hfClose.choose_spec.1.2
  have hFinal := hInv.epilogueLast (by rw [hClose]; rfl)
  rw [← StageAfterPv.block_count_eq (P := P) hCta.symm, ← hIdx] at hFinal
  have hBefore := earlier_pv_issue hpre hX hs hi hd hQ (by omega)
  have hFinalIssue : X.Commit (g, last) spec := ⟨tag, hLast⟩
  have hG := Frame.lt_of_get hX hLast
  obtain ⟨_, hF⟩ := ((hs g hG).machine.produces (hX.thr g hG)).fired_at hLast hQ
  obtain ⟨spec', hs', _, hr'⟩ := RingCommitEvents.commit_issue hpre hG (.inr (.inr hPv)) hF
  have hEqual' : spec = spec' := TcKind.commit.inj (Kind.tc.inj hs')
  subst spec'
  have hRank : r = 0 := by
    rw [hr'] at hTarget'
    split at hTarget'
    · assumption
    · cases hTarget'
  subst r
  have hExit := final_pv_commit_exit_order hpre hX hs ht hFinalIssue hQ hPv hTarget' hFinal hx
  exact (commit_exit_order_through_final hpre hX hs ht hx ⟨_, hFinalIssue⟩ hExit
    i hBefore.le ⟨_, hi⟩).finished

private theorem commit_finished (ht : Frame.Tracked (Machine.code P L) X) :
    CommitFinished L X := by
  rintro ⟨g, i⟩ sp rank m hi hTarget hx
  have hg := Frame.lt_of_get hX hi.choose_spec
  obtain ⟨role, _, hState, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hg).machine ht
    hi.choose_spec (by simp)
  obtain ⟨_, d, rfl, hSite⟩ := RingCommitEvents.commit_source hpre hg hf rfl hTarget
  rcases hSite with ⟨hSite, _⟩ | ⟨hSite, _⟩ | ⟨hSite, _⟩
  · exact query_commit_finished hpre hX hs ht hi hState hSite hTarget hx
  · exact qk_commit_finished hpre hX hs ht hi hState hSite hTarget hx
  · have hInv : Wg1Mma.Inv P L g d := hf.choose_spec.1.2
    have hBound := hInv.i_lt (by rw [hSite]; trivial)
    by_cases hLast : d.i + 1 = Wg1Mma.blocks P L g
    · exact final_pv_commit_finished hpre hX hs ht hi hState hSite hTarget hLast hx
    by_cases hAlmost : d.i + 2 = Wg1Mma.blocks P L g
    · exact penultimate_pv_finished hpre hX hs ht hi hState hSite hTarget hAlmost hx
    · exact reused_pv_commit_finished hpre hX hs ht hi hState hSite hTarget (by omega) hx

/-- Every use of shared storage is inside the owning CTA's lifetime. -/
theorem no_sharedLifetimeUnsafe (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ SharedLifetimeUnsafe L kernel Assumptions.all X :=
  no_unsafe_of_completions hpre hX hs ht (loads_notified hpre hX hs ht)
    (mma_finished hpre hX hs ht) (commit_finished hpre hX hs ht)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime
