-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeCopy
public import Lemmas.Kernel.CommitNextExit

@[expose] public section

/-!
# A commit's arrive-on finishes before its CTA exits

`Life.CommitFinished` (`IpLifeUse`): every arrive-on of a `tcgen05.commit` completes before an
exit of the target barrier's CTA, which is the commit's own CTA (`Own.mbar`) and rank 0 (every
commit of the kernel is the MMA warp's with `commitSpec`: one CTA group, the thread's own CTA).
The MMA warp has four commit sites (`Mma.Site`): `s_ready (i % 2)` (`qkCommit`), `kv_empty`
(`pvCommit1`), `o_done` (`pvCommit2`) and `o_final` (`finCommit`). The commit-order assumption
selects the two middle ones (`Assumptions.commitOrderSites`: `sel_iff`).

* **`o_final`** (`final_good`): observed by the epilogue's poll of `o_final` in lane 0 of warp 0,
  which every exited default-partition thread made before its exit (`exit_poll`, the second kernel
  fix); the poll with no earlier poll observes the commit with no earlier commit, which is this
  commit (`Tmem1.OFinalFacts`).
* **`s_ready`**: observed by a softmax thread's poll: the premise `SObserved`.
* **`kv_empty`, `o_done`** (`good_all`): not observed by every commit (the last three `kv_empty`
  commits and the last `o_done` commit have no waiter), so each is chained through
  `Assumptions.commitOrder` to the thread's next commit (`CommitNext`), with its arrive-on
  performed whenever the next one is (`selectedPerformed`, the assumption's `wf`); the chain ends
  at an observed commit (`s_ready` of the next iteration or `o_final`). The existence of the next
  commit of the same thread is the premise `NextCommit`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Life
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady oFinal commitSpec MmShape QkIssue PvIssue)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The commit-order assumption -/

/-- **The sites the assumptions select with `commitInOrder` are `commitOrderSites`.** -/
theorem sel_iff (pc : Nat) :
    (Assumptions.all.any (·.commitInOrder pc)) = true ↔
      Assumptions.commitOrderSites.contains pc = true := by
  have h : ∀ a ∈ Assumptions.all, a ≠ Assumptions.commitOrder → a.commitInOrder pc = false := by
    intro a ha hne
    simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | rfl
  constructor
  · intro hs
    obtain ⟨a, ha, hc⟩ := List.any_eq_true.mp hs
    by_cases hne : a = Assumptions.commitOrder
    · subst hne
      exact hc
    · rw [h a ha hne] at hc
      cases hc
  · intro hc
    exact List.any_eq_true.mpr ⟨Assumptions.commitOrder, by simp [Assumptions.all], hc⟩

/-- **The arrive-on of a selected commit is performed whenever the next one's is** (the
assumption's constraint, `Assumption.commitPerformedAt`). -/
theorem selectedPerformed (hX : Consistent L kernel asms mem0 X) {g j j' pc : Nat}
    {sp : TcCommit.Spec} {r : Fin 16} (he : X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩)
    (hs : Assumptions.commitOrderSites.contains pc = true) (hjj : j < j')
    (hc : ∃ s, X.Commit (g, j') s) (hk : ∀ k, j < k → k < j' → ¬ ∃ s, X.Commit (g, k) s)
    (hr : r ∈ X.tcNotified (g, j')) : r ∈ X.tcNotified (g, j) := by
  have hw := hX.asm Assumptions.commitOrder (by simp [asms, Assumptions.all])
  exact hw g j j' pc sp r he hs hjj hc hk hr

/-! ### The commits of the MMA warp -/

/-- The target of a `commitSpec` is its barrier at rank 0 and nothing else. -/
theorem target_commitSpec {c : Nat} {l m : Loc} {r : Fin 16}
    (h : TcCommit.target (commitSpec c l) r = some m) : r.val = 0 ∧ m = ⟨.shared, c, l.addr⟩ := by
  unfold TcCommit.target at h
  split at h
  · rename_i hr
    simp only [commitSpec, Option.some.injEq] at h hr
    have hr0 : r.val = 0 := by omega
    refine ⟨hr0, ?_⟩
    rw [← h, hr0]
    rfl
  · cases h

theorem target_commitSpec_zero (c : Nat) (l : Loc) :
    TcCommit.target (commitSpec c l) ⟨0, by omega⟩ = some ⟨.shared, c, l.addr⟩ := by
  simp [TcCommit.target, commitSpec]

/-- **The four kinds of commit**: a commit of the kernel is the MMA warp's, to `s_ready`, to
`o_final`, or at a site the commit-order assumption selects (`kv_empty`, `o_done`). -/
theorem commit_class (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc : Nat} {s : TcCommit.Spec}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit s)⟩) :
    ((∃ b, b < 2 ∧ s = commitSpec (g / L.block) (sReady L (g / L.block) b)) ∧
        Assumptions.commitOrderSites.contains pc = false) ∨
      (s = commitSpec (g / L.block) (oFinal L (g / L.block)) ∧
        Assumptions.commitOrderSites.contains pc = false) ∨
      (Assumptions.commitOrderSites.contains pc = true ∧ ∃ l, s = commitSpec (g / L.block) l) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, P, -, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he (.inr ⟨s, rfl⟩)
  unfold MmShape at hsh
  cases hs : d.site <;> simp only [hs] at hsh
  all_goals first
    | (simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
       obtain ⟨rfl, rfl⟩ := hsh
       first
         | (left; exact ⟨⟨_, Nat.mod_lt _ (by omega), rfl⟩, by decide⟩)
         | (right; left; exact ⟨rfl, by decide⟩)
         | (right; right; exact ⟨by decide, _, rfl⟩))
    | (exfalso; simp [QkIssue, PvIssue] at hsh)

/-! ### Finished chains -/

/-- The arrive-on of commit `(g, k)` at rank `r` has an observation chain to an exit of CTA `c`. -/
def Good (L : Launch) (X : Execution) (c g k : Nat) (r : Fin 16) : Prop :=
  ∃ finish, OwnerExit L X c finish ∧ X.AsyncPresent (g, k) (.tcNotify r) ∧
    EnabledBefore L kernel asms X (.async (g, k) (.tcNotify r)) (.thread finish, false)

theorem Good.finished {c g k : Nat} {r : Fin 16} (h : Good L X c g k r) :
    SharedFinished L kernel asms X (.async (g, k) (.tcNotify r)) c := by
  obtain ⟨finish, hx, hp, hb⟩ := h
  exact SharedFinished.of_completedBefore hp hx hb.completedBefore

/-- **A commit observed by a poll of a thread of the CTA that exits later has a chain.** -/
theorem Good.of_observed (hX : Consistent L kernel asms mem0 X) {c g k h j : Nat} {r : Fin 16}
    {m : Loc} {acq : Bool} {ws : MbarScope} (hx : CtaExited L X c)
    (hp : X.AsyncPresent (g, k) (.tcNotify r))
    (hwo : WaitObserves X (.async (g, k) (.tcNotify r)) (h, j) m acq ws) (hh : h < L.threads)
    (hhc : h / L.block = c) : Good L X c g k r := by
  obtain ⟨pcw, q, hget⟩ := hwo.1
  obtain ⟨kx, pcx, hk, hlt⟩ := exit_after_poll hx hh hhc hget (fun _ h => by cases h)
  obtain ⟨ex, hsp⟩ := poll_spins hX hget
  have hobs : Witness L X (.async (g, k) (.tcNotify r)) (h, j) :=
    Witness.of_mbarObserved (mbarObserved_of_waitObserves hX.tma.2.2.1 hp hwo)
  have hres : Resumes kernel X (h, j) (h, kx) := Resumes.of_spin hget hsp rfl hlt (len_of_get hk)
  exact ⟨(h, kx), ⟨hh, hhc, pcx, hk⟩, hp,
    EnabledBefore.of_observed hobs (.single (DepStep.of_resumes L hres))⟩

/-- **A commit chained to the thread's next commit** (`CommitNext`) has the next one's chain. -/
theorem Good.of_next (hX : Consistent L kernel asms mem0 X) {c g k k' pc : Nat}
    {sp : TcCommit.Spec} {r : Fin 16} (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (hs : Assumptions.commitOrderSites.contains pc = true) (hkk : k < k')
    (hc : ∃ s, X.Commit (g, k') s) (hmin : ∀ q, k < q → q < k' → ¬ ∃ s, X.Commit (g, q) s)
    (hg : Good L X c g k' r) : Good L X c g k r := by
  obtain ⟨finish, hx, hp, hb⟩ := hg
  have hp0 : X.AsyncPresent (g, k) (.tcNotify r) := selectedPerformed hX he hs hkk hc hmin hp
  have hn : CommitNext asms X (.async (g, k) (.tcNotify r)) (.async (g, k') (.tcNotify r)) := by
    refine ⟨rfl, rfl, hkk, hp0, hp, ⟨pc, sp, he, (sel_iff pc).mpr hs⟩, hc, hmin⟩
  refine ⟨finish, hx, hp0, ?_⟩
  rcases hb with ⟨o, ho, h⟩ | ⟨i, p, w, o, he', hobs, ho, h⟩
  · have hpr : X.RefPresent (.async (g, k') (.tcNotify r)) := hp
    exact .inl ⟨o, ho, .head (Or.inr (Or.inr ⟨rfl, rfl, .inl hn⟩))
      (.head (Or.inl (DepStep.node (L := L) hpr)) h)⟩
  · cases he'
    exact .inl ⟨o, ho, .head (Or.inr (Or.inr ⟨rfl, rfl, .inl hn⟩))
      (.head (Or.inl (DepStep.of_witness L hobs)) h)⟩

/-- **The commit to `o_final` has a chain**: the epilogue's poll in lane 0 of warp 0. -/
theorem final_good (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (F : ∀ c < L.grid, Tmem1.OFinalFacts L X c)
    {g k pc : Nat}
    {sp : TcCommit.Spec} {r : Fin 16} {m : Loc}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩) (htg : TcCommit.target sp r = some m)
    (hsp : sp = commitSpec (g / L.block) (oFinal L (g / L.block)))
    (hx : CtaExited L X (g / L.block)) : Good L X (g / L.block) g k r := by
  have hg := Frame.lt_of_get hX he
  set c := g / L.block with hc
  have hcl : c < L.grid := cta_lt_grid hpre hg
  obtain ⟨cm, p0, Fa, hcm, hcmc, hone, hcommit, hbefore⟩ := F c hcl
  have hmo : m = oFinal L c := by
    obtain ⟨-, hm⟩ := target_commitSpec (hsp ▸ htg)
    rw [hm]
    rfl
  have hb : L.block = 256 := hpre.block
  have hh : c * L.block < L.threads := by
    unfold Launch.threads
    exact Nat.mul_lt_mul_of_pos_right hcl (by omega)
  have hhc : c * L.block / L.block = c := Nat.mul_div_cancel c (by omega)
  have hhd : c * L.block % L.block < 128 := by rw [Nat.mul_mod_left]; omega
  obtain ⟨pcl, hl⟩ := hx (c * L.block) hh hhc
  rw [List.getLast?_eq_getElem?] at hl
  have hkh : X.get (c * L.block, (X.tr (c * L.block)).length - 1) = some ⟨pcl, .exit⟩ := hl
  obtain ⟨j, hjk, pc', p, sc, hget⟩ := exit_poll hpre hX hf hkh hhd
  rw [hhc] at hget
  have hq : okPolls (oFinal L c) ((X.tr (c * L.block)).take j) + 0 =
      okPolls (oFinal L c) ((X.tr (c * L.block)).take j) := rfl
  obtain ⟨i', pcx, sp', rank', hget', hmbar', htgt', hcnt', hrank', hobs⟩ :=
    (SO.fObj hX Fa).observes hX (SO.fReach hX Fa (c * L.block) hcommit) hget hq
  -- the commit is `cm`'s first commit to `o_final`, like the observed one
  have hcb : SO.CommitBar L c (oFinal L c) := SO.CommitBar.oFinal
  obtain ⟨hgcm, hmb⟩ := Fa.commit_only he (hmo ▸ htg) (hmo ▸ hcb)
  subst hgcm
  have hmbs : sp.mbar = oFinal L c := hmb
  have hcnt : ((X.tr g).take k).countP (commitsTo (oFinal L c)) = 0 := hcommit he hmbs
  have hki : k = i' := by
    refine nthEv_unique (p := commitsTo (oFinal L c)) he (by simp [commitsTo, hmbs]) hget'
      (by simp [commitsTo, hmbar']) ?_
    rw [hcnt, hcommit hget' hmbar']
  subst hki
  have hsp' : sp' = sp := by
    have := hget'.symm.trans he
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at this
    exact this.2
  subst hsp'
  have hrr : rank' = r := by
    obtain ⟨h1, -⟩ := target_commitSpec (hsp ▸ htgt')
    obtain ⟨h2, -⟩ := target_commitSpec (hsp ▸ htg)
    exact Fin.ext (h1.trans h2.symm)
  subst hrr
  exact Good.of_observed hX hx hrank' hobs hh hhc

/-! ### The premises and the assembly -/

/-- **Every commit to an `s_ready` barrier of an exited CTA is observed** by a successful poll of
a thread of its CTA (the softmax thread's poll for the block, `SO.s_observes`): the counting fact
that the MMA warp's QK commits and the softmax region's polls of `s_ready` agree in number. It is
stated for an exited CTA: before the exit the poll may not have happened yet (an execution is a
prefix of a run), and the only use of the premise is the chain to an exit of the CTA. -/
def SObserved (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {sp : TcCommit.Spec} {r : Fin 16} {m : Loc} {b : Nat},
    X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some m → b < 2 →
      m = sReady L (g / L.block) b → CtaExited L X (g / L.block) →
      ∃ h j acq ws, h < L.threads ∧ h / L.block = g / L.block ∧
        X.AsyncPresent (g, k) (.tcNotify r) ∧
        WaitObserves X (.async (g, k) (.tcNotify r)) (h, j) m acq ws

/-- **A commit at a selected site is followed by another commit of its thread**, once its CTA
exited (the `o_final` commit follows every `kv_empty` and `o_done` commit). -/
def NextCommit (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {sp : TcCommit.Spec}, X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ →
    Assumptions.commitOrderSites.contains pc = true → CtaExited L X (g / L.block) →
      ∃ k', k < k' ∧ ∃ s', X.Commit (g, k') s'

/-- The specification of a commit of the kernel is a `commitSpec` of its CTA. -/
theorem commit_spec_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc : Nat} {s : TcCommit.Spec}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit s)⟩) :
    ∃ l, s = commitSpec (g / L.block) l := by
  rcases commit_class hpre hX hf he with ⟨⟨b, -, rfl⟩, -⟩ | ⟨rfl, -⟩ | ⟨-, l, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **Every commit of an exited CTA has a chain to an exit.** -/
theorem good_all (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (F : ∀ c < L.grid, Tmem1.OFinalFacts L X c)
    (hS : SObserved L X)
    (hN : NextCommit L X) {c : Nat} (hx : CtaExited L X c) :
    ∀ (n g k pc : Nat) (s : TcCommit.Spec) (r : Fin 16) (m : Loc),
      (X.tr g).length - k ≤ n → g / L.block = c →
      X.get (g, k) = some ⟨pc, .tc (.commit s)⟩ → TcCommit.target s r = some m →
        Good L X c g k r := by
  intro n
  induction n with
  | zero =>
    intro g k pc s r m hn hgc he htg
    have := len_of_get he
    simp only at this
    omega
  | succ n ih =>
    intro g k pc s r m hn hgc he htg
    subst hgc
    rcases commit_class hpre hX hf he with ⟨⟨b, hb, rfl⟩, -⟩ | ⟨rfl, -⟩ | ⟨hsel, l, rfl⟩
    · obtain ⟨-, hm⟩ := target_commitSpec htg
      obtain ⟨h, j, acq, ws, hh, hhc, hp, hwo⟩ := hS he htg hb (by rw [hm]; rfl) hx
      exact Good.of_observed hX hx hp hwo hh hhc
    · exact final_good hpre hX hf F he htg rfl hx
    · obtain ⟨hr0, -⟩ := target_commitSpec htg
      obtain ⟨k0, hk0, s0, hs0⟩ := hN he hsel hx
      have hex : ∃ q, k < q ∧ ∃ s', X.Commit (g, q) s' := ⟨k0, hk0, s0, hs0⟩
      classical
      set k' := Nat.find hex with hk'
      obtain ⟨hkk, s', pc', hget'⟩ := Nat.find_spec hex
      have hmin : ∀ q, k < q → q < k' → ¬ ∃ s, X.Commit (g, q) s := by
        intro q hq hq' ⟨s2, hs2⟩
        exact Nat.find_min hex hq' ⟨hq, s2, hs2⟩
      obtain ⟨l', hl'⟩ := commit_spec_of hpre hX hf hget'
      have hr : r = ⟨0, by omega⟩ := Fin.ext hr0
      have htg' : TcCommit.target s' r = some ⟨.shared, g / L.block, l'.addr⟩ := by
        rw [hl', hr]
        exact target_commitSpec_zero _ _
      have hlen : (X.tr g).length - k' ≤ n := by
        have := len_of_get hget'
        simp only at this
        omega
      have hg' := ih g k' pc' s' r _ hlen rfl hget' htg'
      exact Good.of_next hX he hsel hkk ⟨s', pc', hget'⟩ hmin hg'

/-- **`CommitFinished`**: the arrive-on of every commit completes before an exit of its CTA. -/
theorem commitFinished (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (own : Own L X)
    (F : ∀ c < L.grid, Tmem1.OFinalFacts L X c)
    (hS : SObserved L X) (hN : NextCommit L X) : CommitFinished L X := by
  intro ⟨g, k⟩ s rank m ⟨pc, he⟩ htg hx
  have hmc : m.cta = g / L.block := own.mbar (.inr (.inr (.inr (.inl ⟨s, rank, ⟨pc, he⟩, htg⟩))))
  rw [hmc] at hx ⊢
  exact (good_all hpre hX hf F hS hN hx (X.tr g).length g k pc s rank m (Nat.sub_le _ _) rfl he
    htg).finished

end
end PTX.Kernels.InklingRelDecode.Proof.Life
