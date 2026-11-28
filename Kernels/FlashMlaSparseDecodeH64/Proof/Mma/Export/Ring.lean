-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Mma
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaExit
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count

@[expose] public section

/-! # The MMA lane's time against its commits

For a lane `y` with an event `e0` of the MMA code after the election (`MmaOn L y e0.pc`: the CTA's
MMA lane, `mmaLane`), with the slots of `Lib/Slots.lean` and the CTA's block count
`blocksOf P L c`, `C` its commits to the slot's object:

* `mma_qkEarly`: short of the uses of `qkDone j` (`C < ringUses 2 j R`), the lane is no later than
  `qkCommit (2 C + j)`; `mma_qkExit`: a lane that exited has made all of them;
* `mma_svEarly`, `mma_svExit`: the same for `svDone j` and `svCommit`;
* `mma_qUtEarly`: before its commit to `bar_q_utccp` the lane is earlier than `qUtccpSlot`
  (whether or not it has reached the arrival at pc 1929).

The early facts come from one view of the lane's last state (`mma_end`): a prologue state at
`mmaOrg + ord` with its counts, a block-`r` state at `frame r + mmaOff + off` with its counts, or
the barrier or the exit with the full counts (`Common/MmaExit.lean`: the early return of a CTA
beyond the batch is not reached after an MMA event). The exit facts read the full counts behind
the exit (`mma_exit_full`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-! ### Site arithmetic -/

/-- A loop site's place plus the step: up to the commit to `qk_done` at most `18`, after it at
most `mmaPvc`. -/
private theorem loop_x {s : Mma.Site} {δ : Nat} (h : s.inLoop = true) (hδ : δ ≤ 1)
    (hm : δ = 1 → s ≠ .qkCommit ∧ s ≠ .pvCommit) :
    (s.idx ≤ 18 ∧ s.off + δ ≤ 18) ∨ (19 ≤ s.idx ∧ s.off + δ ≤ mmaPvc) := by
  cases s <;> simp only [Mma.Site.inLoop, reduceCtorEq] at h
  all_goals simp only [Mma.Site.idx, Mma.Site.off, mmaSo, mmaPvc, ne_eq, reduceCtorEq,
    not_false_eq_true, and_true, not_true_eq_false, and_false, imp_false] at hm ⊢
  all_goals (try have := ‹Fin _›.isLt)
  all_goals omega

/-- A prologue site's place: at most `33`, at most `31` before the commit's count. -/
private theorem pro_x {s : Mma.Site} {δ : Nat} (h : Mma.ProSite s) (hδ : δ ≤ 1)
    (hm : δ = 1 → s ≠ .qCopyCommit) :
    s.ord + δ ≤ 34 ∧ (s.pro ≤ 28 → s.ord + δ ≤ 31) := by
  obtain ⟨h1, h2, h3⟩ := h
  cases s <;> simp only [Mma.Site.inLoop, reduceCtorEq, ne_eq, not_true_eq_false] at h1 h2 h3
  all_goals simp only [Mma.Site.ord, Mma.Site.pro, ne_eq, reduceCtorEq, not_false_eq_true,
    not_true_eq_false, imp_false] at hm ⊢
  all_goals (try have := ‹Fin _›.isLt)
  all_goals omega

/-! ### The view of the lane's last state -/

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hnu : ¬ HasUb X) {k : Nat} {e0 : Event} (he0 : X.get (y, k) = some e0)
  (hu0 : ∀ f, e0.kind ≠ .ub f) (hr0 : 1853 < e0.pc ∧ e0.pc < 2162)
include hp hX hFw hnu he0 hu0 hr0

omit hp hX hFw he0 hu0 hr0 in
private theorem noUbM (i : Nat) : ((X.tr y).take i).countP (Mma.cls .ub) = 0 := by
  refine List.countP_eq_zero.mpr fun f hf hcl => hnu ?_
  obtain ⟨j, -, hj⟩ := get_lt_of_mem_take hf
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | ub fl => exact ⟨(y, j), pc, fl, hj⟩
  | wait l q ok a sc => cases ok <;> simp [Mma.cls, Mma.kindOf] at hcl
  | tc t => cases t <;> simp [Mma.cls, Mma.kindOf] at hcl
  | _ => simp [Mma.cls, Mma.kindOf] at hcl

omit hp hX hFw he0 hu0 hr0 in
private theorem noUbG (i : Nat) : ((X.tr y).take i).countP (cls .ub) = 0 :=
  List.countP_eq_zero.mpr fun f hf hcl => hnu (by
    obtain ⟨j, -, hj⟩ := get_lt_of_mem_take hf
    obtain ⟨pc, kd⟩ := f
    cases kd <;> simp [cls] at hcl
    exact ⟨(y, j), pc, _, hj⟩)

/-- The counts of the lane's prefix `i`. -/
private abbrev Cnts (X : Execution) (y i : Nat) (O : Mma.Objs) (j r b : Nat) : Prop :=
  ∀ c, c ≠ .ub → ((X.tr y).take i).countP (Mma.cls c) = Mma.cntAt O j r b false c

/-- **The time of a state of the lane**, plus `δ` when the machine moves on from it. -/
private theorem mma_step {Q : Nat → Prop}
    (hpro : ∀ i (s : Mma.Site) δ, i ≤ (X.tr y).length → Cnts X y i (Mma.objs L y) s.pro 0 0 →
      s.ord + δ ≤ 34 → (s.pro ≤ 28 → s.ord + δ ≤ 31) → Q (mmaOrg + s.ord + δ))
    (hloop : ∀ i r b x, i ≤ (X.tr y).length → r < blocksOf P L (y / L.block) →
      Cnts X y i (Mma.objs L y) 31 r b → (b ≤ 18 ∧ x ≤ 18) ∨ (19 ≤ b ∧ x ≤ mmaPvc) →
      Q (frame r + mmaOff + x))
    (hend : ∀ i, i ≤ (X.tr y).length → (∀ c, c ≠ .ub → c ≠ .bar 12 →
      ((X.tr y).take i).countP (Mma.cls c) =
        Mma.cntAt (Mma.objs L y) 31 (blocksOf P L (y / L.block)) 0 false c) → False)
    {i δ : Nat} {σ : (thread P L y).D} (hi : i ≤ (X.tr y).length) (hki : k ≤ i) (hδ : δ ≤ 1)
    (hσ : Frame.stateAt (thread P L) X y i = some (some σ))
    (hmv : δ = 1 → ∀ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n) →
      d.site ≠ .qkCommit ∧ d.site ≠ .pvCommit ∧ d.site ≠ .qCopyCommit) :
    Q (time P L y σ + δ) := by
  obtain ⟨d, n, rfl, hR, hP⟩ := post_state hp hX hFw hnu he0 hu0 hr0 hki hσ
  have hR := hR (noUbM hnu i)
  have ht : time P L y (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n) = mmaOrg + Mma.place d := rfl
  rw [ht]
  have hrd : d.site ≠ .loadTopk → d.site ≠ .loadExtra →
      Mma.rounds d.l0 d.l1 = blocksOf P L (y / L.block) :=
    mma_rounds hp hX hFw he0 hu0 hr0 hki hσ
  by_cases hlp : d.site.inLoop = true
  · obtain ⟨hok, hcnt⟩ := (Mma.core_loop hlp).mp hR
    obtain ⟨-, -, -, hrR, -⟩ := id hok
    rw [hrd (fun h => by rw [h] at hlp; cases hlp) (fun h => by rw [h] at hlp; cases hlp)] at hrR
    have hx := loop_x hlp hδ fun h => (hmv h d n rfl).imp_right And.left
    have := hloop i d.cnt.toNat d.site.idx (d.site.off + δ) hi hrR hcnt hx
    rw [Mma.place_loop hlp]
    rw [show mmaOrg + (mmaBlk0 + stride * d.cnt.toNat + d.site.off) + δ =
      frame d.cnt.toNat + mmaOff + (d.site.off + δ) by
        simp only [frame, mmaBlk0, loopBase, mmaOff, mmaOrg, stride]; omega]
    exact this
  by_cases hb : d.site = .outBar
  · have hc : ∀ c, c ≠ .ub → ((X.tr y).take i).countP (Mma.cls c) =
        Mma.cntAt (Mma.objs L y) 31 (Mma.rounds d.l0 d.l1) 0 false c := by
      obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
      simp only at hb
      subst hb
      exact hR
    rw [hrd (by rw [hb]; decide) (by rw [hb]; decide)] at hc
    exact (hend i hi fun c h1 _ => hc c h1).elim
  by_cases hx : d.site = .exit
  · have hc := mma_exit_counts hp hX hFw he0 hu0 hr0 hki hσ hx
      (noUbG hnu i) (noUbM hnu i)
    rw [hrd (by rw [hx]; decide) (by rw [hx]; decide)] at hc
    refine (hend i hi fun c h1 h2 => ?_).elim
    rw [hc c h1]
    simp [Mma.cntAt, h2]
  · have hps : Mma.ProSite d.site := ⟨by simpa using hlp, hx, hb⟩
    obtain ⟨-, hpc⟩ := id hps
    have hcnt : Cnts X y i (Mma.objs L y) d.site.pro 0 0 := fun c hc => Mma.pro_cnt hR hps hc
    obtain ⟨h1, h2⟩ := pro_x hps hδ fun h => (hmv h d n rfl).2.2
    rw [Mma.place_pro hps]
    exact hpro i d.site δ hi hcnt h1 h2

/-- **The lane's last state**: the principle behind the early facts. -/
private theorem mma_end {Q : Nat → Prop} (hz : Q 0)
    (hpro : ∀ i (s : Mma.Site) δ, i ≤ (X.tr y).length → Cnts X y i (Mma.objs L y) s.pro 0 0 →
      s.ord + δ ≤ 34 → (s.pro ≤ 28 → s.ord + δ ≤ 31) → Q (mmaOrg + s.ord + δ))
    (hloop : ∀ i r b x, i ≤ (X.tr y).length → r < blocksOf P L (y / L.block) →
      Cnts X y i (Mma.objs L y) 31 r b → (b ≤ 18 ∧ x ≤ 18) ∨ (19 ≤ b ∧ x ≤ mmaPvc) →
      Q (frame r + mmaOff + x))
    (hend : ∀ i, i ≤ (X.tr y).length → (∀ c, c ≠ .ub → c ≠ .bar 12 →
      ((X.tr y).take i).countP (Mma.cls c) =
        Mma.cntAt (Mma.objs L y) 31 (blocksOf P L (y / L.block)) 0 false c) → False) :
    Q (Sched.threadTime (timed P L) X y) := by
  have hk : k < (X.tr y).length := (List.getElem?_eq_some_iff.mp he0).1
  have hg := Frame.lt_of_get hX he0
  have step := @mma_step _ _ _ _ _ hp hX hFw hnu _ _ he0 hu0 hr0 Q hpro hloop hend
  rw [timed_eq]
  unfold Sched.threadTime
  cases hs : Frame.stateAt (thread P L) X y (X.tr y).length with
  | some o =>
    cases o with
    | none => exact absurd hs (follow_iff.mp hFw y hg _).1
    | some σ => simpa using step (Nat.le_refl _) hk.le (Nat.zero_le 1) hs (by omega)
  | none =>
    simp only
    cases hs' : Frame.stateAt (thread P L) X y ((X.tr y).length - 1) with
    | none => exact hz
    | some o =>
      cases o with
      | none => exact absurd hs' (follow_iff.mp hFw y hg _).1
      | some σ =>
        refine step (by omega) (by omega) (Nat.le_refl 1) hs' fun _ d n hd => ?_
        obtain ⟨f, hf⟩ : ∃ f, (X.tr y)[(X.tr y).length - 1]? = some f :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hn := Frame.stateAt_succ (C := thread P L) hf
        rw [Nat.sub_add_cancel (by omega), hs, hs', hd] at hn
        refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
          simp [Code.toMachine, Mma.succ, h] at hn

end

/-! ### The facts -/

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- The lane's commits on `l` at prefix `i`: at most its commits. -/
private theorem commits_take (hw : warp L y = 4) (i : Nat) (l : Loc) :
    ((X.tr y).take i).countP (Mma.cls (.commit l)) ≤ (X.tr y).countP (PTX.Flow.commitsTo l) := by
  rw [← lane4_commits hp hX hFw hw i, flow_commitsTo]
  exact (List.take_sublist i _).countP_le

omit hp hX hFw in
/-- The full counts with and without the barrier agree off the barrier. -/
private theorem cnt_fin {O : Mma.Objs} {R : Nat} {c : Mma.Cnt} (h : c ≠ .bar 12) :
    Mma.cntAt O 31 R 0 true c = Mma.cntAt O 31 R 0 false c := by
  simp [Mma.cntAt, h]

/-- **The MMA lane short of its uses of `qkDone j` is no later than the commit slot of its next
use.** -/
theorem mma_qkEarly (hnu : ¬ HasUb X) {k : Nat} {e0 : Event} (he0 : X.get (y, k) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hon : MmaOn L y e0.pc) {c : Nat} {j : Fin 2}
    (hc : y / L.block = c)
    (hlt : (X.tr y).countP (PTX.Flow.commitsTo (mbarLoc L c (.qkDone j))) <
      ringUses 2 j.val (blocksOf P L c)) :
    Sched.threadTime (timed P L) X y ≤
      qkCommit (2 * (X.tr y).countP (PTX.Flow.commitsTo (mbarLoc L c (.qkDone j))) + j.val) := by
  obtain ⟨⟨hw, -, h2⟩, h1⟩ := hon
  subst hc
  have hC := commits_take hp hX hFw hw (l := loc L y (.qkDone j))
  simp only [loc] at hC
  have hj := j.isLt
  refine mma_end hp hX hFw hnu he0 hu0 ⟨h1, h2⟩ (Q := fun t => t ≤ qkCommit (2 * (X.tr y).countP
    (PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.qkDone j))) + j.val)) (Nat.zero_le _)
    (fun _ _ _ _ _ h34 _ => ?_) (fun i r b x _ _ hcnt hx => ?_) (fun i _ hF => ?_)
  · simp only [qkCommit, frame, loopBase, stride, mmaOff, mmaQkc, mmaOrg]; omega
  · have h3 := (hcnt _ (by simp)).trans (Mma.cnt_qk hp r b j)
    have := hC i
    simp only [loc] at h3
    simp only [Mma.useAt, ringUses, Mma.ind, qkCommit, frame, loopBase, stride, mmaOff, mmaQkc,
      mmaPvc] at h3 hlt hx ⊢
    split_ifs at h3 <;> omega
  · have h3 := (hF _ (by simp) (by simp)).trans (Mma.cnt_qk hp _ 0 j)
    have := hC i
    simp only [loc] at h3
    simp only [Mma.useAt, ringUses, Mma.ind] at h3 hlt
    split_ifs at h3 <;> omega

/-- **The MMA lane short of its uses of `svDone j` is no later than the commit slot of its next
use.** -/
theorem mma_svEarly (hnu : ¬ HasUb X) {k : Nat} {e0 : Event} (he0 : X.get (y, k) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hon : MmaOn L y e0.pc) {c : Nat} {j : Fin 2}
    (hc : y / L.block = c)
    (hlt : (X.tr y).countP (PTX.Flow.commitsTo (mbarLoc L c (.svDone j))) <
      ringUses 2 j.val (blocksOf P L c)) :
    Sched.threadTime (timed P L) X y ≤
      svCommit (2 * (X.tr y).countP (PTX.Flow.commitsTo (mbarLoc L c (.svDone j))) + j.val) := by
  obtain ⟨⟨hw, -, h2⟩, h1⟩ := hon
  subst hc
  have hC := commits_take hp hX hFw hw (l := loc L y (.svDone j))
  simp only [loc] at hC
  have hj := j.isLt
  refine mma_end hp hX hFw hnu he0 hu0 ⟨h1, h2⟩ (Q := fun t => t ≤ svCommit (2 * (X.tr y).countP
    (PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.svDone j))) + j.val)) (Nat.zero_le _)
    (fun _ _ _ _ _ h34 _ => ?_) (fun i r b x _ _ hcnt hx => ?_) (fun i _ hF => ?_)
  · simp only [svCommit, frame, loopBase, stride, mmaOff, mmaPvc, mmaOrg]; omega
  · have h3 := (hcnt _ (by simp)).trans (Mma.cnt_sv hp r b j)
    have := hC i
    simp only [loc] at h3
    simp only [ringUses, svCommit, frame, loopBase, stride, mmaOff, mmaPvc] at h3 hlt hx ⊢
    omega
  · have h3 := (hF _ (by simp) (by simp)).trans (Mma.cnt_sv hp _ 0 j)
    have := hC i
    simp only [loc] at h3
    omega

/-- **The MMA lane before its commit to `bar_q_utccp` is earlier than the slot**, from any event
of the MMA code after the election on (before or after the arrival at pc 1929). -/
theorem mma_qUtEarly (hnu : ¬ HasUb X) {k : Nat} {e0 : Event} (he0 : X.get (y, k) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hon : MmaOn L y e0.pc)
    (h0 : (X.tr y).countP (PTX.Flow.commitsTo (loc L y .qUtccp)) = 0) :
    Sched.threadTime (timed P L) X y < qUtccpSlot := by
  obtain ⟨⟨hw, -, h2⟩, h1⟩ := hon
  have hC := commits_take hp hX hFw hw (l := loc L y .qUtccp)
  have hq : ∀ j r b, Mma.cntAt (Mma.objs L y) j r b false (.commit (loc L y .qUtccp)) =
      Mma.ind (29 ≤ j) := fun j r b => by
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.obj_qUt hp, Mma.obj_qk hp, Mma.obj_sv hp,
      Mma.mloc_eq_iff]
  refine mma_end hp hX hFw hnu he0 hu0 ⟨h1, h2⟩ (Q := fun t => t < qUtccpSlot)
    (by simp [qUtccpSlot]) (fun i s _ _ hcnt _ h31 => ?_)
    (fun i r b x _ _ hcnt _ => ?_) (fun i _ hF => ?_)
  · have h3 := (hcnt _ (by simp)).trans (hq _ 0 0)
    have := hC i
    simp only [Mma.ind] at h3
    split_ifs at h3 with h
    · omega
    · have := h31 (by omega)
      have := qUtccp_lt
      omega
  · have h3 := (hcnt _ (by simp)).trans (hq 31 r b)
    have := hC i
    simp only [Mma.ind] at h3
    split_ifs at h3 <;> omega
  · have h3 := (hF _ (by simp) (by simp)).trans (hq 31 _ 0)
    have := hC i
    simp only [Mma.ind] at h3
    split_ifs at h3 <;> omega

/-- **The MMA lane that exited has made all its uses of `qkDone j`.** -/
theorem mma_qkExit {k x pc : Nat} {e0 : Event} (he0 : X.get (y, k) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hon : MmaOn L y e0.pc) {c : Nat} {j : Fin 2}
    (hc : y / L.block = c) (hx : X.get (y, x) = some ⟨pc, .exit⟩) :
    ringUses 2 j.val (blocksOf P L c) ≤
      (X.tr y).countP (PTX.Flow.commitsTo (mbarLoc L c (.qkDone j))) := by
  obtain ⟨⟨hw, -, h2⟩, h1⟩ := hon
  subst hc
  have h3 := ((mma_exit_full hp hX hFw he0 hu0 ⟨h1, h2⟩ hx _ (by simp)).trans
    (cnt_fin (by simp))).trans (Mma.cnt_qk hp _ 0 j)
  have := commits_take hp hX hFw hw x (loc L y (.qkDone j))
  simp only [loc, Mma.useAt, Mma.ind] at h3 this
  split_ifs at h3 <;> omega

/-- **The MMA lane that exited has made all its uses of `svDone j`.** -/
theorem mma_svExit {k x pc : Nat} {e0 : Event} (he0 : X.get (y, k) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hon : MmaOn L y e0.pc) {c : Nat} {j : Fin 2}
    (hc : y / L.block = c) (hx : X.get (y, x) = some ⟨pc, .exit⟩) :
    ringUses 2 j.val (blocksOf P L c) ≤
      (X.tr y).countP (PTX.Flow.commitsTo (mbarLoc L c (.svDone j))) := by
  obtain ⟨⟨hw, -, h2⟩, h1⟩ := hon
  subst hc
  have h3 := ((mma_exit_full hp hX hFw he0 hu0 ⟨h1, h2⟩ hx _ (by simp)).trans
    (cnt_fin (by simp))).trans (Mma.cnt_sv hp _ 0 j)
  have := commits_take hp hX hFw hw x (loc L y (.svDone j))
  simp only [loc] at h3 this
  omega

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
