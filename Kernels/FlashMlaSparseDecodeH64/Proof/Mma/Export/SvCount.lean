-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MmaSlot
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaExit
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CommitSites
import Lemmas.Protocol.NotifyBlocker

@[expose] public section

/-! # The MMA lane's commits to `qkDone` and `svDone`: at most the CTA's uses of the slot

A commit to `svDone s` of CTA `c` is the PV commit of a block `r` below the CTA's block count
(`blocksOf`, the lane's loaded words) with `r % 2 = s`, after `r / 2` earlier commits to the slot
(`commit_block`). So a lane makes at most `ringUses 2 s (blocksOf P L c)` of them over its whole
trace (`mma_svCommits_le`): the last one would otherwise be a commit with that many before it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **A QK commit and a PV commit are of a block below the CTA's block count**: the commit of
block `r` to `qkDone s` (to `svDone s`) has `s = slot2 r`, and before it the lane made `r / 2`
commits to that slot of `qkDone` (`ringUses 2 b r` to each slot `b` of `svDone`). -/
private theorem commit_block {i pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) :
    (∀ c s, sp.mbar = mbarLoc L c (.qkDone s) → c = y / L.block ∧ ∃ r, r < blocksOf P L c ∧
      s = slot2 r ∧ ((X.tr y).take i).countP
        (PTX.Flow.commitsTo (mbarLoc L c (.qkDone s))) = r / 2 ∧
        ((X.tr y).take i).countP (Proof.Mma.cls .mma) = 24 * r + 16) ∧
    (∀ c s, sp.mbar = mbarLoc L c (.svDone s) → c = y / L.block ∧ ∃ r, r < blocksOf P L c ∧
      s = slot2 r ∧ (∀ b : Fin 2, ((X.tr y).take i).countP
        (PTX.Flow.commitsTo (mbarLoc L c (.svDone b))) = ringUses 2 b.val r) ∧
        ((X.tr y).take i).countP (Proof.Mma.cls .mma) = 24 * r + 24) := by
  have h := commit_pcs hX he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  have hub : ∀ f, (⟨pc, .tc (.commit sp)⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, hE, hl, hw⟩ := mma_state hJ hi hev hpc
    ⟨by simp only; omega, by simp only; omega⟩
  have hR := hR (state_ub hX hσ he)
  have hc : (fun c => n (.mma c)) = fun c => ((X.tr y).take i).countP (Mma.cls c) :=
    funext fun c => state_count hσ (.mma c)
  rw [hc] at hR
  have hR := hR (take_noUb hX he)
  rcases Mma.ev_commit hl hE with ⟨hs, hm'⟩ | ⟨hs, hm'⟩ | ⟨hs, hm'⟩
  · refine ⟨fun c s hm => ?_, fun c s hm => ?_⟩ <;>
      cases (Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.qUt_loc hp)))).2
  · obtain ⟨⟨-, -, -, hrR, -, hpha, -⟩, hn⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hR
    rw [hpha] at hm'
    have hrd := mma_rounds hp hX hFw he hub ⟨by simp only; omega, by simp only; omega⟩ le_rfl hσ
      (fun h => by rw [h] at hs; cases hs) (fun h => by rw [h] at hs; cases hs)
    refine ⟨fun c s hm => ?_, fun c s hm => ?_⟩
    · obtain ⟨rfl, hf⟩ :=
        Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.qk_loc hp (slot2 d.cnt.toNat))))
      cases MbarFam.qkDone.inj hf
      have hC := lane4_commits hp hX hFw hw i (loc L y (.qkDone (slot2 d.cnt.toNat)))
      rw [hn _ (by simp), Mma.cnt_qk hp] at hC
      simp only [loc] at hC
      refine ⟨rfl, d.cnt.toNat, by omega, rfl, ?_, ?_⟩
      · rw [flow_commitsTo, hC, hs]
        simp [Mma.useAt, Mma.Site.idx, Mma.ind, slot2, ringUses]
        omega
      · rw [hn _ (by simp), hs]
        simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.mmaIn, Mma.Site.idx]
    · cases (Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.qk_loc hp (slot2 d.cnt.toNat))))).2
  · obtain ⟨⟨-, -, -, hrR, -, hpha, -⟩, hn⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hR
    rw [hpha] at hm'
    have hrd := mma_rounds hp hX hFw he hub ⟨by simp only; omega, by simp only; omega⟩ le_rfl hσ
      (fun h => by rw [h] at hs; cases hs) (fun h => by rw [h] at hs; cases hs)
    refine ⟨fun c s hm => ?_, fun c s hm => ?_⟩
    · cases (Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.sv_loc hp (slot2 d.cnt.toNat))))).2
    · obtain ⟨rfl, hf⟩ :=
        Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.sv_loc hp (slot2 d.cnt.toNat))))
      cases MbarFam.svDone.inj hf
      refine ⟨rfl, d.cnt.toNat, by omega, rfl, fun b => ?_, ?_⟩
      · have hC := lane4_commits hp hX hFw hw i (loc L y (.svDone b))
        rw [hn _ (by simp), Mma.cnt_sv hp] at hC
        simp only [loc] at hC
        rw [flow_commitsTo, hC]
      · rw [hn _ (by simp), hs]
        simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.mmaIn, Mma.Site.idx]

/-- **A PV commit to `svDone s` of CTA `c` is the commit of a block `r` below the CTA's block
count**: `s` is the block's slot, and before the commit the lane made `ringUses 2 b r` commits to
each slot `b`. -/
theorem mma_svBlock {i pc c : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = mbarLoc L c (.svDone s)) :
    c = y / L.block ∧ ∃ r, r < blocksOf P L c ∧ s = slot2 r ∧ ∀ b : Fin 2,
      ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L c (.svDone b))) =
        ringUses 2 b.val r := by
  obtain ⟨hc, r, hr, hs, hall, -⟩ := (commit_block hp hX hFw he).2 c s hm
  exact ⟨hc, r, hr, hs, hall⟩

/-- **A QK commit to `qkDone s` of CTA `c` is the commit of a block `r` below the CTA's block
count**: `s` is the block's slot, and before the commit the lane made `r / 2` commits to it. -/
theorem mma_qkBlock {i pc c : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = mbarLoc L c (.qkDone s)) :
    c = y / L.block ∧ ∃ r, r < blocksOf P L c ∧ s = slot2 r ∧
      ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L c (.qkDone s))) = r / 2 := by
  obtain ⟨hc, r, hr, hs, hall, -⟩ := (commit_block hp hX hFw he).1 c s hm
  exact ⟨hc, r, hr, hs, hall⟩

/-- **The MMA lane's commits to `svDone s` of CTA `c` are at most the CTA's uses of the slot.** -/
theorem mma_svCommits_le (c : Nat) (s : Fin 2) :
    (X.tr y).countP (PTX.Flow.commitsTo (mbarLoc L c (.svDone s))) ≤
      ringUses 2 s.val (blocksOf P L c) := by
  by_contra hlt
  obtain ⟨e, he, hpe, hcnt⟩ := nthEv_spec (X := X) (g := y) (Nat.lt_of_not_le hlt)
  obtain ⟨sp, hks, hsm⟩ := MbarRing.Notify.commit_of_commitsTo hpe
  obtain ⟨pce, kd⟩ := e
  simp only at hks
  subst hks
  obtain ⟨-, r, hr, hs, hall⟩ := mma_svBlock hp hX hFw he hsm
  have h1 := hall s
  rw [hcnt] at h1
  subst hs
  simp only [slot2, ringUses] at h1
  omega

/-- **A PV commit of a block before the last has a later commit in its lane**, once the lane
exited: the commits to the other slot, which the block `r + 1` makes, are `ringUses 2 b R` at the
exit and `ringUses 2 b r` before the commit. -/
theorem mma_svNext {i pc c x pcx r : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hc : c = y / L.block)
    (hx : X.get (y, x) = some ⟨pcx, .exit⟩) (hr : r + 1 < blocksOf P L c) (hs : s = slot2 r)
    (hall : ∀ b : Fin 2, ((X.tr y).take i).countP
      (PTX.Flow.commitsTo (mbarLoc L c (.svDone b))) = ringUses 2 b.val r)
    (hsm : sp.mbar = mbarLoc L c (.svDone s)) :
    ∃ j pc' sp', i < j ∧ X.get (y, j) = some ⟨pc', .tc (.commit sp')⟩ := by
  have hw := mma_commit_warp hp hX hFw he
  have hpc := commit_pcs hX he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  have hex := mma_exit_full hp hX hFw he (fun _ h => by cases h)
    ⟨by simp only; omega, by simp only; omega⟩ hx
    (.commit (loc L y (.svDone (slot2 (r + 1))))) (by simp)
  have hn := lane4_commits hp hX hFw hw x (loc L y (.svDone (slot2 (r + 1))))
  rw [hex] at hn
  subst hc
  have hb : ∀ b : Fin 2, Mma.cntAt (Mma.objs L y) 31 (blocksOf P L (y / L.block)) 0 true
      (.commit (loc L y (.svDone b))) = ringUses 2 b.val (blocksOf P L (y / L.block)) := by
    intro b
    fin_cases b <;> simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.obj_qUt hp, Mma.obj_qk hp,
      Mma.obj_sv hp, Mma.mloc_eq_iff, Mma.ind]
  rw [hb] at hn
  have hlt : ringUses 2 (slot2 (r + 1)).val r < (X.tr y).countP
      (PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.svDone (slot2 (r + 1))))) := by
    have h1 := (List.take_sublist x (X.tr y)).countP_le
      (p := PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.svDone (slot2 (r + 1)))))
    simp only [loc] at hn
    rw [flow_commitsTo] at h1 ⊢
    simp only [slot2, ringUses] at hn h1 ⊢
    omega
  obtain ⟨e, hj, hpe, hcnt⟩ := nthEv_spec hlt
  obtain ⟨sp', hk, hmb⟩ := MbarRing.Notify.commit_of_commitsTo hpe
  obtain ⟨pce, kd⟩ := e
  simp only at hk
  subst hk
  refine ⟨_, pce, sp', ?_, hj⟩
  have h2 := hall (slot2 (r + 1))
  by_contra hle
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with h3 | h3
  · have e1 := countP_take_succ hj hpe
    have e2 := countP_take_mono (PTX.Flow.commitsTo (mbarLoc L (y / L.block)
      (.svDone (slot2 (r + 1))))) (X.tr y) (show _ + 1 ≤ i from h3)
    omega
  · rw [h3, he] at hj
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hj
    obtain ⟨-, rfl⟩ := hj
    have := (Mma.mloc_fam (hsm.symm.trans hmb)).2
    have h5 : s = slot2 (r + 1) := MbarFam.svDone.inj this
    rw [hs] at h5
    simp only [slot2, Fin.mk.injEq] at h5
    omega

omit hp hX hFw in
private theorem mmaIn_qk {k : Nat} (h : k < 16) : Mma.mmaIn (2 + k) = k := by
  unfold Mma.mmaIn; split_ifs <;> omega

omit hp hX hFw in
private theorem mmaIn_pv {k : Nat} (h : k < 8) : Mma.mmaIn (21 + k) = 16 + k := by
  unfold Mma.mmaIn; split_ifs <;> omega

/-- **An MMA of the lane is the `24 r + k`-th MMA**: a QK MMA (D at 400) with `k < 16`, or a PV MMA
(D at `128 (k % 2)`) which is the `16 + k`-th of its block. -/
private theorem mma_nth_site {x pcx b : Nat} {sx : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hx : X.get (y, x) = some ⟨pcx, .tc (.mma b sx acc mask)⟩)
    (hat : MbarRow.MmaAt L y pcx) :
    ∃ r k, (k < 16 ∧ b = 400 ∧ ((X.tr y).take x).countP (Proof.Mma.cls .mma) = 24 * r + k) ∨
      (k < 8 ∧ b = 128 * (k % 2) ∧
        ((X.tr y).take x).countP (Proof.Mma.cls .mma) = 24 * r + 16 + k) := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  have hub : ∀ f, (⟨pcx, .tc (.mma b sx acc mask)⟩ : Event).kind ≠ .ub f :=
    fun _ h => by cases h
  obtain ⟨d, hR, ⟨-, hE⟩, hl, -⟩ := mma_at hp hX hFw hx hub ⟨hlo, hhi⟩
  have hc := hR (take_noUb hX hx)
  cases hs : d.site with
  | qk k =>
    obtain ⟨-, hn⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    refine ⟨d.cnt.toNat, k.val, .inl ⟨k.isLt, ?_, ?_⟩⟩
    · simp only [Mma.EvK, hs] at hE
      rcases hE with ⟨s', h1, -⟩ | ⟨f, hf⟩
      · simp only [Kind.tc.injEq, TcKind.mma.injEq] at h1
        exact h1.1
      · cases hf
    · rw [hn _ (by simp), hs]
      simp only [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.idx, mmaIn_qk k.isLt]
      simp
  | pv k =>
    obtain ⟨-, hn⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    refine ⟨d.cnt.toNat, k.val, .inr ⟨k.isLt, ?_, ?_⟩⟩
    · simp only [Mma.EvK, hs] at hE
      rcases hE with ⟨s', h1, -⟩ | ⟨f, hf⟩
      · simp only [Kind.tc.injEq, TcKind.mma.injEq] at h1
        exact h1.1
      · cases hf
    · rw [hn _ (by simp), hs]
      simp only [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.idx, mmaIn_pv k.isLt]
      simp
      omega
  | leave s' => exact absurd hs (hl s')
  | _ =>
    exfalso
    simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, hs] at hE

omit hp hX hFw in
/-- The MMA with `n` earlier ones, when the lane made more than `n` before `i`. -/
private theorem mma_nth {i n : Nat} (hw : warp L y = 4)
    (h : n + 1 ≤ ((X.tr y).take i).countP (Proof.Mma.cls .mma)) :
    ∃ x < i, ∃ pcx b sx acc mask, X.get (y, x) = some ⟨pcx, .tc (.mma b sx acc mask)⟩ ∧
      MbarRow.MmaAt L y pcx ∧ ((X.tr y).take x).countP (Proof.Mma.cls .mma) = n := by
  obtain ⟨x, e, hx, hg, hp, hc⟩ := exists_nthEv h
  obtain ⟨pcx, kd⟩ := e
  have hr : Mma.inRole ⟨pcx, kd⟩ = true ∧ Mma.kindOf ⟨pcx, kd⟩ = some .mma := by
    simpa [Mma.cls] using hp
  obtain ⟨hin, hk⟩ := hr
  simp only [Mma.inRole, decide_eq_true_eq] at hin
  obtain ⟨b, sx, acc, mask, rfl⟩ : ∃ b sx acc mask, kd = .tc (.mma b sx acc mask) := by
    unfold Mma.kindOf at hk
    split at hk <;> first | (simp at hk; done) | exact ⟨_, _, _, _, by assumption⟩
  exact ⟨x, hx, pcx, b, sx, acc, mask, hg, ⟨hw, by omega, by omega⟩, hc⟩

/-- **A QK commit follows a QK MMA, and a PV MMA of each parity if past the first block**: the
commit of block `r` to `qkDone s` is after the block's first QK MMA and, for `r ≥ 1`, after both
first PV MMAs of block `r - 1` (the lane's `24 r + 16` MMAs). -/
theorem mma_qkMmas {i pc c : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = mbarLoc L c (.qkDone s)) :
    ∃ r, s = slot2 r ∧ ((X.tr y).take i).countP
        (PTX.Flow.commitsTo (mbarLoc L c (.qkDone s))) = r / 2 ∧
      (∃ x < i, ∃ pcx sx acc mask, X.get (y, x) = some ⟨pcx, .tc (.mma 400 sx acc mask)⟩ ∧
        MbarRow.MmaAt L y pcx) ∧
      (1 ≤ r → ∀ kk < 2, ∃ x < i, ∃ pcx sx acc mask,
        X.get (y, x) = some ⟨pcx, .tc (.mma (128 * kk) sx acc mask)⟩ ∧ MbarRow.MmaAt L y pcx) := by
  have hw := mma_commit_warp hp hX hFw he
  obtain ⟨-, r, -, hs, hall, hn⟩ := (commit_block hp hX hFw he).1 c s hm
  refine ⟨r, hs, hall, ?_, fun hr kk hkk => ?_⟩
  · obtain ⟨x, hxi, pcx, b, sx, acc, mask, hx, hat, hc⟩ := mma_nth (X := X) hw
      (i := i) (n := 24 * r) (by omega)
    obtain ⟨r', k, ⟨hk, hb, hc'⟩ | ⟨hk, hb, hc'⟩⟩ := mma_nth_site hp hX hFw hx hat
    · subst hb
      exact ⟨x, hxi, pcx, sx, acc, mask, hx, hat⟩
    · omega
  · obtain ⟨x, hxi, pcx, b, sx, acc, mask, hx, hat, hc⟩ := mma_nth (X := X) hw
      (i := i) (n := 24 * (r - 1) + 16 + kk) (by omega)
    obtain ⟨r', k, ⟨hk, hb, hc'⟩ | ⟨hk, hb, hc'⟩⟩ := mma_nth_site hp hX hFw hx hat
    · omega
    · have hk' : k = kk := by omega
      subst hk'
      refine ⟨x, hxi, pcx, sx, acc, mask, ?_, hat⟩
      rw [hx, hb, Nat.mod_eq_of_lt hkk]

/-- **A PV commit follows both first PV MMAs of its block** (the lane's `24 r + 24` MMAs). -/
theorem mma_svMmas {i pc c : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = mbarLoc L c (.svDone s)) :
    ∀ kk < 2, ∃ x < i, ∃ pcx sx acc mask,
      X.get (y, x) = some ⟨pcx, .tc (.mma (128 * kk) sx acc mask)⟩ ∧ MbarRow.MmaAt L y pcx := by
  intro kk hkk
  have hw := mma_commit_warp hp hX hFw he
  obtain ⟨-, r, -, -, -, hn⟩ := (commit_block hp hX hFw he).2 c s hm
  obtain ⟨x, hxi, pcx, b, sx, acc, mask, hx, hat, hc⟩ := mma_nth (X := X) hw
    (i := i) (n := 24 * r + 16 + kk) (by omega)
  obtain ⟨r', k, ⟨hk, hb, hc'⟩ | ⟨hk, hb, hc'⟩⟩ := mma_nth_site hp hX hFw hx hat
  · omega
  · have hk' : k = kk := by omega
    subst hk'
    refine ⟨x, hxi, pcx, sx, acc, mask, ?_, hat⟩
    rw [hx, hb, Nat.mod_eq_of_lt hkk]

omit hp hX hFw in
private theorem cls_mma (e : Event) : Mma.cls .mma e = isMmaIssue e := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | wait q p ok a sc => cases ok <;> simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]
  | tc t => cases t <;> simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]
  | _ => simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]

omit hp hX hFw in
private theorem issues_eq (xs : List Event) : xs.countP (Mma.cls .mma) = mmaIssues xs :=
  List.countP_congr fun e _ => by rw [cls_mma]

/-- **A QK commit of block `r`**: a commit to `qkDone s` of CTA `c` is the commit of a block `r`
below the CTA's block count with slot `s`, after `r / 2` commits to the slot and `24 r + 16` MMA
issues; the lane's QK MMA `15` of the block, the `24 r + 15`-th issue, is before it. -/
theorem mma_qkCommit {i pc c : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = mbarLoc L c (.qkDone s)) :
    c = y / L.block ∧ ∃ r, r < blocksOf P L c ∧ s = slot2 r ∧
      ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L c (.qkDone s))) = r / 2 ∧
      mmaIssues ((X.tr y).take i) = 24 * r + 16 ∧
      ∃ x < i, ∃ pcx sx acc mask, X.get (y, x) = some ⟨pcx, .tc (.mma 400 sx acc mask)⟩ ∧
        MbarRow.MmaAt L y pcx ∧ mmaIssues ((X.tr y).take x) = 24 * r + 15 := by
  obtain ⟨hc, r, hr, hs, hall, hn⟩ := (commit_block hp hX hFw he).1 c s hm
  have hw := mma_commit_warp hp hX hFw he
  rw [issues_eq] at hn
  obtain ⟨x, hxi, pcx, b, sx, acc, mask, hx, hat, hcx⟩ := mma_nth (X := X) hw
    (i := i) (n := 24 * r + 15) (by rw [issues_eq]; omega)
  rw [issues_eq] at hcx
  obtain ⟨r', k, ⟨hk, hb, hc'⟩ | ⟨hk, hb, hc'⟩⟩ := mma_nth_site hp hX hFw hx hat
  · rw [issues_eq] at hc'
    subst hb
    exact ⟨hc, r, hr, hs, hall, hn, x, hxi, pcx, sx, acc, mask, hx, hat, hcx⟩
  · rw [issues_eq] at hc'
    omega

/-- **A PV commit of block `r`**: a commit to `svDone s` of CTA `c` is the commit of a block `r`
below the CTA's block count with slot `s`, after `ringUses 2 b r` commits to each slot `b` and
`24 r + 24` MMA issues. -/
theorem mma_svCommit {i pc c : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = mbarLoc L c (.svDone s)) :
    c = y / L.block ∧ ∃ r, r < blocksOf P L c ∧ s = slot2 r ∧ (∀ b : Fin 2,
      ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L c (.svDone b))) =
        ringUses 2 b.val r) ∧ mmaIssues ((X.tr y).take i) = 24 * r + 24 := by
  obtain ⟨hc, r, hr, hs, hall, hn⟩ := (commit_block hp hX hFw he).2 c s hm
  rw [issues_eq] at hn
  exact ⟨hc, r, hr, hs, hall, hn⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
