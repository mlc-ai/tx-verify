-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
public import Lemmas.Flow.Polls
public import Lemmas.Flow.NotTensor
public import Lemmas.Flow.NotCommit
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CommitSites
import Lemmas.Tensor.LoadBox
import Lemmas.Tensor.LoadBoxOnto

@[expose] public section

/-! # The MMA lane's counts on the query's objects

For a lane `y` of warp 4 (the MMA lane, or a lane that lost the election and fires none of these
events), over its whole trace: at most eight tensor copies to `bar_q_tma` (`mma_issues_le`), at
most one arrival on it (`mma_arrivals_le`) and at most one commit to `bar_q_utccp`
(`mma_commits_le`). At its next event, a wait on `bar_q_tma` at an MMA pc, it has made its arrival
and its eight copies (`mma_tmaPre`); at a wait on `bar_q_utccp` at an MMA pc it has no successful
poll of it and has made its one commit to it (`mma_qUt_wait`). A lane with an event of the MMA
code from the arrival on (pc 1929) that exits has committed to `bar_q_utccp`
(`mma_commitExit`). Its commit of use `u` to `svDone s` follows `u + 1` successful polls of
`dequantReady s` (`mma_svArr`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

private theorem loc_ne {f f' : MbarFam} (h : f ≠ f') : loc L y f ≠ loc L y f' := by
  intro he
  simp only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at he
  exact h (MbarFam.off_inj he)

/-- A count over a list is at most `B` when each counted element has fewer than `B` before it. -/
private theorem countP_le_of_each {l : List Event} {p : Event → Bool} {B : Nat}
    (h : ∀ j f, l[j]? = some f → p f = true → (l.take j).countP p + 1 ≤ B) :
    l.countP p ≤ B := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    rw [List.countP_append]
    by_cases hx : p x = true
    · have := h l.length x (by simp) hx
      rw [List.take_left' rfl] at this
      simpa [hx] using this
    · have := ih fun j f hj hp => by
        have hjl : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
        have := h j f (by rw [List.getElem?_append_left hjl]; exact hj) hp
        rwa [List.take_append_of_le_length (by omega)] at this
      simpa [hx] using this

/-- The two names of a commit addressing `l` are one predicate. -/
theorem flow_commitsTo (l : Loc) : PTX.Flow.commitsTo l = MbarRow.commitsTo l := by
  funext f
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | tc t => cases t <;> rfl
  | _ => rfl

/-- **A commit is a warp-4 lane's** (the commits are at MMA pcs, `commit_pcs`). -/
theorem mma_commit_warp (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) : warp L y = 4 := by
  have h := commit_pcs hX he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨-, -, -, -, hw⟩ := mma_at hp hX hFw he (fun _ h => by cases h)
    ⟨by simp only; omega, by simp only; omega⟩
  exact hw

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hw : warp L y = 4)
include hp hX hFw hw

private theorem role {j : Nat} {f : Event} (hf : X.get (y, j) = some f) (hk : PollCommitK f.kind) :
    1850 ≤ f.pc ∧ f.pc < 2162 := by
  have := lane4_inRole hp hX hFw hw hf hk
  simp only [Mma.inRole, decide_eq_true_eq] at this
  omega

private theorem issues_eq (k : Nat) :
    ((X.tr y).take k).countP (issuesTo (loc L y .qTma)) =
      ((X.tr y).take k).countP (Mma.cls .tma) := by
  refine List.countP_congr fun f hf => ?_
  obtain ⟨j, hj⟩ := get_of_mem_take hf
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | tensorIssue a s =>
    have hr := role hp hX hFw hw hj (.inr (.inr (.inl ⟨a, s, rfl⟩)))
    have hin := lane4_inRole hp hX hFw hw hj (.inr (.inr (.inl ⟨a, s, rfl⟩)))
    obtain ⟨d, -, hev, hl, -⟩ := mma_at hp hX hFw hj (fun _ h => by cases h) hr
    obtain ⟨i, -, hm⟩ := Mma.ev_tensor hl hev
    simp only [Mma.cls, hin, Mma.kindOf, issuesTo, hm, Mma.qTma_loc hp]
    simp
  | tc t => cases t <;> simp [issuesTo, Mma.cls, Mma.kindOf]
  | wait l q ok a sc => cases ok <;> simp [issuesTo, Mma.cls, Mma.kindOf]
  | _ => simp [issuesTo, Mma.cls, Mma.kindOf]

private theorem arrivals_eq (k : Nat) (l : Loc) :
    arrivals l ((X.tr y).take k) = ((X.tr y).take k).countP (Mma.cls (.arrive l)) := by
  refine List.countP_congr fun f hf => ?_
  obtain ⟨j, hj⟩ := get_of_mem_take hf
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | arrive l' tx c r sc =>
    have hin := lane4_inRole hp hX hFw hw hj (.inr (.inr (.inr ⟨l', tx, c, r, sc, rfl⟩)))
    simp only [Mma.cls, hin, Mma.kindOf, arrivesOn, sourceArrive]
    simp
  | tc t => cases t <;> simp [arrivesOn, sourceArrive, Mma.cls, Mma.kindOf]
  | wait l q ok a sc => cases ok <;> simp [arrivesOn, sourceArrive, Mma.cls, Mma.kindOf]
  | _ => simp [arrivesOn, sourceArrive, Mma.cls, Mma.kindOf]

/-- **At most eight tensor copies to `bar_q_tma`.** -/
theorem mma_issues_le : (X.tr y).countP (issuesTo (loc L y .qTma)) ≤ 8 := by
  refine countP_le_of_each fun j f hj hpf => ?_
  rw [issues_eq hp hX hFw hw j]
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | tensorIssue a s =>
    have hr := role hp hX hFw hw hj (.inr (.inr (.inl ⟨a, s, rfl⟩)))
    obtain ⟨d, hR, hev, hl, -⟩ := mma_at hp hX hFw hj (fun _ h => by cases h) hr
    obtain ⟨i, hs, -⟩ := Mma.ev_tensor hl hev
    have hc := Mma.pro_cnt (hR (take_noUb hX hj)) (by rw [hs]; exact ⟨rfl, by simp, by simp⟩)
      (c := .tma) (by simp)
    rw [hc, hs]
    have := i.isLt
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.pro]
  | tc t => cases t <;> simp [issuesTo] at hpf
  | wait l q ok a sc => simp [issuesTo] at hpf
  | _ => simp [issuesTo] at hpf

/-- **At most one arrival on any object.** -/
theorem mma_arrivals_le (l : Loc) : arrivals l (X.tr y) ≤ 1 := by
  refine countP_le_of_each fun j f hj hpf => ?_
  have h := arrivals_eq hp hX hFw hw j l
  simp only [arrivals] at h
  rw [h]
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | arrive l' tx c r sc =>
    have hr := role hp hX hFw hw hj (.inr (.inr (.inr ⟨l', tx, c, r, sc, rfl⟩)))
    obtain ⟨d, hR, hev, hl, -⟩ := mma_at hp hX hFw hj (fun _ h => by cases h) hr
    obtain ⟨hs, -⟩ := Mma.ev_arrive hl hev
    have hc := Mma.pro_cnt (hR (take_noUb hX hj)) (by rw [hs]; exact ⟨rfl, by simp, by simp⟩)
      (c := .arrive l) (by simp)
    rw [hc, hs]
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.pro]
  | tc t => cases t <;> simp [arrivesOn, sourceArrive] at hpf
  | wait l q ok a sc => simp [arrivesOn, sourceArrive] at hpf
  | _ => simp [arrivesOn, sourceArrive] at hpf

/-- **At most one commit to `bar_q_utccp`.** -/
theorem mma_commits_le : (X.tr y).countP (PTX.Flow.commitsTo (loc L y .qUtccp)) ≤ 1 := by
  rw [flow_commitsTo]
  refine countP_le_of_each fun j f hj hpf => ?_
  rw [lane4_commits hp hX hFw hw j]
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | tc t =>
    cases t with
    | commit s =>
      have hr := role hp hX hFw hw hj (.inr (.inl ⟨s, rfl⟩))
      obtain ⟨d, hR, hev, hl, -⟩ := mma_at hp hX hFw hj (fun _ h => by cases h) hr
      have hc := hR (take_noUb hX hj)
      simp only [MbarRow.commitsTo, decide_eq_true_eq] at hpf
      rcases Mma.ev_commit hl hev with ⟨hs, -⟩ | ⟨hs, hm⟩ | ⟨hs, hm⟩
      · rw [Mma.pro_cnt hc (by rw [hs]; exact ⟨rfl, by simp, by simp⟩) (by simp), hs]
        simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.pro, Mma.useAt, ringUses]
      · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, -⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
        rw [hpha] at hm
        replace hm := hm.trans (Mma.qk_loc hp (slot2 d.cnt.toNat))
        exact absurd (hm.symm.trans hpf) (loc_ne (by simp))
      · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, -⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
        rw [hpha] at hm
        replace hm := hm.trans (Mma.sv_loc hp (slot2 d.cnt.toNat))
        exact absurd (hm.symm.trans hpf) (loc_ne (by simp))
    | _ => simp [MbarRow.commitsTo] at hpf
  | wait l q ok a sc => simp [MbarRow.commitsTo] at hpf
  | _ => simp [MbarRow.commitsTo] at hpf

/-- **The lane's commit of use `u` to `svDone s` follows `u + 1` successful polls of
`dequantReady s`** (`DequantInputs.mmaSvArr`). -/
theorem mma_svArr {i pc c : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = mbarLoc L c (.svDone s)) :
    ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L c (.svDone s))) <
      okPolls (mbarLoc L c (.dequantReady s)) ((X.tr y).take i) := by
  have hr := role hp hX hFw hw he (.inr (.inl ⟨sp, rfl⟩))
  obtain ⟨d, hR, hev, hl, -⟩ := mma_at hp hX hFw he (fun _ h => by cases h) hr
  have hc := hR (take_noUb hX he)
  rcases Mma.ev_commit hl hev with ⟨hs, hm'⟩ | ⟨hs, hm'⟩ | ⟨hs, hm'⟩
  · cases (Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.qUt_loc hp)))).2
  · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, -⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hpha] at hm'
    cases (Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.qk_loc hp (slot2 d.cnt.toNat))))).2
  · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, hn⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hpha] at hm'
    obtain ⟨rfl, hf⟩ :=
      Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.sv_loc hp (slot2 d.cnt.toNat))))
    cases MbarFam.svDone.inj hf
    have hC := lane4_commits hp hX hFw hw i (loc L y (.svDone (slot2 d.cnt.toNat)))
    have hP := lane4_okPolls hp hX hFw hw i (loc L y (.dequantReady (slot2 d.cnt.toNat)))
    rw [hn _ (by simp), Mma.cnt_sv hp] at hC
    rw [hn _ (by simp), Mma.cnt_ready hp] at hP
    simp only [loc] at hC hP
    rw [flow_commitsTo, hC, hP, hs]
    simp [Mma.useAt, Mma.Site.idx, Mma.ind, slot2]

/-- **The lane's commit of use `u` to `qkDone s` follows `u` successful polls of `soReady s`**: at
its block's commit to `qk_done` the lane has polled `so_ready` once per earlier use of the slot. -/
theorem mma_qkArr {i pc c : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = mbarLoc L c (.qkDone s)) :
    ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L c (.qkDone s))) =
      okPolls (mbarLoc L c (.soReady s)) ((X.tr y).take i) := by
  have hr := role hp hX hFw hw he (.inr (.inl ⟨sp, rfl⟩))
  obtain ⟨d, hR, hev, hl, -⟩ := mma_at hp hX hFw he (fun _ h => by cases h) hr
  have hc := hR (take_noUb hX he)
  rcases Mma.ev_commit hl hev with ⟨hs, hm'⟩ | ⟨hs, hm'⟩ | ⟨hs, hm'⟩
  · cases (Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.qUt_loc hp)))).2
  · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, hn⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hpha] at hm'
    obtain ⟨rfl, hf⟩ :=
      Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.qk_loc hp (slot2 d.cnt.toNat))))
    cases MbarFam.qkDone.inj hf
    have hC := lane4_commits hp hX hFw hw i (loc L y (.qkDone (slot2 d.cnt.toNat)))
    have hP := lane4_okPolls hp hX hFw hw i (loc L y (.soReady (slot2 d.cnt.toNat)))
    rw [hn _ (by simp), Mma.cnt_qk hp] at hC
    rw [hn _ (by simp), Mma.cnt_so hp] at hP
    simp only [loc] at hC hP
    rw [flow_commitsTo, hC, hP, hs]
    simp [Mma.useAt, Mma.Site.idx, Mma.ind, slot2]
  · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, -⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hpha] at hm'
    cases (Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.sv_loc hp (slot2 d.cnt.toNat))))).2

/-- **The lane's commit of use `u` to `qkDone s` follows `u + 1` successful polls of
`dequantReady s`**: the block's QK follows the poll of the block's ready wait. -/
theorem mma_qkDq {i pc c : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = mbarLoc L c (.qkDone s)) :
    ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L c (.qkDone s))) <
      okPolls (mbarLoc L c (.dequantReady s)) ((X.tr y).take i) := by
  have hr := role hp hX hFw hw he (.inr (.inl ⟨sp, rfl⟩))
  obtain ⟨d, hR, hev, hl, -⟩ := mma_at hp hX hFw he (fun _ h => by cases h) hr
  have hc := hR (take_noUb hX he)
  rcases Mma.ev_commit hl hev with ⟨hs, hm'⟩ | ⟨hs, hm'⟩ | ⟨hs, hm'⟩
  · cases (Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.qUt_loc hp)))).2
  · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, hn⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hpha] at hm'
    obtain ⟨rfl, hf⟩ :=
      Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.qk_loc hp (slot2 d.cnt.toNat))))
    cases MbarFam.qkDone.inj hf
    have hC := lane4_commits hp hX hFw hw i (loc L y (.qkDone (slot2 d.cnt.toNat)))
    have hP := lane4_okPolls hp hX hFw hw i (loc L y (.dequantReady (slot2 d.cnt.toNat)))
    rw [hn _ (by simp), Mma.cnt_qk hp] at hC
    rw [hn _ (by simp), Mma.cnt_ready hp] at hP
    simp only [loc] at hC hP
    rw [flow_commitsTo, hC, hP, hs]
    simp [Mma.useAt, Mma.Site.idx, Mma.ind, slot2]
  · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, -⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hpha] at hm'
    cases (Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.sv_loc hp (slot2 d.cnt.toNat))))).2

/-- **At its wait on `bar_q_tma` the lane has made its arrival and its eight copies.** -/
theorem mma_tmaPre {pc p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X y ⟨pc, .wait (loc L y .qTma) p ok acq sc⟩)
    (hr : 1850 ≤ pc ∧ pc < 2162) :
    arrivals (loc L y .qTma) (X.tr y) = 1 ∧
      (X.tr y).countP (issuesTo (loc L y .qTma)) = 8 := by
  obtain ⟨d, hR, hev, hl, hu⟩ := next_mma hp hFw hn (fun _ h => by cases h) hr
  have hc := hR hu
  have ha := arrivals_eq hp hX hFw hw (X.tr y).length (loc L y .qTma)
  have hi := issues_eq hp hX hFw hw (X.tr y).length
  rw [List.take_length] at ha hi
  rw [ha, hi]
  rcases Mma.ev_wait hl hev with ⟨hs, -⟩ | ⟨-, hm⟩ | ⟨hs, hm⟩ | ⟨hs, hm⟩
  · rw [Mma.pro_cnt hc (by rw [hs]; exact ⟨rfl, by simp, by simp⟩) (by simp),
      Mma.pro_cnt hc (by rw [hs]; exact ⟨rfl, by simp, by simp⟩) (by simp), hs]
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.pro, Mma.qTma_eq, Mma.qTma_loc hp]
  · rw [Mma.qUt_loc hp] at hm
    exact absurd hm (loc_ne (by simp))
  · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, -⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hpha] at hm
    replace hm := hm.trans (Mma.ready_loc hp (slot2 d.cnt.toNat))
    exact absurd hm (loc_ne (by simp))
  · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, -⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hpha] at hm
    replace hm := hm.trans (Mma.so_loc hp (slot2 d.cnt.toNat))
    exact absurd hm (loc_ne (by simp))

/-- **At its wait on `bar_q_utccp` the lane has no successful poll of it and has committed to
it once.** -/
theorem mma_qUt_wait {pc p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X y ⟨pc, .wait (loc L y .qUtccp) p ok acq sc⟩)
    (hr : 1850 ≤ pc ∧ pc < 2162) :
    okPolls (loc L y .qUtccp) (X.tr y) = 0 ∧
      (X.tr y).countP (PTX.Flow.commitsTo (loc L y .qUtccp)) = 1 := by
  obtain ⟨d, hR, hev, hl, hu⟩ := next_mma hp hFw hn (fun _ h => by cases h) hr
  have hc := hR hu
  have ho := lane4_okPolls hp hX hFw hw (X.tr y).length (loc L y .qUtccp)
  have hm := lane4_commits hp hX hFw hw (X.tr y).length (loc L y .qUtccp)
  rw [List.take_length] at ho hm
  rw [ho, flow_commitsTo, hm]
  rcases Mma.ev_wait hl hev with ⟨-, hm⟩ | ⟨hs, -⟩ | ⟨hs, hm⟩ | ⟨hs, hm⟩
  · rw [Mma.qTma_loc hp] at hm
    exact absurd hm (loc_ne (by simp))
  · rw [Mma.pro_cnt hc (by rw [hs]; exact ⟨rfl, by simp, by simp⟩) (by simp),
      Mma.pro_cnt hc (by rw [hs]; exact ⟨rfl, by simp, by simp⟩) (by simp), hs]
    have hq : loc L y .qUtccp ≠ (Mma.objs L y).qTma := by
      rw [Mma.qTma_eq, Mma.qTma_loc hp]; exact loc_ne (by simp)
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.pro, Mma.qUt_eq, Mma.qUt_loc hp, hq,
      Mma.useAt, ringUses]
  · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, -⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hpha] at hm
    replace hm := hm.trans (Mma.ready_loc hp (slot2 d.cnt.toNat))
    exact absurd hm (loc_ne (by simp))
  · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, -⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hpha] at hm
    replace hm := hm.trans (Mma.so_loc hp (slot2 d.cnt.toNat))
    exact absurd hm (loc_ne (by simp))

/-- **A lane with an event of the MMA code from the arrival on that exits has committed to
`bar_q_utccp`.** -/
theorem mma_commitExit {j k pc : Nat} {e0 : Event} (he0 : X.get (y, j) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hr0 : 1929 ≤ e0.pc ∧ e0.pc < 2162) (hjk : j < k)
    (hx : X.get (y, k) = some ⟨pc, .exit⟩) :
    1 ≤ (X.tr y).countP (PTX.Flow.commitsTo (loc L y .qUtccp)) := by
  obtain ⟨d0, hR0, hE0, hP0⟩ := post_at hp hX hFw he0 hu0 ⟨by omega, hr0.2⟩ (Nat.le_refl j) he0 hu0
  have h8 := Mma.tma_eight (hR0 (take_noUb hX he0)) hP0.2 (by rw [← hE0.1]; omega)
    (by rw [← hE0.1]; omega)
  obtain ⟨dk, hRk, hEk, hPk⟩ := post_at hp hX hFw he0 hu0 ⟨by omega, hr0.2⟩ hjk.le hx
    (fun _ h => by cases h)
  have hs : dk.site = .exit := by
    obtain ⟨-, hk⟩ := hEk
    obtain ⟨-, hl⟩ := hPk
    obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := dk
    cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hk ⊢
    case leave i => exact hl i rfl
  have hmono : ((X.tr y).take j).countP (Mma.cls .tma) ≤
      ((X.tr y).take k).countP (Mma.cls .tma) :=
    (List.take_sublist_take_left hjk.le).countP_le
  rcases Mma.exit_cnt (hRk (take_noUb hX hx)) hs with hc | hc
  · rw [hc .tma (by simp)] at hmono
    have h0 : Mma.cntAt (Mma.objs L y) 1 0 0 false .tma = 0 := by
      simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt]
    omega
  · have h1 := hc (.commit (loc L y .qUtccp)) (by simp)
    have hq : loc L y .qUtccp = (Mma.objs L y).qUt := by rw [Mma.qUt_eq, Mma.qUt_loc hp]
    have h2 : 1 ≤ Mma.cntAt (Mma.objs L y) 31 (Mma.rounds dk.l0 dk.l1) 0 true
        (.commit (loc L y .qUtccp)) := by
      simp only [Mma.cntAt, Mma.proCnt, hq, Mma.ind]
      simp
    rw [flow_commitsTo]
    have h3 : ((X.tr y).take k).countP (MbarRow.commitsTo (loc L y .qUtccp)) ≤
        (X.tr y).countP (MbarRow.commitsTo (loc L y .qUtccp)) :=
      (List.take_sublist k (X.tr y)).countP_le
    rw [lane4_commits hp hX hFw hw k] at h3
    omega

/-- **A query load of the MMA lane writes its own 8192 bytes of the query tile**: the load with
`a` earlier loads to `bar_q_tma` writes only into `[S + 8192 a, S + 8192 (a + 1))` of its CTA,
`S` the shared base. -/
theorem mma_qLoad_range {i pc al : Nat} {s : TensorCopy.Spec}
    (he : X.get (y, i) = some ⟨pc, .tensorIssue al s⟩) :
    1853 < pc ∧ s.mbar = loc L y .qTma ∧ ∃ a < 8,
      ((X.tr y).take i).countP (issuesTo (loc L y .qTma)) = a ∧
      ∀ {x y' j : Nat} {l : Loc}, TensorCopy.writeLoc s x y' j = some l →
        l.space = .shared ∧ l.cta = y / L.block ∧ L.sharedBase + 8192 * a ≤ l.addr ∧
          l.addr < L.sharedBase + 8192 * a + 8192 := by
  have hr := role hp hX hFw hw he (.inr (.inr (.inl ⟨al, s, rfl⟩)))
  obtain ⟨d, hR, ⟨hpc, hE⟩, hl, -⟩ := mma_at hp hX hFw he (fun _ h => by cases h) hr
  have hc := hR (take_noUb hX he)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp only [Mma.EvK] at hE
  case qLoad i =>
    have hpc' : 1853 < pc := by
      simp only [Mma.Site.pc] at hpc
      have hi := i.isLt
      rw [hpc]
      fin_cases i <;> simp
    rcases hE with ⟨a', s', hk', hmb, -, hsb, ⟨h0, hr', hf, hsw⟩, bb, hb, hmap⟩ | ⟨f, hf⟩
    · cases hk'
      refine ⟨hpc', hmb.trans (Mma.qTma_loc hp), i.val, i.isLt, ?_, fun {x y' j l} hl => ?_⟩
      · rw [issues_eq hp hX hFw hw,
          Mma.pro_cnt hc (by exact ⟨rfl, by simp, by simp⟩) (c := .tma) (by simp)]
        simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.pro]
      · obtain ⟨h1, h2, h3, h4⟩ := TensorCopy.writeLoc_b128_64 h0 hr' hf hsw hl
        rw [hsb] at h1 h2 h3 h4
        exact ⟨h1, h2, h3, by omega⟩
    · cases hf
  case leave i => exact absurd rfl (hl i)
  all_goals simp [Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE

/-- **A query load of the MMA lane writes every byte of its own 8192 bytes of the query tile**:
the load with `a` earlier loads to `bar_q_tma` has, for each byte of
`[S + 8192 a, S + 8192 (a + 1))` of its CTA, a slot whose location it is. -/
theorem mma_qLoad_onto {i pc al : Nat} {s : TensorCopy.Spec}
    (he : X.get (y, i) = some ⟨pc, .tensorIssue al s⟩) :
    ∃ a < 8, ((X.tr y).take i).countP (issuesTo (loc L y .qTma)) = a ∧
      ∀ {l : Loc}, l.space = .shared → l.cta = y / L.block → L.sharedBase + 8192 * a ≤ l.addr →
        l.addr < L.sharedBase + 8192 * a + 8192 →
          ∃ x y' j, TensorCopy.writeLoc s x y' j = some l := by
  have hr := role hp hX hFw hw he (.inr (.inr (.inl ⟨al, s, rfl⟩)))
  obtain ⟨d, hR, ⟨hpc, hE⟩, hl, -⟩ := mma_at hp hX hFw he (fun _ h => by cases h) hr
  have hc := hR (take_noUb hX he)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp only [Mma.EvK] at hE
  case qLoad i =>
    rcases hE with ⟨a', s', hk', hmb, -, hsb, ⟨h0, hr', hf, hsw⟩, bb, hb, hmap⟩ | ⟨f, hf⟩
    · cases hk'
      refine ⟨i.val, i.isLt, ?_, fun {l} h1 h2 h3 h4 => ?_⟩
      · rw [issues_eq hp hX hFw hw,
          Mma.pro_cnt hc (by exact ⟨rfl, by simp, by simp⟩) (c := .tma) (by simp)]
        simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.pro]
      · refine TensorCopy.writeLoc_b128_64_onto h0 hr' hf hsw ?_ ?_ ?_ ?_ <;> rw [hsb] <;>
          assumption
    · cases hf
  case leave i => exact absurd rfl (hl i)
  all_goals simp [Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
