-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit
import Lemmas.Flow.CommitHit

@[expose] public section

/-! # A commit notifies the mbarrier it names

The trace-level commit-target fact `Notify.Obj.blocker` consumes (its `htgt`): every
`tcgen05.commit` of the code is unmasked (a static scan, evaluated once), so it resolves with the
rank bit of its addressed mbarrier (`fires_commit_unmasked`), and the launch's clusters have one
CTA, so that rank selects the mbarrier itself (`resolve_self_hit`). The MMA lane's commits (pcs
1982, 2104, 2150) are all the code's commits; the statement holds of every thread's. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private def unmasked : Op → Bool
  | .tcCommit _ _ _ mask => mask.isNone
  | _ => true

private theorem unmasked_code : kernel.code.all (fun i => unmasked i.op) = true := by
  decide +kernel

/-- A commit of the code resolves with the rank bit of its addressed mbarrier. -/
private theorem commit_resolve (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {pc : Nat}
    {sp : TcCommit.Spec} (he : X.get i = some ⟨pc, .tc (.commit sp)⟩) :
    ∃ g mb, TcCommit.resolve L g (i.1 / L.block) mb
      (BitVec.ofNat 16 (2 ^ L.rankOfCta mb.cta)) = some sp := by
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hf
  have hop : commitOp ins.op = true := by
    cases h : commitOp ins.op
    · exact (fires_notCommit (eventTmpl_notCommit (commitOp_ne h)) hf sp rfl).elim
    · rfl
  have hu := List.all_eq_true.mp unmasked_code ins (List.mem_of_getElem? hc)
  cases hi : ins.op <;> simp only [hi, commitOp, Bool.false_eq_true] at hop
  rename_i group base off mask
  simp only [hi, unmasked, Option.isNone_iff_eq_none] at hu
  subst hu
  rw [hi] at hf
  obtain ⟨mb, hr⟩ := fires_commit_unmasked hf rfl
  exact ⟨group, mb, hr⟩

/-- **A commit naming `l` targets `l`** (the `htgt` input of `Notify.Obj.blocker`). -/
theorem mma_commitHit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {y i pc : Nat} {sp : TcCommit.Spec} {l : Loc}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hl : sp.mbar = l) :
    ∃ rank, TcCommit.target sp rank = some l := by
  subst hl
  obtain ⟨_, mb, hr⟩ := commit_resolve hX he
  refine resolve_self_hit hr ?_
  simp [Launch.clusterSizeOf, Launch.clusterSizeAt, hp.clusterPlaces, gridPlace, Dim3.prod]

/-- **A commit's cluster is one CTA.** -/
theorem mma_commitOne (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {y i pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) : sp.clusterSize = 1 := by
  obtain ⟨_, mb, hr⟩ := commit_resolve hX he
  unfold TcCommit.resolve at hr
  split_ifs at hr
  cases hr
  simp [Launch.clusterSizeOf, Launch.clusterSizeAt, hp.clusterPlaces, gridPlace, Dim3.prod]

/-- **A thread's commits target the same ranks** (the `hprev` input of `Sched.commit_stepsQ`):
each commit's cluster is one CTA, so a commit that targets a rank targets rank zero, and every
commit targets rank zero (`mma_commitHit`). -/
theorem mma_commitPrev (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {g j j' pc pc' : Nat} {sp sp' : TcCommit.Spec} {rank : Fin 16} {l : Loc}
    (he : X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩)
    (he' : X.get (g, j') = some ⟨pc', .tc (.commit sp')⟩)
    (hit : TcCommit.target sp' rank = some l) :
    ∃ l', TcCommit.target sp rank = some l' := by
  obtain ⟨r, hr⟩ := mma_commitHit hp hX he rfl
  have h1 := mma_commitOne hp hX he
  have h2 := mma_commitOne hp hX he'
  have hr1 : r.val < 1 := by
    unfold TcCommit.target at hr
    split_ifs at hr with h
    omega
  have hk1 : rank.val < 1 := by
    unfold TcCommit.target at hit
    split_ifs at hit with h
    omega
  obtain rfl : r = rank := Fin.ext (by omega)
  exact ⟨_, hr⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
