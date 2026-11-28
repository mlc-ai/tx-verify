-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Kernel.Goals
public import Lemmas.Flow.NotMatrix
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.CommitTarget
public import Lemmas.Execution.ShapeExecution
public import Lemmas.Cluster.Unit

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

/-- All instructions that specify a Tensor Core CTA group use the same group. -/
theorem tcGroupUniform : kernel.TcGroupUniform := by
  unfold Kernel.TcGroupUniform
  decide +kernel

private theorem noMatrixCode : kernel.code.all (fun ins => !matrixOp ins.op) = true := by
  decide +kernel

/-- The frozen kernel has no warp-level matrix events. -/
theorem noMatrixEvent {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {e : Event}
    (he : X.get i = some e) : isMatrix e = false :=
  no_matrix_of_code hX noMatrixCode he

/-- The kernel issues CTA-group tensor MMAs and no warp matrix instructions. -/
theorem noMatrixUnsafe {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) : ¬ MatrixUnsafe l A X :=
  not_matrixUnsafe_of_none l (fun _ _ h => noMatrixEvent hX h)

private theorem noClusterCode : kernel.code.all (fun ins => !clusterOp ins.op) = true := by
  decide +kernel

theorem noClusterEvent {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {pc : Nat} {op : ClusterOp}
    (he : X.get i = some ⟨pc, .cluster op⟩) : False :=
  no_kind_of_code hX clusterOp (fun k => ∃ op, k = .cluster op)
    (fun _ ⟨_, h⟩ => by cases h)
    (fun hf ⟨_, hk⟩ => by simp [fires_cluster_op hf hk, clusterOp])
    noClusterCode he ⟨op, rfl⟩

/-- An exit record can only fail with a malformed thread and no cluster collective is issued. -/
theorem noClusterFault {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) : ¬ ClusterFault l X := by
  rintro ⟨c, _, s, _, record, err, hsrc, _, hperform, herr⟩
  cases record with
  | exit =>
    simp only [ClusterBarrier.Record.perform, ClusterBarrier.perform] at hperform
    split at hperform
    · cases hperform
      cases herr
    · cases hperform
  | arrival cta warp release lanes =>
    cases lanes with
    | nil =>
      simp only [ClusterBarrier.Record.perform, List.map_nil, List.any_nil, Bool.false_eq_true,
        ↓reduceIte, ClusterBarrier.performAll] at hperform
      split at hperform <;> cases hperform
      cases herr
    | cons pair rest =>
      obtain ⟨_, _, pc, aligned, he⟩ := hsrc pair (by simp)
      exact noClusterEvent hX he
  | wait cta warp lanes =>
    cases lanes with
    | nil =>
      simp only [ClusterBarrier.Record.perform, List.map_nil, ClusterBarrier.performAll] at hperform
      split at hperform <;> cases hperform
      cases herr
    | cons pair rest =>
      obtain ⟨_, _, pc, aligned, he⟩ := hsrc pair (by simp)
      exact noClusterEvent hX he

private def singleCommitOp : Op → Bool
  | .tcCommit group .. => group == .one
  | _ => true

private theorem singleCommitCode : kernel.code.all (fun i => singleCommitOp i.op) = true := by
  decide +kernel

/-- The resolved commit uses the frozen single-CTA qualifier. -/
theorem singleCommitResolved {A : List Assumption} {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l kernel A m X) {i : EvId} {s : TcCommit.Spec}
    (hi : X.Commit i s) :
    s.group = .one ∧ TcCommit.resolve l s.group (i.1 / l.block) s.mbar s.mask = some s := by
  obtain ⟨pc, he⟩ := hi
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hCode, hf⟩
  · cases hf
  have hCommit : commitOp ins.op = true := by
    cases h : commitOp ins.op
    · exact (fires_notCommit (eventTmpl_notCommit (commitOp_ne h)) hf s rfl).elim
    · rfl
  have hSingle := List.all_eq_true.mp singleCommitCode ins (List.mem_of_getElem? hCode)
  cases hOp : ins.op <;> simp only [hOp, commitOp, Bool.false_eq_true] at hCommit
  rename_i group base off mask
  simp only [hOp, singleCommitOp, beq_iff_eq] at hSingle
  rw [hOp, hSingle] at hf
  obtain ⟨bar, bits, hResolve⟩ := tcCommit_resolves hf rfl
  unfold TcCommit.resolve at hResolve
  split at hResolve
  · cases hResolve
    exact ⟨rfl, ite_eq_left ‹_›⟩
  · cases hResolve

/-- A Tensor Core commit resolves to the issuing CTA, which belongs to its own one-CTA group. -/
theorem noTcCommitUnsafe {p : Params} {l : Launch} {m : Mem0} {A : List Assumption}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel A m X) :
    ¬ TcCommitUnsafe l X := by
  rintro ⟨i, s, hi, hBad⟩
  obtain ⟨pc, he⟩ := hi
  have hg := PTX.Proof.event_thread_lt hX he
  have hCTA : i.1 / l.block < l.grid := by
    rw [Launch.threads, hp.block] at hg
    rw [hp.block]
    omega
  obtain ⟨hGroup, hResolve⟩ := singleCommitResolved hX ⟨pc, he⟩
  apply hBad
  refine ⟨hg, hResolve, ?_⟩
  have hs : ∀ k, (l.clusterPlaces k).shape = ⟨1, 1, 1⟩ := by
    intro k
    rw [hp.clusterPlaces, hp.clusterNctaid]
    rfl
  have hc : i.1 / l.block < l.nclusters := hp.nclusters ▸ hCTA
  rw [hGroup, Launch.ctaGroup_one, Launch.rankOfCta_unit hs hc, Launch.peerCta_unit hs hc hCTA]
  simp

end PTX.Kernels.InklingRelDecode.Proof.Lib
