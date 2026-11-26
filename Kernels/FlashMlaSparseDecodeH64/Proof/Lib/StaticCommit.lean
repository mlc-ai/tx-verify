-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Clc.ClcExecution
public import Lemmas.Execution.ShapeExecution
public import Lemmas.Flow.CommitTarget
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.NotCommit
public import Lemmas.Flow.NotMatrix
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.StoreValid
public import Lemmas.Flow.WaitLoopPcs
public import Lemmas.Flow.WarpUniform
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The classes of `Unsafe` the decoded code excludes: commits and stores

Every Tensor Core commit is a one-CTA commit of a one-CTA cluster (`noTcCommitUnsafe`), and every
tensor store a plain tile write with no bulk copy at all (`noTensorStoreUnsafe`): static scans of
the decoded program, each evaluated once. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

/-! ### Tensor Core commits -/

set_option maxRecDepth 100000 in
private theorem noPairCommits :
    OpPcsFast kernel.code (fun op => match op with
      | .tcCommit .two .. => true
      | _ => false) [] = true := by
  decide +kernel

/-- **ERR-TC-COMMIT**: every commit is a one-CTA commit, and the launch's clusters have one CTA,
so it resolves to an existing group of the issuing CTA. -/
theorem noTcCommitUnsafe {P : Params} (hpre : Pre P l m) (hX : Consistent l kernel A m X) :
    ¬ TcCommitUnsafe l X := by
  rintro ⟨⟨g, i⟩, sp, ⟨site, he⟩, hbad⟩
  have hg := Frame.lt_of_get hX he
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hf
  cases hop : commitOp ins.op
  · exact (fires_notCommit (eventTmpl_notCommit (commitOp_ne hop)) hf sp rfl).elim
  · cases hi : ins.op <;> simp only [hi, commitOp, Bool.false_eq_true] at hop
    rename_i group base off mask
    cases group
    case two =>
      have h := OpPcsFast.mem noPairCommits hc (by rw [hi])
      exact List.not_mem_nil h
    case one =>
      rw [hi] at hf
      obtain ⟨b, bits, hr⟩ := tcCommit_resolves hf rfl
      have hsz (k : Nat) : l.clusterSizeAt k = 1 := by
        simp [Launch.clusterSizeAt, hpre.clusterPlaces, gridPlace, Dim3.prod]
      have hloc (n k c : Nat) : l.locate n k c = (k + c, 0) := by
        rw [Launch.locate_regular (fun k => by
          change l.clusterSizeAt k = l.clusterSize.val
          rw [hsz, hpre.clusterSize]), hpre.clusterSize, Nat.div_one, Nat.mod_one]
      have hstart (k : Nat) : l.clusterStart k = k := by
        induction k with
        | zero => rfl
        | succ k ih => rw [Launch.clusterStart, ih, hsz]
      unfold TcCommit.resolve at hr
      split at hr
      · rename_i hValid
        have hGrid : g / l.block < l.grid := hValid.2.1
        cases hr
        refine hbad ⟨hg, ?_, ?_⟩
        · simp [TcCommit.resolve, hValid]
        · simp [Launch.ctaGroup_one, Launch.peerCta, Launch.clusterOfCta, Launch.rankOfCta,
            Launch.clusterSizeOf, hloc, hstart, hsz, hGrid]
      · cases hr

/-! ### Tensor stores and bulk copies -/

private def plainTileStore : Op → Bool
  | .cpTensorStore _ _ _ _ _ .tile none => true
  | op => !tensorStoreOp op

private theorem plainTileStoreCode :
    kernel.code.all (fun i => plainTileStore i.op) = true := by
  decide +kernel

/-- Every issued tensor store resolves to a valid tile write without a reduction. -/
theorem tensorStoreForm (hX : Consistent l kernel A m X) {i : EvId} {addr : Nat}
    {s : TensorStore.Spec} (hi : X.TensorStoreIssue i addr s) :
    TensorStore.Valid (i.1 / l.block) s ∧ s.rows = none ∧ s.reduce = none := by
  obtain ⟨_, he⟩ := hi
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hCode, hf⟩
  · cases hf
  have hop := fires_tensorStore_op hf rfl
  have hs := List.all_eq_true.mp plainTileStoreCode ins (List.mem_of_getElem? hCode)
  cases hIns : ins.op <;> simp only [hIns, tensorStoreOp, Bool.false_eq_true] at hop
  case cpTensorStore map cs r off policy mode reduce =>
    cases mode <;> cases reduce <;> simp [hIns, plainTileStore, tensorStoreOp] at hs
    rw [hIns] at hf
    exact fires_cpTensorStore_form hf addr s rfl

private theorem noBulkCode : kernel.code.all (fun ins => !bulkOp ins.op) = true := by
  decide +kernel

/-- No bulk copy is issued. -/
theorem noCopy (hX : Consistent l kernel A m X) {i : EvId} {s : AsyncCopy.Spec}
    (hc : X.Copy i s) : False := by
  obtain ⟨_, he⟩ := hc
  exact no_kind_of_code hX bulkOp (fun k => ∃ s, k = .copy s)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulk_op hf hk) noBulkCode he ⟨_, rfl⟩

/-- **ERR-REDUCTION-NO-RULE**: every tensor store is a plain tile write and no bulk copy is
issued, so no reduction is performed. -/
theorem noTensorStoreUnsafe (hX : Consistent l kernel A m X) : ¬ TensorStoreUnsafe A X := by
  rintro (⟨i, o, red, _, _, ho, hRed, _⟩ | hCopy)
  · obtain ⟨⟨address, hi⟩, _⟩ := hX.store i o ho
    change o.spec.reduce = some red at hRed
    rw [(tensorStoreForm hX hi).2.2] at hRed
    cases hRed
  · exact TensorStore.not_copyReduceNoRule_of_none
      (fun _ _ hc _ => (noCopy hX hc).elim) hCopy

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
