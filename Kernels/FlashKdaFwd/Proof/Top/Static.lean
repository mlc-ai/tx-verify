-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Assumptions
public import Kernels.FlashKdaFwd.Spec
public import Lemmas.Execution.NoBarArrive
public import Lemmas.Execution.NoTma
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.NotRegister
public import Lemmas.Flow.NotTcAny
public import Lemmas.Flow.NotTensorPrefetch
public import Lemmas.Flow.NotWait
public import Lemmas.Flow.StoreValid
public import Lemmas.Flow.WaitLoopPcs
public import Lemmas.Flow.WarpUniform

@[expose] public section

/-! # The safety classes that the decoded program excludes

`Correct.safe` asks that no consistent execution is `Unsafe`, a disjunction of 28 classes of
undefined behaviour (`Core/Assembly/Execution.lean`). Fourteen of them cannot occur in this
kernel for a reason that is visible in its 3,836 decoded instructions alone, without following
any thread. This file proves those fourteen, each from one evaluated scan of the code:

* the kernel has no Tensor Core (`tcgen05`) instruction, so no execution has a `tcgen05` event
  (`noTc`). This closes the eight Tensor Core and Tensor Memory classes: `TcMma.SourceUnsafe`,
  `Tmem.Pair.ResourceUnsafe`, `Tmem.Pair.ReleaseUnsafe`, `Tmem.Pair.AccessUnsafe`,
  `TcCommitUnsafe`, `TcMma.WritesUnsafe`, `TcMma.InstructionUnsafe` and `TcMma.ReadsUnsafe`;
* no cluster-launch-control request (`ClcUnsafe`), no cluster barrier (`ClusterFault`), no
  `setmaxnreg` (`SetMaxNReg.UnsafeAt`);
* every tensor store (a copy from shared memory to a global tensor by the copy engine, "TMA")
  is a plain tile write without a reduction, and the kernel has no linear `cp.async` copy
  (`TensorStoreUnsafe`);
* no guarded instruction is one whose guard the lanes of a warp must agree on
  (`WarpDivergent`): the only guarded instructions are plain branches and five moves;
* each of the ten `mbarrier.try_wait` polls heads the loop `poll; @p bra exit; bra poll` that no
  branch enters and whose predicate nothing else reads (`PollShapeUnsafe`).

It also provides the scans that the remaining classes use: no `bar.arrive` (`noBarArrive`), no
mbarrier invalidation (`noMbarInval`), no linear copy (`noCopy`), no tensor prefetch
(`noTensorPrefetch`), and that the read-only assumption on the packed-offsets array is the only
assumption of the kernel that declares undefined behaviour (`noAssumptionUb`).

The scans are over `kernel.code` (`Spec.lean`: `kernel` abbreviates the decoded program). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Top
open PTX PTX.Flow

variable {L : Launch} {mem0 : Mem0} {A : List Assumption} {X : Execution}

/-! ## No Tensor Core instruction -/

private theorem noTcCode : kernel.code.all (fun ins => !tcAnyOp ins.op) = true := by
  decide +kernel

/-- **No event of the kernel is a Tensor Core (`tcgen05`) event.** -/
theorem noTc (hX : Consistent L kernel A mem0 X) : X.NoTc := by
  intro e pc k he
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · have hop : tcAnyOp ins.op = false := by
      have h := List.all_eq_true.mp noTcCode ins (List.mem_of_getElem? hc)
      simpa using h
    exact fires_notTc hop hf k rfl

/-- ERR-TMEM-READ-SOURCE: no Tensor Memory read needs a source. -/
theorem noTmemSource (hX : Consistent L kernel A mem0 X) : ¬ TcMma.SourceUnsafe L A X :=
  fun h => h (noTc hX).sourceSafe

/-- ERR-TMEM-RESOURCE: the Tensor Memory allocator has no request. -/
theorem noTmemResource (hX : Consistent L kernel A mem0 X) : ¬ Tmem.Pair.ResourceUnsafe L X :=
  (noTc hX).not_resourceUnsafe hX.tmemPair

/-- ERR-TMEM-NOT-RELEASED: nothing is allocated, so nothing is left allocated. -/
theorem noTmemRelease (hX : Consistent L kernel A mem0 X) : ¬ Tmem.Pair.ReleaseUnsafe L X :=
  (noTc hX).not_releaseUnsafe hX.tmemPair

/-- ERR-TMEM-ACCESS: no Tensor Memory access. -/
theorem noTmemAccess (hX : Consistent L kernel A mem0 X) : ¬ Tmem.Pair.AccessUnsafe L X :=
  (noTc hX).not_accessUnsafe

/-- ERR-TC-COMMIT: no `tcgen05.commit`. -/
theorem noTcCommit (hX : Consistent L kernel A mem0 X) : ¬ TcCommitUnsafe L X :=
  fun ⟨_, _, hc, _⟩ => (noTc hX).not_commit hc

/-- ERR-TMEM-RACE (writes): no Tensor Memory write. -/
theorem noTmemWrites (hX : Consistent L kernel A mem0 X) : ¬ TcMma.WritesUnsafe L X :=
  (noTc hX).not_writesUnsafe

/-- ERR-TC-MMA: no Tensor Core multiply-accumulate and no `tcgen05.cp`. -/
theorem noTmemInstruction (hX : Consistent L kernel A mem0 X) :
    ¬ TcMma.InstructionUnsafe L A X :=
  (noTc hX).not_instructionUnsafe

/-- ERR-TMEM-RACE (reads): no Tensor Memory read. -/
theorem noTmemReads (hX : Consistent L kernel A mem0 X) : ¬ TcMma.ReadsUnsafe L X :=
  (noTc hX).not_readsUnsafe

/-! ## No cluster launch control, cluster barrier or register request -/

private theorem noClcCode : kernel.code.all (fun ins => !clcOp ins.op) = true := by
  decide +kernel

/-- No cluster-launch-control request is issued. -/
theorem noClcIssue (hX : Consistent L kernel A mem0 X) {i : EvId} {s : Clc.Spec}
    {targets : List Nat} (hi : X.ClcIssue i s targets) : False := by
  obtain ⟨_, he⟩ := hi
  exact no_kind_of_code hX clcOp (fun k => ∃ s t, k = .clcIssue s t)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_clcIssue_op hf hk)
    noClcCode he ⟨_, _, rfl⟩

/-- ERR-CLC-REQUEST-AFTER-FAILURE: there is no request. -/
theorem noClcUnsafe (hX : Consistent L kernel A mem0 X) : ¬ ClcUnsafe L X := by
  rintro ⟨_, _, _, _, _, _, hi, _⟩
  exact noClcIssue hX hi

private theorem noClusterCode : kernel.code.all (fun ins => !clusterOp ins.op) = true := by
  decide +kernel

/-- No event is a cluster barrier operation (`barrier.cluster`). -/
theorem noClusterEvent (hX : Consistent L kernel A mem0 X) {i : EvId} {pc : Nat}
    {op : ClusterOp} (he : X.get i = some ⟨pc, .cluster op⟩) : False :=
  no_kind_of_code hX clusterOp (fun k => ∃ op, k = .cluster op)
    (fun _ ⟨_, h⟩ => by cases h)
    (fun hf ⟨_, hk⟩ => by simp [fires_cluster_op hf hk, clusterOp])
    noClusterCode he ⟨op, rfl⟩

/-- ERR-CLUSTER-BARRIER: a record of a cluster barrier that faults has a lane with a cluster
barrier event, and there is none. -/
theorem noClusterFault (hX : Consistent L kernel A mem0 X) : ¬ ClusterFault L X := by
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

private theorem noRegisterCode : kernel.code.all (fun ins => !setMaxRegOp ins.op) = true := by
  decide +kernel

/-- No event is a `setmaxnreg` request. -/
theorem noRegisterEvent (hX : Consistent L kernel A mem0 X) {i : EvId} {pc : Nat} {inc : Bool}
    {n inst : Nat} (he : X.get i = some ⟨pc, .setMaxReg inc n inst⟩) : False :=
  no_kind_of_code hX setMaxRegOp (fun k => ∃ inc n inst, k = .setMaxReg inc n inst)
    (fun _ ⟨_, _, _, h⟩ => by cases h)
    (fun hf ⟨_, _, _, hk⟩ => by simp [fires_setMaxReg_op hf hk, setMaxRegOp])
    noRegisterCode he ⟨inc, n, inst, rfl⟩

/-- ERR-SETMAXNREG: there is no register request. -/
theorem noRegister (hX : Consistent L kernel A mem0 X) : ¬ SetMaxNReg.UnsafeAt A L X := by
  rintro ⟨e, pc, inc, n, inst, hr, -⟩
  exact noRegisterEvent hX hr

/-! ## Copies, invalidations, prefetches and the form of the tensor stores -/

private theorem noCopyCode : kernel.code.all (fun ins => !bulkOp ins.op) = true := by
  decide +kernel

/-- **No linear asynchronous copy** (`cp.async`, `cp.async.bulk` without a tensor map) is
issued: every copy of the kernel goes through a tensor map. -/
theorem noCopy (hX : Consistent L kernel A mem0 X) (i : EvId) (s : AsyncCopy.Spec) :
    ¬ X.Copy i s := by
  rintro ⟨_, he⟩
  exact no_kind_of_code hX bulkOp (fun k => ∃ s, k = .copy s)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulk_op hf hk) noCopyCode he ⟨s, rfl⟩

private theorem noInvalCode : kernel.code.all (fun ins => !invalOp ins.op) = true := by
  decide +kernel

/-- **No mbarrier is invalidated**: an initialized mbarrier object lives until its CTA ends. -/
theorem noMbarInval (hX : Consistent L kernel A mem0 X) (v : EvId) (m : Loc) :
    ¬ X.MbInval v m := by
  rintro ⟨_, he⟩
  exact no_kind_of_code hX invalOp (fun k => ∃ m, k = .mbInval m)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_mbInval_op hf hk) noInvalCode he
    ⟨m, rfl⟩

private theorem noPrefetchCode :
    kernel.code.all (fun ins => !tensorPrefetchOp ins.op) = true := by
  decide +kernel

/-- **No tensor prefetch** is issued. -/
theorem noTensorPrefetch (hX : Consistent L kernel A mem0 X) {i : EvId} {address : Nat}
    {s : TensorPrefetch.Spec} (hi : X.TensorPrefetchIssue i address s) : False := by
  obtain ⟨_, he⟩ := hi
  exact no_kind_of_code hX tensorPrefetchOp (fun k => ∃ address s, k = .tensorPrefetch address s)
    (fun _ ⟨_, _, hk⟩ => by cases hk)
    (fun hf ⟨_, _, hk⟩ => fires_tensorPrefetch_op hf hk) noPrefetchCode he ⟨_, _, rfl⟩

/-- A tensor store instruction is a plain tile write: no reduction, no gather. -/
private def plainTileStore : Op → Bool
  | .cpTensorStore _ _ _ _ _ .tile none => true
  | op => !tensorStoreOp op

private theorem plainTileStoreCode : kernel.code.all (fun i => plainTileStore i.op) = true := by
  decide +kernel

/-- **Every issued tensor store is a valid tile write without a reduction.** The kernel's 32
tensor stores (16 of an output tile, 16 of the final state) copy bytes; none adds to memory. -/
theorem tensorStore_form (hX : Consistent L kernel A mem0 X) {i : EvId} {addr : Nat}
    {s : TensorStore.Spec} (hi : X.TensorStoreIssue i addr s) :
    TensorStore.Valid (i.1 / L.block) s ∧ s.rows = none ∧ s.reduce = none := by
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

/-- ERR-REDUCTION-NO-RULE: no tensor store reduces and there is no linear copy. -/
theorem noTensorStoreUnsafe (hX : Consistent L kernel A mem0 X) : ¬ TensorStoreUnsafe A X := by
  rintro (⟨i, o, red, _, _, ho, hRed, _⟩ | hCopy)
  · obtain ⟨⟨address, hi⟩, _⟩ := hX.store i o ho
    change o.spec.reduce = some red at hRed
    rw [(tensorStore_form hX hi).2.2] at hRed
    cases hRed
  · exact TensorStore.not_copyReduceNoRule_of_none
      (fun i s hi => (noCopy hX i s hi).elim) hCopy

/-! ## Guards and polls -/

private theorem noUniformGuards : kernel.noUniformGuards = true := by decide +kernel

/-- ERR-NONUNIFORM-GUARD: no instruction whose guard (or branch index) the lanes of a warp must
agree on is guarded. Every `elect.sync`, `shfl.sync`, warp matrix instruction, `bar.sync` and
`bra.uni` of the kernel is unguarded. -/
theorem noWarpDivergent : ¬ WarpDivergent L kernel A X :=
  not_warpDivergent noUniformGuards

/-- The positions of the ten `mbarrier.try_wait` instructions, read off the code. -/
def pollPcs : List Nat :=
  (kernel.code.zipIdx.filter fun x => pollOp x.1.op).map (·.2)

private theorem pollPcs_all : OpPcsFast kernel.code pollOp pollPcs = true := by
  decide +kernel

private theorem pollPcs_loops : kernel.waitLoopPcs pollPcs = true := by
  decide +kernel

/-- **Every poll is a canonical spin**: the event of a `mbarrier.try_wait` is at one of the ten
poll instructions, each of which heads a wait loop of the CUTLASS shape. -/
theorem poll_canonical (hX : Consistent L kernel A mem0 X) {i : EvId} {pc q : Nat} {m : Loc}
    {ok acq : Bool} {sc : MbarScope} (he : X.get i = some ⟨pc, .wait m q ok acq sc⟩) :
    ∃ exit, kernel.CanonicalSpin pc exit := by
  rcases get_source hX he with ⟨_, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  by_cases hw : ∃ p b off par a s, ins.op = .mbarWait p b off par a s
  · obtain ⟨p, b, off, par, a, s, ho⟩ := hw
    exact Kernel.canonicalSpin_of_waitLoopPcs pollPcs_all pollPcs_loops hc ho
  · exact (fires_notWait (eventTmpl_notWait fun p b off par a s ho => hw ⟨p, b, off, par, a, s, ho⟩)
      hf m q ok acq sc rfl).elim

/-- ERR-POLL-SHAPE: every poll is a canonical spin. -/
theorem noPollShapeUnsafe (hX : Consistent L kernel A mem0 X) : ¬ PollShapeUnsafe kernel X := by
  rintro ⟨i, pc, m, q, ok, acq, sc, he, hn, _⟩
  exact hn (poll_canonical hX he)

/-! ## Barriers: the form of the instructions -/

/-- The kernel has `bar.sync` only, no `bar.arrive`. -/
theorem noBarArrive : kernel.NoBarArrive := by
  unfold Kernel.NoBarArrive
  decide +kernel

instance : Fact kernel.NoBarArrive := ⟨noBarArrive⟩

/-! ## Assumptions -/

/-- **Only the read-only assumption on the packed-offsets array declares undefined behaviour**
(a write of a byte of that array). The other five assumptions of `Assumptions.all` have no `ub`
clause. -/
theorem noAssumptionUb (hInput : ¬ Assumptions.inputReadOnly.ub L mem0 X) :
    ¬ ∃ a ∈ Assumptions.all, a.ub L mem0 X := by
  rintro ⟨a, ha, hu⟩
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hu
  · exact hu
  · exact hu
  · exact hu
  · exact hu
  · exact hInput hu

end PTX.Kernels.FlashKdaFwd.Proof.Top
