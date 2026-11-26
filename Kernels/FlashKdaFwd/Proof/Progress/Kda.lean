-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Data.Decoded
public import Kernels.FlashKdaFwd.Proof.Progress.Asm
public import Kernels.FlashKdaFwd.Proof.Progress.Progress
public import Lemmas.Flow.NotRegister
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.NotAsyncWait
public import Lemmas.Flow.NotAsyncArrive
public import Lemmas.Flow.NotTcAny
public import Lemmas.Flow.NotBulk
public import Lemmas.Execution.NoBarArrive

@[expose] public section

/-!
# The assumption and code premises of the progress skeleton, for the FlashKDA kernel

`Progress.lean` proves progress for any kernel from three structures of premises. Two of them
are proved here for the FlashKDA kernel:

* `codeOk`: the facts of the code. The 3,836 instructions contain no mode vote, no
  cluster-barrier operation, no `setmaxnreg`, no `cp.async.wait_group`, no `tcgen05`
  instruction, no linear bulk copy, no `cp.async.mbarrier.arrive`, no cancellation request and
  no `bar.arrive` (each a check of the decoded code by kernel evaluation), so no consistent
  execution has an event of such a kind.
* `asmOk`: the assumptions' execution constraints, with elected lane `0`: `wfStepE_all`,
  `wf_appendLanes`, `zero_member` and `leaderZero` of `Asm.lean`.

Also here: `readWf_of_safe` proves the field `Premises.readWf` of the third structure from the
safety goal (no operation writes the packed-offsets array).

The third structure, `Premises`, is what remains: one group of facts per class of pending
thread or operation, to be supplied by the thread layer and the protocol layer. `Machine.lean`
states the theorem against the kernel's thread machine.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched PTX.Step PTX.Kernels.FlashKdaFwd

noncomputable section

/-! ### The facts of the code -/

/-- The code has no mode vote. -/
theorem kernel_noVoteMode :
    Decoded.kernel.code.all (fun ins => !voteModeOp ins.op) = true := by decide +kernel

/-- The code has no cluster-barrier operation. -/
theorem kernel_noCluster :
    Decoded.kernel.code.all (fun ins => !Flow.clusterOp ins.op) = true := by decide +kernel

/-- The code has no `setmaxnreg`. -/
theorem kernel_noSetMaxReg :
    Decoded.kernel.code.all (fun ins => !Flow.setMaxRegOp ins.op) = true := by decide +kernel

/-- The code has no `cp.async.wait_group`. -/
theorem kernel_noAsyncWait :
    Decoded.kernel.code.all (fun ins => !Flow.asyncWaitOp ins.op) = true := by decide +kernel

/-- The code has no `tcgen05` instruction. -/
theorem kernel_noTc :
    Decoded.kernel.code.all (fun ins => !Flow.tcAnyOp ins.op) = true := by decide +kernel

/-- The code has no linear bulk copy. -/
theorem kernel_noBulk :
    Decoded.kernel.code.all (fun ins => !Flow.bulkOp ins.op) = true := by decide +kernel

/-- The code has no `cp.async.mbarrier.arrive`. -/
theorem kernel_noAsyncArrive :
    Decoded.kernel.code.all (fun ins => !Flow.asyncArriveOp ins.op) = true := by decide +kernel

/-- The code has no cancellation request. -/
theorem kernel_noClc :
    Decoded.kernel.code.all (fun ins => !Flow.clcOp ins.op) = true := by decide +kernel

/-- The code has no `bar.arrive`. -/
theorem kernel_noBarArrive : Decoded.kernel.NoBarArrive := by
  unfold Kernel.NoBarArrive
  decide +kernel

variable {L : Launch} {mem0 : Mem0} {A : List Assumption} {X : Execution}

/-- **No event of a consistent execution has an absent kind.** -/
theorem kernel_kinds (hX : Consistent L Decoded.kernel A mem0 X) {i : EvId} {e : Event}
    (he : X.get i = some e) : absent e.kind = false := by
  obtain ⟨pc, k⟩ := e
  cases k
  case cluster op =>
    exact (Flow.no_kind_of_code hX Flow.clusterOp (fun k => ∃ op, k = .cluster op)
      (fun _ ⟨_, h⟩ => by cases h)
      (fun hf ⟨_, hk⟩ => by rw [Flow.fires_cluster_op hf hk]; rfl) kernel_noCluster he
      ⟨op, rfl⟩).elim
  case setMaxReg inc n inst =>
    exact (Flow.no_kind_of_code hX Flow.setMaxRegOp
      (fun k => ∃ inc n inst, k = .setMaxReg inc n inst) (fun _ ⟨_, _, _, h⟩ => by cases h)
      (fun hf ⟨_, _, _, hk⟩ => by rw [Flow.fires_setMaxReg_op hf hk]; rfl) kernel_noSetMaxReg he
      ⟨inc, n, inst, rfl⟩).elim
  case asyncWait n =>
    exact (Flow.no_kind_of_code hX Flow.asyncWaitOp (fun k => ∃ n, k = .asyncWait n)
      (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => Flow.fires_asyncWait_op hf hk)
      kernel_noAsyncWait he ⟨n, rfl⟩).elim
  case tc kd =>
    exact (Flow.no_kind_of_code hX Flow.tcAnyOp (fun k => ∃ kd, k = .tc kd)
      (fun _ ⟨_, h⟩ => by cases h)
      (fun {_ _ _ op _ _} hf ⟨kd', hk⟩ => by
        cases hop : Flow.tcAnyOp op
        · exact (Flow.fires_notTc hop hf kd' hk).elim
        · rfl)
      kernel_noTc he ⟨kd, rfl⟩).elim
  case copy s =>
    exact (Flow.no_kind_of_code hX Flow.bulkOp (fun k => ∃ s, k = .copy s)
      (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => Flow.fires_bulk_op hf hk)
      kernel_noBulk he ⟨s, rfl⟩).elim
  case asyncArrive m noinc =>
    exact (Flow.no_kind_of_code hX Flow.asyncArriveOp
      (fun k => ∃ m noinc, k = .asyncArrive m noinc) (fun _ ⟨_, _, h⟩ => by cases h)
      (fun hf ⟨_, _, hk⟩ => Flow.fires_asyncArrive_op hf hk)
      kernel_noAsyncArrive he ⟨m, noinc, rfl⟩).elim
  case clcIssue sp tg =>
    exact (Flow.no_kind_of_code hX Flow.clcOp (fun k => ∃ sp tg, k = .clcIssue sp tg)
      (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => Flow.fires_clcIssue_op hf hk)
      kernel_noClc he ⟨sp, tg, rfl⟩).elim
  case bar id cnt mode =>
    cases mode
    · rfl
    · exact (Consistent.noBarArrive kernel_noBarArrive hX i pc id cnt he).elim
  all_goals rfl

/-- **The facts of the code** (proved). -/
theorem codeOk : CodeOk L Decoded.kernel mem0 A :=
  ⟨kernel_noVoteMode, fun _ hX _ _ he => kernel_kinds hX he⟩

/-! ### The assumptions -/

/-- **The assumption interface, with elected lane 0** (proved). -/
theorem asmOk {K : Kernel} : AsmOk L K mem0 Assumptions.all 0 where
  step := wfStepE_all
  lanes _ hX _ ev h := wf_appendLanes hX _ ev h
  member := zero_member
  det _ hX := leaderZero hX

/-- **No operation of a consistent execution writes a byte of the packed-offsets array**, given
safety: such a write is the undefined behaviour the assumption `inputReadOnly` declares, one
disjunct of `Unsafe`. -/
theorem noOffsetWrite {K : Kernel} (hs : SafeGoal K Assumptions.all L mem0)
    (hX : Consistent L K Assumptions.all mem0 X) :
    ¬ Assumptions.inputReadOnly.ub L mem0 X := fun h => by
  have hub : ∃ a ∈ Assumptions.all, a.ub L mem0 X :=
    ⟨Assumptions.inputReadOnly, by simp [Assumptions.all], h⟩
  exact hs.2 X hX (by unfold Unsafe; simp [hub])

/-- **The premise `Premises.readWf` of the skeleton, proved from safety**: an appended read
whose bytes have sources keeps the assumptions' constraints, because no operation writes the
packed-offsets array. -/
theorem readWf_of_safe {K : Kernel} (hs : SafeGoal K Assumptions.all L mem0)
    (hX : Consistent L K Assumptions.all mem0 X) (g pc : Nat) (a : Acc)
    (bs : List (Option Byte)) (r : Nat → Option AsyncCopy.Ref)
    (h : ∀ e, NewRead L mem0 X g e r a bs) :
    ∀ a' ∈ Assumptions.all, a'.wf L mem0 (X.snoc g ⟨pc, .rd a bs⟩ r) :=
  wf_snoc_read_of_noOffsetWrite hX (noOffsetWrite hs hX) (h ⟨pc, .rd a bs⟩)

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
