-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Lemmas.Flow.NotAsyncArrive
public import Lemmas.Flow.NotBulk
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.PollPhase

@[expose] public section

/-! # Object record sources in the frozen FlashMLA kernel -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol

open AsyncCopy Flow MBarrier

private theorem no_inval_sites : kernel.code.all (fun ins => !invalOp ins.op) = true := by
  decide +kernel

private theorem no_async_arrive_sites :
    kernel.code.all (fun ins => !asyncArriveOp ins.op) = true := by
  decide +kernel

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The frozen kernel never issues an asynchronous barrier arrival. -/
theorem no_async_arrive (hX : Consistent L kernel Assumptions.all mem0 X) {i : EvId} {e : Event}
    {m : Loc} {noinc : Bool} (he : X.get i = some e) (hk : e.kind = .asyncArrive m noinc) :
    False :=
  no_kind_of_code hX asyncArriveOp (fun k => ∃ target b, k = .asyncArrive target b)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, h⟩ => fires_asyncArrive_op hf h)
    no_async_arrive_sites he ⟨m, noinc, hk⟩

/-- The frozen kernel never issues an mbarrier invalidation. -/
theorem no_inval (hX : Consistent L kernel Assumptions.all mem0 X) {i : EvId} {m : Loc}
    (hi : X.MbInval i m) : False := by
  obtain ⟨_, he⟩ := hi
  exact no_kind_of_code hX invalOp (fun k => ∃ m, k = .mbInval m)
    (fun _ ⟨_, hk⟩ => by cases hk) (fun hf ⟨_, hk⟩ => fires_mbInval_op hf hk)
    no_inval_sites he ⟨m, rfl⟩

/-- Each FlashMLA mbarrier has a single lifetime because the frozen kernel issues no
invalidation. -/
theorem objects_single_lifetime (hX : Consistent L kernel Assumptions.all mem0 X) (m : Loc) :
    NoInval (X.objects m) :=
  objects_noInval hX.tma.2.2.1 (fun _ _ => no_inval hX) m

/-- The frozen kernel has no async arrive instructions that increment a barrier's pending
count. -/
theorem objects_no_pending_increment (hX : Consistent L kernel Assumptions.all mem0 X) (m : Loc) :
    incrementsBefore (X.objects m) (X.objects m).length = 0 := by
  apply incrementsBefore_length_of
  intro r hr ha
  cases record_source hX.tma.2.2.1 hr with
  | increment _ he _ =>
    exact no_async_arrive hX he rfl
  | init _ _ h | inval _ _ h | arrive _ _ h | wait _ _ h | tensor _ _ _ h
  | arriveOn _ _ _ _ h | bulk _ _ _ _ h | commit _ _ _ h | clc _ _ _ _ h =>
    rw [ha] at h
    cases h

private theorem no_linear_copy_sites : kernel.code.all (fun ins => !bulkOp ins.op) = true := by
  decide +kernel

private theorem no_cluster_cancel_sites : kernel.code.all (fun ins => !clcOp ins.op) = true := by
  decide +kernel

/-- Every complete-tx record comes from a tensor load. Tensor stores and MMA commit
notifications have other forms. The frozen kernel has no linear bulk copy or cluster-cancel
request. -/
theorem object_completion_source (hX : Consistent L kernel Assumptions.all mem0 X) {m : Loc}
    {r : Record Ref} {bytes : Nat} (hr : r ∈ X.objects m) (ha : r.action = .completeTx bytes) :
    ∃ (i : EvId) (e : Event) (addr : Nat) (sp : TensorCopy.Spec), r.id = .async i (.notify .load) ∧
      X.get i = some e ∧ e.kind = .tensorIssue addr sp ∧ sp.mbar = m ∧
      TensorTransfer.bytes sp.descriptor = bytes := by
  cases record_source hX.tma.2.2.1 hr with
  | tensor hid he hm h =>
    rw [ha] at h
    exact ⟨_, _, _, _, hid, he, rfl, hm, (Action.completeTx.inj h).symm⟩
  | bulk _ he _ _ _ =>
    exact (no_kind_of_code hX bulkOp (fun k => ∃ s, k = .copy s)
      (fun _ ⟨_, hk⟩ => by cases hk) (fun hf ⟨_, hk⟩ => fires_bulk_op hf hk)
      no_linear_copy_sites he ⟨_, rfl⟩).elim
  | clc _ he _ _ _ =>
    exact (no_kind_of_code hX clcOp (fun k => ∃ s ts, k = .clcIssue s ts)
      (fun _ ⟨_, _, hk⟩ => by cases hk) (fun hf ⟨_, _, hk⟩ => fires_clcIssue_op hf hk)
      no_cluster_cancel_sites he ⟨_, _, rfl⟩).elim
  | init _ _ h | inval _ _ h | arrive _ _ h | wait _ _ h | increment _ _ h
  | arriveOn _ _ _ _ h | commit _ _ _ h =>
    rw [ha] at h
    cases h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol
