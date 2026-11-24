-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressData
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSpins
import Lemmas.Flow.NotThreadFence
import Lemmas.Order.GuardSnoc

public section

/-! # Read source selection in safe FlashMLA prefixes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000 in
private theorem no_release : kernel.code.all (fun ins => !releaseOp ins.op) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem no_fence : kernel.code.all (fun ins => !threadFenceOp ins.op) = true := by
  decide +kernel

/-- No ordinary thread fence appears in the frozen kernel. -/
theorem no_thread_fence {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (e : EvId) (sem : FenceSem)
    (s : MbarScope) : ¬ X.ThreadFence e sem s := fun ⟨_, he⟩ =>
  Flow.no_kind_of_code hX Flow.threadFenceOp (fun k => ∃ sem s, k = .fence sem s)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => Flow.fires_threadFence_op hf hk)
    no_fence he ⟨_, _, rfl⟩

/-- No ordinary store has release semantics in the frozen kernel. -/
theorem write_no_release {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {a : Acc} {bs : List Byte} {tag : Nat}
    (he : X.get i = some ⟨tag, .wr a bs⟩) : a.release = false := by
  rcases get_source hX he with ⟨_, hk⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hk
  · have h := List.all_eq_true.mp no_release ins (List.mem_of_getElem? hc)
    simp only [Bool.not_eq_true'] at h
    exact PTX.fires_write_release hf h rfl

/-- The canonical spins and absence of ordinary release synchronization follow from the frozen
instructions. Object records are fault-free by safety. -/
theorem sync_guarded {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hsafe : ¬ Unsafe L kernel Assumptions.all mem0 X) : SyncGuarded L kernel X where
  spin _ _ _ _ _ _ he := RingSpins.successful_poll hX he
  noMemSync e f := ⟨noSynchronizesWith_of (fun _ _ _ _ he =>
    write_no_release hX he)
    (fun _ _ _ _ _ he => (GlobalWrites.no_rmw hX ⟨_, he⟩).elim) e f,
    not_fenceSync_of_noFence (no_thread_fence hX) e f⟩
  noFault m _ _ r _ hr _ _ _ := by
    cases hf : r.fault with
    | none => rfl
    | some f =>
      refine absurd ?_ hsafe
      exact .inr (.inr (.inr (.inr (.inr (.inl (.inl
        ⟨m, r, List.mem_of_getElem? hr, by simp [hf]⟩))))))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
