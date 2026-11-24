-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.MemoryFacts
public import Kernels.Fp16Gemm8192.Proof.TensorFacts
public import Kernels.Fp16Gemm8192.Proof.CommitFacts
public import Kernels.Fp16Gemm8192.Proof.TmemAccessFacts
public import Kernels.Fp16Gemm8192.Proof.TcInstrFacts
public import Kernels.Fp16Gemm8192.Proof.TcLoadFacts
public import Kernels.Fp16Gemm8192.Proof.Safety.Clc
public import Kernels.Fp16Gemm8192.Proof.Safety.SyncBar
public import Kernels.Fp16Gemm8192.Proof.Safety.SyncCluster
public import Kernels.Fp16Gemm8192.Proof.Safety.Tma
public import Kernels.Fp16Gemm8192.Proof.PollFacts
public import Kernels.Fp16Gemm8192.Proof.Safety.TensorStore
public import Kernels.Fp16Gemm8192.Proof.Safety.ThreadUb
public import Kernels.Fp16Gemm8192.Proof.Safety.ThreadTc
public import Kernels.Fp16Gemm8192.Proof.Safety.Resource
public import Kernels.Fp16Gemm8192.Proof.Safety.ResourceTensor
public import Kernels.Fp16Gemm8192.Proof.Safety.ResourceTmem
public import Kernels.Fp16Gemm8192.Proof.Safety.TcWrites
public import Kernels.Fp16Gemm8192.Proof.Safety.EventKinds
public import Kernels.Fp16Gemm8192.Proof.Thread.WaitSpins
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemAlloc.BaseValue
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Requests
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Exit
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Joint
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Complete
public import Kernels.Fp16Gemm8192.Proof.ClusterLaneFacts
public import Lemmas.CtaBarrier.CtaBarrierFault
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Joint

@[expose] public section

/-! # `SafeGoal`

The root of the safety layer: every branch of `Unsafe` is dispatched to its theorem, from the
thread facts (`threadFacts`) and the protocols' exports. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof
noncomputable section

/-- **Every poll of the kernel is the poll of a canonical spin**, whether or not it succeeds: it
fires from a listed poll of the code, which heads a wait loop (as `wait_spins`). -/
theorem poll_spins {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {e : EvId} {pc : Nat} {m : Loc}
    {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : X.get e = some ⟨pc, .wait m p ok acq sc⟩) :
    ∃ exit, kernel.CanonicalSpin pc exit := by
  obtain ⟨g, k⟩ := e
  obtain ⟨d, hσ⟩ := Frame.event_state (fun _ => sound hpre) hX (tracked hpre hX) he
    (fun _ _ h => by cases h)
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hpc := EventFrame.fires_source_pc hf
  simp only at hpc
  subst hpc
  by_cases hw : ∃ q b off par a s, ins.op = .mbarWait q b off par a s
  · obtain ⟨q, b, off, par, a, s, hop⟩ := hw
    exact Kernel.canonicalSpin_of_waitLoopPcs kernel_poll_pcs kernel_wait_loops hc hop
  · push Not at hw
    exact absurd rfl (Flow.fires_notWait (Flow.eventTmpl_notWait hw) hf m p ok acq sc)

/-- **No consistent execution is unsafe.** -/
theorem safe_goal {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    SafeGoal kernel Prod L mem0 := by
  refine ⟨Safety.tc_group_uniform, fun X hX hu => ?_⟩
  have ht := threadFacts hpre hX
  have hrw := Region.responseWriters hpre hX ht
  have hagree := ClcRing.allResponsesAgree hpre hX ht hrw
  have hrv := ClcRing.readerValues hpre hX ht hrw
  have hbv := TmemAlloc.baseValue hpre hX ht
  rcases hu with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h
  · exact no_ub hpre hX h
  · exact Memory.no_unalloc hpre hX h
  · exact Memory.no_race hpre hX h
  · exact Memory.no_mixed hpre hX h
  · exact Safety.no_barMismatch hX ht h
  · exact Safety.no_tmaUnsafe hpre hX ht (inputFacts hpre hX ht)
      (tmemFacts hpre hX ht) (clcFacts hpre hX ht) (Region.sharedWindow hpre hX ht) h
  · exact h (tc_supported hpre hX)
  · exact Safety.no_assumption_ub h
  · obtain ⟨htcd, htcx⟩ := Safety.no_tc_unsafe hX ht hagree hbv
    obtain ⟨hcld, hclx⟩ := Safety.no_cluster_mismatch hX ht
    rcases (alignedMismatch_iff L).mp h with (h | h) | (h | h) | (h | h) | (h | h) | (h | h)
    · exact htcd h
    · exact htcx h
    · exact Safety.no_barDivergent hX ht h
    · exact Safety.no_barExited hX ht h
    · exact hcld h
    · exact hclx h
    · exact Safety.no_setMaxReg_divergent hX ht h
    · exact Safety.no_setMaxReg_exited hX ht h
    · obtain ⟨g, i, pc, op, own, recv, n, hget, -⟩ := AlignedClass.divergent_matrix_old L h
      have := Safety.no_matrix hX ht hget
      simp [isMatrix] at this
    · obtain ⟨g, i, pc, op, own, recv, n, hget, -⟩ := AlignedClass.exited_matrix_old L h
      have := Safety.no_matrix hX ht hget
      simp [isMatrix] at this
  · exact no_sharedLifetimeUnsafe hpre hX h
  · exact Safety.failed_query_safe hpre hX ht (ClcRing.issueBeforeObservers hpre hX ht)
      (ClcRing.requestsBeforeFailure hpre hX ht hrv) hrv h
  · exact no_tensorUnsafe hpre hX h
  · exact Safety.no_tensorStoreUnsafe hX ht h
  · exact Safety.no_tensor_allocation_unsafe hX ht h
  · exact Tmem.Pair.no_resource_unsafe hX (Safety.pairFacts hpre hX ht hbv) h
  · exact Tmem.Pair.no_release_unsafe hX (Safety.pairFacts hpre hX ht hbv) h
  · obtain ⟨e, pc, m, q, ok, acq, sc, he, hns, -⟩ := h
    exact hns (poll_spins hpre hX he)
  · exact no_tmemAccessUnsafe hpre hX h
  · exact no_tcCommitUnsafe hpre hX h
  · exact Safety.no_writes_unsafe hpre hX ht h
  · exact no_instructionUnsafe hpre hX h
  · exact Safety.no_reads_unsafe hpre hX ht h
  · exact Safety.no_reg_unsafe hpre hX ht h.unsafe
  · refine not_ctaBarFault hX (fun e f id cnt cnt' pc pc' _ he hf => ?_) h
    obtain ⟨-, -, -, -, h1, -⟩ := Safety.bar_info (g := e.1) (i := e.2) hX ht he
    obtain ⟨-, -, -, -, h2, -⟩ := Safety.bar_info (g := f.1) (i := f.2) hX ht hf
    rw [h1, h2]
  · exact no_cluster_fault hX ht h
  · exact not_warpDivergent_polls poll_guards local_frames (poll_obj_uniform hpre hX ht)
      (poll_ordered hpre hX ht) h
  · exact not_matrixUnsafe_of_none L (fun e ev he => Safety.no_matrix hX ht he) h
  · exact Safety.no_mbarUninit hpre hX ht h

end
end PTX.Kernels.Fp16Gemm8192.Proof
