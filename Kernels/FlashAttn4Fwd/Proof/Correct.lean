-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.SafeFacts
public import Kernels.FlashAttn4Fwd.Proof.ProgressFacts
public import Kernels.FlashAttn4Fwd.Proof.BoundFacts
public import Kernels.FlashAttn4Fwd.Proof.ValuesGlue
public import Kernels.FlashAttn4Fwd.Proof.FactsAllValues
public import Lemmas.Kernel.Existence

@[expose] public section

/-! # The kernel's correctness

The four conclusions (`safe_goal`, `progress_goal`, `bound_goal`, `result_goal_of_values`) and
their assembly `PTX.correct_of`, as for the GEMM kernel. The thread layer's exports the goals
take are assembled in `FactsAll*.lean` from their field theorems, and so are the protocol
premises (`FactsAllValues.lean`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The launches `Pre` describes are ones the kernel's declarations admit (CORRECT-LAUNCH). -/
theorem valid {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    L.Valid kernel := by
  refine ⟨Launch.oneDimLaunch_clusterGridValid hpre.oneDimLaunch, fun n h => ?_, fun s h => ?_,
    fun name p v h => ?_⟩
  · have hk : kernel.maxThreads = none := rfl
    rw [hk] at h
    cases h
  · have hk : kernel.reqThreads = some (512, 1, 1) := rfl
    rw [hk, Option.some.injEq] at h
    rw [Launch.oneDim_reqntid hpre.oneDimLaunch.1, ← h, hpre.block]
  · have hk : kernel.ptrParams = [] := rfl
    rw [hk] at h
    cases h

/-- **The kernel is correct** on every launch that satisfies its precondition. -/
theorem correct {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    Correct kernel asms L mem0 (Post P mem0) :=
  have hR : SafeRemaining P L mem0 := fun _ hX =>
    ⟨FactsAll.threadInputs hpre hX, ⟨FactsAll.smemElements hpre hX⟩⟩
  correct_of (safe_goal hpre hR)
    (fun hs => progress_goal hpre hs (FactsAll.progressRemaining hpre) (outside_ordered hpre hR))
    (bound_goal hpre)
    (result_goal_of_values hpre (fun _ hX => FactsAll.resultInputs hpre hX) fun _ hX _ =>
      FactsAll.valueInputs hpre hX)

/-- The assumptions are well-formed on the empty execution. -/
theorem assumptions_wf {L : Launch} {mem0 : Mem0} :
    ∀ a ∈ asms, a.wf L mem0 Execution.empty := by
  simp [asms, Assumptions.all, Assumptions.idealArith, Assumptions.clusterMbar,
    Assumptions.approx, Assumptions.swExp2, Assumptions.peerBit, Assumptions.tcLd,
    Assumptions.commitOrder, Assumptions.pollAgree, Assumption.idealReal,
    Assumption.clusterScopeMbarAt, Assumption.approxExact, Assumption.segmentExact,
    Assumption.pairEvenAt, Assumption.tcLdDataflowAt, Assumption.commitOrderAt,
    Assumption.pollAgreeAt]
  intro g j j' pc sp r h
  simp [Execution.get, Execution.empty] at h

/-- The model admits a completed execution. -/
theorem completed_execution {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X, Consistent L kernel asms mem0 X ∧ Complete L X :=
  (correct hpre).complete_exists (valid hpre) assumptions_wf

/-- A completed execution with the specified output exists. -/
theorem realizable_result {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X mf, Consistent L kernel asms mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  (correct hpre).output_exists (valid hpre) assumptions_wf

end

end PTX.Kernels.FlashAttn4Fwd.Proof
