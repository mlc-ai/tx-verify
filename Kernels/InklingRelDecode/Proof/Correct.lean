-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.All
public import Kernels.InklingRelDecode.Proof.Progress.All
public import Kernels.InklingRelDecode.Proof.Bound.All
public import Kernels.InklingRelDecode.Proof.Result.OutAll
public import Kernels.InklingRelDecode.Proof.Interface.ClassSm
public import Kernels.InklingRelDecode.Proof.Interface.TmCode
public import Kernels.InklingRelDecode.Proof.Interface.PrefixAll
public import Kernels.InklingRelDecode.Proof.AssembleAll
public import Kernels.InklingRelDecode.Proof.Protocol.Lk5WStore
public import Lemmas.Kernel.Existence
public import Kernels.InklingRelDecode.Proof.Interface.PrefixDone

@[expose] public section

/-! # The kernel's correctness

The four conclusions (`safe_goal`, `progress_goal`, `bound_goal`, `Out.result_goal`) and their
assembly `PTX.correct_of`. Each takes premises about the thread machines and the protocols. Every
premise is built in `Assemble*.lean` (`Assemble.base_of`, `Assemble.protocol_of`,
`Assemble.remaining_of`, `Assemble.inputs_of`) from the tracking of the machines,
`Interface.tracked_holds`. `correct_of_pre`,
`completed_execution_of_pre` and `realizable_result_of_pre` are the three public theorems of
`Theorem.lean`. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- **The kernel is correct** on every launch that satisfies `Pre`. -/
theorem correct_of_pre {Q : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre Q L mem0) :
    Correct kernel Assumptions.all L mem0 (Post Q mem0) := by
  have hbase : ∀ X, Consistent L kernel Assumptions.all mem0 X → Assemble.Base Q L mem0 X :=
    fun X hX => Assemble.base_of hpre hX (Interface.tmplOk hpre)
      (Interface.tracked_holds hpre hX)
  have hprem : ∀ X, Consistent L kernel Assumptions.all mem0 X → Interface.Premises Q L X :=
    fun X hX => (hbase X hX).prem
  have hI : ∀ X, Consistent L kernel Assumptions.all mem0 X →
      ∀ i, Interface.Lk.ScratchIt Q L X i :=
    fun X hX => Interface.Lk.scratchIt_of_store hpre hX (hbase X hX).facts
      (Assemble.Base.roleReads hpre hX)
      (Interface.Lk.storeWord_all hpre hX (hbase X hX).facts
        (Rs.smBaseZero hpre hX (hbase X hX).facts
          (Interface.baseWordRead_of hpre hX)))
  have hsm : ∀ X, Consistent L kernel Assumptions.all mem0 X → Interface.Lk.LaneAgreeSm Q L X :=
    fun X hX => Interface.Lk.laneAgreeSm_of_it hpre hX (hbase X hX).facts (hI X hX)
  have halpha : ∀ X, Consistent L kernel Assumptions.all mem0 X → Bar.AlphaAgree L X :=
    fun X hX => Interface.Lk.alphaAgree_of_it hpre hX (hbase X hX).facts (hI X hX)
  have hs := Safety.safe_goal hpre Interface.smOb hprem
    (fun X hX => Assemble.protocol_of hpre hX (hbase X hX) (hsm X hX)
      (halpha X hX) (hI X hX))
  refine correct_of hs (fun hs' => ?_) ?_ (Result.Out.result_goal hpre
    (fun X hX hc => Assemble.inputs_of hpre hX hc (hbase X hX)
      (hI X hX)))
  · exact Progress.progress_goal hpre Interface.smOb hprem hs'
      (Assemble.remaining_of hpre hs' hbase
        (fun X hX => Assemble.protocol_of hpre hX (hbase X hX) (hsm X hX) (halpha X hX) (hI X hX))
        halpha hsm hI)
  · exact Bound.bound_goal hpre (fun g hg h => Interface.smOb g hg h)
      (fun X hX => Interface.tracked_select (hbase X hX).facts.tracked)
      (Assemble.dispatchBound_of hpre hbase)

/-- The assumptions are well-formed on the empty execution, which has no event. -/
theorem assumptions_wf {L : Launch} {mem0 : Mem0} :
    ∀ a ∈ Assumptions.all, a.wf L mem0 Execution.empty := by
  intro a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | trivial
    | (intro g j j' pc sp r h; simp [Execution.get, Execution.empty] at h)
    | (intro e pc a bs h; simp [Execution.get, Execution.empty] at h)

/-- The model admits a completed execution on every launch that satisfies `Pre`. -/
theorem completed_execution_of_pre {Q : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre Q L mem0) : ∃ X, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X :=
  (correct_of_pre hpre).complete_exists hpre.launchValid assumptions_wf

/-- A completed execution with the specified output exists on every launch that satisfies
`Pre`. -/
theorem realizable_result_of_pre {Q : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre Q L mem0) :
    ∃ X mf, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post Q mem0 mf :=
  (correct_of_pre hpre).output_exists hpre.launchValid assumptions_wf

end

end PTX.Kernels.InklingRelDecode.Proof
