-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Quiet.Base
import Lemmas.Step.CommitOrderExtend

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

public theorem assumptions_step {L : Launch} {m : Mem0} :
    Assumption.WfStep (fun _ => true) L kernel m Assumptions.all := by
  intro X Y hX hle hord hr a ha
  have hw := hX.asm a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals first
    | trivial
    | exact Assumption.commitPerformedAt_extend (fun _ _ => rfl) hw hX.tcCommit hle hord
    | exact fun e pc a bs he hs => hw e pc a bs (hr e _ he rfl) hs

end PTX.Kernels.InklingRelDecode.Proof.Lib
