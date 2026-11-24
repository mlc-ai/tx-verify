-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.AssembleLock
public import Kernels.InklingRelDecode.Proof.Protocol.Lk4Tc
public import Kernels.InklingRelDecode.Proof.Progress.Lk4WarpExit

@[expose] public section

/-!
# The lockstep's second round of consumers, from the base and the softmax premise

From `Interface.Lk.LaneAgree` (`Base.laneAgree`, whose one premise is `LaneAgreeSm`):

* `Base.tcAligned`: `Safety.Protocol.tcAligned` (`Bar.tcDivergent_not`, `Bar.tcExited_not`);
* `Progress.Lk4.warpColl_exit`: `WarpCollFacts.exit` (used in `AssembleProgress.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Assemble
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (b : Base Q L mem0 X)
include hpre hX b

/-- **`Safety.Protocol.tcAligned`.** -/
theorem Base.tcAligned (hsm : Lk.LaneAgreeSm Q L X) :
    ¬ AlignedClass.tc.Divergent L kernel X ∧ ¬ AlignedClass.tc.Exited L kernel X :=
  ⟨Bar.tcDivergent_not hpre hX b.facts (Interface.baseWordRead_of hpre hX)
      (Base.laneAgree hpre hX b hsm),
    Bar.tcExited_not hpre hX b.facts (Base.laneAgree hpre hX b hsm)⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Assemble
