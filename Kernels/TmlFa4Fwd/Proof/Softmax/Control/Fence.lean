-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Projection
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control

open PTX.Proof PTX.Flow
set_option maxRecDepth 100000

theorem stepAt_fence_firstU {p L m g} (hp : Pre p L m) (v : V) :
    (code p L g).StepAtU ⟨.fence false,v,0,[]⟩ := by
  apply project rfl
  have hparams := params hp
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_3581, rfl, trivial⟩) ?_
  apply Code.step_issue (dn := Softmax.D.mk' (.bsync false) v.scheduler)
    (hc0 := Flow.code_3581)
  all_goals first | rfl | advances | exact fun _ => rfl | lands_auto (soft_seg) (soft_inv)

theorem stepAt_fence_biasU {p L m g} (hp : Pre p L m) (v : V) :
    (code p L g).StepAtU ⟨.fence true,v,0,[]⟩ := by
  apply project rfl
  have hparams := params hp
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_5269, rfl, trivial⟩) ?_
  apply Code.step_issue (dn := Softmax.D.mk' (.bsync true) v.scheduler)
    (hc0 := Flow.code_5269)
  all_goals first | rfl | advances | exact fun _ => rfl | lands_auto (soft_seg) (soft_inv)

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
