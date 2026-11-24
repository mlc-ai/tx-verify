-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Projection
public import Kernels.TmlFa4Fwd.Proof.Softmax.Handoff

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control

/-- The softmax control and value machines accept the same startup hand-off. -/
theorem facts_init (p : Params) (L : Launch) (g : Nat) :
    (code p L g).facts (code p L g).init = (codeD p L g).facts (codeD p L g).init :=
  facts_eq_data (d := (code p L g).init) (liveD_3102.trans ctlLive_3102.symm)

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
