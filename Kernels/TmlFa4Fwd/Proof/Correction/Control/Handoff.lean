-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
public import Kernels.TmlFa4Fwd.Proof.Correction.Handoff

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

set_option maxRecDepth 100000 in
/-- Startup's existing gate supplies exactly the registers of the control machine. -/
theorem facts_init (p : Params) (L : Launch) (g : Nat) :
    (code p L g).facts (code p L g).init =
      (Data.code p L g).facts (Data.code p L g).init := rfl

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
