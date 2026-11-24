-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.ShapeScalar
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX PTX.Proof PTX.Flow
noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

variable {p L m g} (hp : Pre p L m) (v : V) (k : Fin 4)
include hp

theorem shape_rbar (st : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.rbar st, v, k⟩ := by
  fin_cases st
  all_goals ctl_step

theorem shape_fbar (st : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.fbar st, v, k⟩ := by
  fin_cases st
  all_goals ctl_step

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
