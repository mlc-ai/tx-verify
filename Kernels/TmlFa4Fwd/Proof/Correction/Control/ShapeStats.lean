-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.ShapeScalar
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX PTX.Proof PTX.Flow
noncomputable section

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {g : Nat} (v : V) (k : Fin 4)


theorem shape_rscale (st : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.rscale st, v, k⟩ := by
  fin_cases st
  all_goals
    intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_ldAny hf rfl rfl rfl (fun _ _ => .inl ⟨_, _, rfl⟩) (fun _ => .inr ⟨_, rfl⟩)

theorem shape_fsum (st : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.fsum st, v, k⟩ := by
  fin_cases st
  all_goals
    intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_ldAny hf rfl rfl rfl (fun _ _ => .inl ⟨_, _, rfl⟩) (fun _ => .inr ⟨_, rfl⟩)

theorem shape_fmax (st : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.fmax st, v, k⟩ := by
  fin_cases st
  all_goals
    intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_ldAny hf rfl rfl rfl (fun _ _ => .inl ⟨_, _, rfl⟩) (fun _ => .inr ⟨_, rfl⟩)

theorem shape_lse (h : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.lse h, v, k⟩ := by
  fin_cases h
  all_goals
    intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_store hf rfl (fun _ _ => .inl ⟨_, _, rfl⟩) (fun _ => .inr ⟨_, rfl⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
