-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.ProjectStep

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

theorem project_fence {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.fence x0,v,k⟩ := by
  intro x0
  project_step

theorem project_fdone {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.fdone x0 x1,v,k⟩ := by
  intro x0 x1
  fin_cases x0 <;> fin_cases x1 <;> project_step

theorem project_lse {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.lse x0,v,k⟩ := by
  intro x0
  fin_cases x0 <;> project_step

theorem project_wend {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.wend x0,v,k⟩ := by
  intro x0
  project_step

theorem project_barEnd {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.barEnd x0,v,k⟩ := by
  intro x0
  project_step

theorem project_exit {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.exit x0,v,k⟩ := by
  intro x0
  project_step

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
