-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.ProjectStep

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

theorem project_fbar {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.fbar x0,v,k⟩ := by
  intro x0
  project_step

theorem project_fsum {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.fsum x0,v,k⟩ := by
  intro x0
  fin_cases x0 <;> project_step

theorem project_fmax {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.fmax x0,v,k⟩ := by
  intro x0
  fin_cases x0 <;> project_step

theorem project_farr {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.farr x0,v,k⟩ := by
  intro x0
  project_step

theorem project_fw {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.fw x0 x1,v,k⟩ := by
  intro x0 x1
  project_step

theorem project_fld {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.fld x0 x1,v,k⟩ := by
  intro x0 x1
  project_step

theorem project_fwl {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.fwl x0 x1,v,k⟩ := by
  intro x0 x1
  project_step

theorem project_fst {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0 x1 x2, Projects (p := p) (L := L) (g := g) ⟨.fst x0 x1 x2,v,k⟩ := by
  intro x0 x1 x2
  project_step

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
