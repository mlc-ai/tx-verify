-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.ProjectStep

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

theorem project_rscale {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.rscale x0,v,k⟩ := by
  intro x0
  fin_cases x0 <;> project_step

theorem project_rvote {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.rvote x0,v,k⟩ := by
  intro x0
  fin_cases x0 <;> project_step

theorem project_rld {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.rld x0 x1,v,k⟩ := by
  intro x0 x1
  project_step

theorem project_rldw {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.rldw x0 x1,v,k⟩ := by
  intro x0 x1
  project_step

theorem project_rst {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.rst x0 x1,v,k⟩ := by
  intro x0 x1
  project_step

theorem project_rwait {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.rwait x0,v,k⟩ := by
  intro x0
  project_step

theorem project_rarr {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.rarr x0 x1,v,k⟩ := by
  intro x0 x1
  project_step

theorem project_farr0 {p L g} (v : Correction.V) (k : Fin 4) :
    Projects (p := p) (L := L) (g := g) ⟨.farr0,v,k⟩ := by
  project_step

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
