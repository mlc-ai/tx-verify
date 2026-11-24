-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.ProjectStep

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

theorem project_setmax {p L g} (v : Correction.V) (k : Fin 4) :
    Projects (p := p) (L := L) (g := g) ⟨.setmax,v,k⟩ := by
  project_step

theorem project_bar1 {p L g} (v : Correction.V) (k : Fin 4) :
    Projects (p := p) (L := L) (g := g) ⟨.bar1,v,k⟩ := by
  project_step

theorem project_arr {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.arr x0,v,k⟩ := by
  intro x0
  project_step

theorem project_word {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.word x0,v,k⟩ := by
  intro x0
  project_step

theorem project_down {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.down x0,v,k⟩ := by
  intro x0
  project_step

theorem project_up {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.up x0 x1,v,k⟩ := by
  intro x0 x1
  project_step

theorem project_total {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.total x0,v,k⟩ := by
  intro x0
  project_step

theorem project_vote {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.vote x0,v,k⟩ := by
  intro x0
  project_step

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
