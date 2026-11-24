-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.ProjectStep

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

theorem project_pre {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.pre x0,v,k⟩ := by
  intro x0
  project_step

theorem project_tiles {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.tiles x0,v,k⟩ := by
  intro x0
  project_step

theorem project_q0 {p L g} (v : Correction.V) (k : Fin 4) :
    Projects (p := p) (L := L) (g := g) ⟨.q0,v,k⟩ := by
  project_step

theorem project_q1 {p L g} (v : Correction.V) (k : Fin 4) :
    Projects (p := p) (L := L) (g := g) ⟨.q1,v,k⟩ := by
  project_step

theorem project_uk {p L g} (v : Correction.V) (k : Fin 4) :
    Projects (p := p) (L := L) (g := g) ⟨.uk,v,k⟩ := by
  project_step

theorem project_nb {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.nb x0,v,k⟩ := by
  intro x0
  fin_cases x0
  · project_step
  · intro e a h
    cases h
    change some (some (erase (enterRounds p L g _))) = some (some (erase (enterRounds p L g _)))
    unfold enterRounds Correction.D.ite
    split <;> rename_i h
    all_goals split
    all_goals first | rfl | exact (False.elim (by contradiction))

theorem project_free {p L g} (v : Correction.V) (k : Fin 4) :
    Projects (p := p) (L := L) (g := g) ⟨.free,v,k⟩ := by
  project_step

theorem project_rbar {p L g} (v : Correction.V) (k : Fin 4) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.rbar x0,v,k⟩ := by
  intro x0
  project_step

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
