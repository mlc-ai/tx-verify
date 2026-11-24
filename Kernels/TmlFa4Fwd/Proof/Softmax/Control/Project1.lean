-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.ProjectStep

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

theorem project_tiles {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.tiles x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_q0 {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    Projects (p := p) (L := L) (g := g) ⟨.q0,v,k, acc⟩ := by
  project_step

theorem project_q1 {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    Projects (p := p) (L := L) (g := g) ⟨.q1,v,k, acc⟩ := by
  project_step

theorem project_uk {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    Projects (p := p) (L := L) (g := g) ⟨.uk,v,k, acc⟩ := by
  project_step

theorem project_wq {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    Projects (p := p) (L := L) (g := g) ⟨.wq,v,k, acc⟩ := by
  project_step

theorem project_ws {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.ws x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_sld {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.sld x0 x1,v,k, acc⟩ := by
  intro x0 x1
  project_step

theorem project_sldw {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.sldw x0,v,k, acc⟩ := by
  intro x0
  project_step

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
