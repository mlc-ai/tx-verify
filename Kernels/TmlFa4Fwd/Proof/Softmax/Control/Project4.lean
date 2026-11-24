-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.ProjectStep

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

theorem project_wend {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.wend x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_barEnd {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.barEnd x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_exit {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.exit x0,v,k, acc⟩ := by
  intro x0
  project_step

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
