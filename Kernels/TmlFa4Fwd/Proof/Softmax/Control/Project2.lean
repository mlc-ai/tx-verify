-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.ProjectStep

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

theorem project_wb {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.wb x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_bld {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.bld x0 x1,v,k, acc⟩ := by
  intro x0 x1
  project_step

theorem project_fence {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.fence x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_bsync {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.bsync x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_barr {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.barr x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_stat {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.stat x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_narr {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.narr x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_pst {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.pst x0 x1,v,k, acc⟩ := by
  intro x0 x1
  project_step

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
