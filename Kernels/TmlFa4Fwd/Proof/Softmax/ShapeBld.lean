-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- Every bias site decodes to a non-extending load. The instruction is independent of the
lane state and the sub-step. -/
theorem bld_instr (b : Bool) (c : Fin 16) : ∃ guard a,
    kernel.code[(Site.bld b c).pc]? = some ⟨guard, .mem a⟩ ∧
      a.kind = .load ∧ a.nc = false ∧ a.ext = .same := by
  cases b <;> fin_cases c <;> exact ⟨_, _, by code_lookup, rfl, rfl, rfl⟩

theorem shapeAt_bld (_hp : Pre p L m) (d : D) (hs : ∃ b c, d.site = .bld b c) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨b, c, hs⟩ := hs
  obtain ⟨guard, a, hc', hld, hnc, hext⟩ := bld_instr b c
  intro t ins e o hat hi hc hf
  change kernel.code[d.site.pc]? = some ins at hc
  rw [hs, hc'] at hc
  cases hc
  unfold Ev
  rw [hs]
  exact shape_ldAny (P := rdOrUb) hf hld hnc hext (fun r bs => .inl ⟨r, bs, rfl⟩)
    (fun f => .inr ⟨f, rfl⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
