-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
public import Kernels.TmlFa4Fwd.Proof.Softmax.EvS
import Kernels.TmlFa4Fwd.Proof.Softmax.Shapes
import Kernels.TmlFa4Fwd.Proof.Softmax.ShapeBld

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Proof PTX.Flow
noncomputable section

abbrev Ev (p : Params) (L : Launch) (g : Nat) (d : D) :=
  Softmax.Ev p L g d.scheduler

abbrev EvS (p : Params) (L : Launch) (g : Nat) (d : D) :=
  Softmax.EvS p L g d.scheduler

variable {p : Params} {L : Launch} {g : Nat} {m : Mem0}

/-- Only the vector bias load permits an arbitrary partial accumulator. Its read template
already determines its event shape, independently of every accumulated value. -/
theorem shapeAt (hp : Pre p L m) (d : D) : (code p L g).ShapeAt (Ev p L g) d := by
  intro t ins e o hat hi hc hf
  by_cases hb : ∃ b c, d.site = .bld b c
  · obtain ⟨b,c,hs⟩ := hb
    obtain ⟨guard, a, hdec, hk, hn, he⟩ := bld_instr b c
    change kernel.code[d.site.pc]? = some ins at hc
    rw [hs, hdec] at hc
    cases hc
    change Softmax.Ev p L g d.scheduler e
    unfold Softmax.Ev
    rw [show d.scheduler.site = .bld b c from hs]
    exact shape_ldAny (P := rdOrUb) hf hk hn he (fun r bs => .inl ⟨r, bs, rfl⟩)
      (fun f => .inr ⟨f, rfl⟩)
  · apply Softmax.shapeAt hp d.scheduler hat _ hc hf
    obtain ⟨s,v,k,acc⟩ := d
    cases s <;> first | exact hi | exact (hb ⟨_, _, rfl⟩).elim

theorem shape (hp : Pre p L m) : (code p L g).Shape (Ev p L g) :=
  Code.Shape.of_at (shapeAt hp)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
