-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The shared objects of a CTA

An mbarrier object of a lane's CTA, named by its offset from the shared base. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {L : Launch} {g : Nat}

/-- The shared object at the shared base plus `o` of a lane's CTA. -/
abbrev obj (L : Launch) (g o : Nat) : Loc := ⟨.shared, g / L.block, L.sharedBase + o⟩

theorem obj_off {h o o' : Nat} (hl : obj L g o = obj L h o') :
    h / L.block = g / L.block ∧ o' = o := by
  simp only [obj, Loc.mk.injEq, true_and] at hl
  omega

theorem obj_inj {o o' : Nat} (h : obj L g o = obj L g o') : o = o' :=
  (obj_off h).2.symm

theorem obj_cta {h : Nat} (hc : h / L.block = g / L.block) (o : Nat) : obj L h o = obj L g o := by
  simp only [obj, hc]

end
end PTX.Kernels.TmlFa4Fwd.Proof
