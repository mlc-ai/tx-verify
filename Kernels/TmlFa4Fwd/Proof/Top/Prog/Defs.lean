-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Released

@[expose] public section

/-! # The shapes of the progress classes

What the progress class files (`Top/Prog/<Class>.lean`) state their open parts with: the descent
step of an obligation under tml-fa4's time table (`StepsAt`), a released pending lane whose end
state satisfies a predicate (`RelSteps`), and the loader's waits (`Loader.isWait`). This file
imports no safety class, so a safety class's proof does not rebuild the progress classes. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The loader's polls: the empty-slot waits, the TMA groups' waits and the drain's waits. -/
def Loader.isWait : Loader.Site → Prop
  | .slot _ _ | .tw _ | .dw _ | .dq => True
  | _ => False

instance (s : Loader.Site) : Decidable (Loader.isWait s) := by
  cases s <;> simp only [Loader.isWait] <;> infer_instance

/-- The descent step of an obligation under tml-fa4's time table. -/
abbrev StepsAt (p : Params) (L : Launch) (m : Mem0) (X : Execution) (o : Descent.Obligation) :
    Prop :=
  Sched.Steps (Progress.timed p L) m X o

/-- A released pending lane of a maximal execution whose state at the end of its trace
satisfies `P` steps. -/
def RelSteps (p : Params) (L : Launch) (m : Mem0) (P : (g : Nat) → (thread p L g).D → Prop) :
    Prop :=
  ∀ X, Maximal L kernel Assumptions.all m X → ∀ g σ, Frame.Pending L X g →
    Step.Released L X g → Frame.stateAt (thread p L) X g (X.tr g).length = some (some σ) →
    P g σ → StepsAt p L m X (.thread g)

/-- **A state at a warp collective**: its instruction is outside the released template and is a
warp collective. -/
def CollAt (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Prop :=
  RestAt p L g σ ∧ ∀ ins, kernel.code[(thread p L g).pc σ]? = some ins →
    Descent.opKind ins.op = .warp

/-- The warp key of a lane: its CTA and warp. -/
def warpKey (L : Launch) (g : Nat) : Nat × Nat := (g / L.block, g % L.block / 32)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
