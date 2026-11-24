-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
public import Lemmas.Flow.UbStop

@[expose] public section

/-! # The softmax fragment's open states and premises

The numeric states not stepped yet, and the two premises about them that the thread machine and the
following theorems name. No step proof is imported here. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The first P store of a round with bias waits for the round's score loads at sub-step 0
(`delayedTmem`). -/
def Site.delayed : Site → Bool
  | .pst .first 0 | .pst .bias 0 => true
  | _ => false

/-- An event that is no undefined behaviour. -/
abbrev NoUb (_ : D) (e : Event) : Prop := ∀ f, e.kind ≠ .ub f

/-- **The numeric states not stepped by `stepAt_ctl`**: the closing poll of a bias round. -/
def D.numeric (d : D) : Bool :=
  match d.site with
  | .pwend .bias => true
  | _ => false

/-- The states whose event stores a data register: a P store other than the implicit wait of a
delayed one, a statistics store, a final store. -/
def D.dataStore (d : D) : Bool :=
  match d.site with
  | .stat _ | .fin _ => true
  | .pst r q => !((Site.pst r q).delayed && d.k.val == 0)
  | _ => false

/-- **Numeric steps**: the step obligation at the numeric states. -/
def NumSteps (p : Params) (L : Launch) (g : Nat) : Prop :=
  ∀ d : D, d.numeric = true → (codeD p L g).StepAt d

/-- **Data stores are defined**: no event fired at a data-store state is undefined behaviour. -/
def DataStoreSafe (p : Params) (L : Launch) (g : Nat) : Prop :=
  ∀ d : D, d.dataStore = true → (codeD p L g).ShapeAt NoUb d

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
