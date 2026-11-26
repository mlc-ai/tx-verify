-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.CtaBarFinishExit
public import Lemmas.Quiet.Base

@[expose] public section

/-! # Named-barrier release under quiet extensions

`NamedBar.sync_release` under `Assumption.WfQuiet`. -/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- The step well-formedness rule supports releasing all arrival participants. -/
theorem sync_releaseQ (hmax : Maximal L K A mem0 X) {sel : Nat → Bool}
    (hA : Assumption.WfQuiet sel L K mem0 A)
    (hf : ∀ Y, Consistent L K A mem0 Y → ¬ CtaBarFault L Y) {count : Option Nat}
    {p : Finset Nat} {id : Nat} (hG : Shape L count p id) (hS : Sources L X count p id)
    {g pc : Nat} (hg : g < L.threads)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id count pc)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (g / L.block * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (g / L.block * L.block + y)).take j).countP (Execution.isBarId id) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Step.Released L Y g :=
  sync_release_of_wf hmax hA.ctaHistory hf hG hS hg hlast hlane

end

end PTX.NamedBar
