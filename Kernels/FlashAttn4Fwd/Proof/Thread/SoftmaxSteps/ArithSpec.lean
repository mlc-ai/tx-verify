-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.WaitLd

@[expose] public section

/-! # The statements of the arithmetic steps

The four steps whose segments compute the tile's arithmetic, stated here and proved in their
own files:

* `step_ldW3_gen0 : StepSpec (.ldW false 3)`: the first tile's last implicit wait, the row
  maximum, to the named barrier `gen 0`;
* `step_gen0_pst : StepSpec (.gen 0)`: the first tile's named barrier, the exponentials and
  packs, to its first probability store;
* `step_ldW3_alphaSt : StepSpec (.ldW true 3)`: a loop tile's last implicit wait, the new
  maximum and `α`, to the store of `α`;
* `step_gen1_pst : StepSpec (.gen 1)`: a loop tile's named barrier, the exponentials and packs,
  to its first probability store.

`StepSpec s` is the obligation of the site machine at a state of site `s` (`Softmax.stepAt`):
every event fired at a concrete state of it steps to its successor (`Step`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Every event fired at a concrete state of a state at site `s` steps to its successor. -/
def StepSpec (s : Site) : Prop :=
  ∀ {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}
    {ins : Instr}, Pre P L mem0 → d.site = s → Inv L g d → AtS L g d t →
    kernel.code[d.site.pc]? = some ins →
    Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) → Step L g d e u

/-- The four arithmetic steps. -/
structure ArithSteps : Prop where
  ldW3_gen0 : StepSpec (.ldW false 3)
  gen0_pst : StepSpec (.gen 0)
  ldW3_alphaSt : StepSpec (.ldW true 3)
  gen1_pst : StepSpec (.gen 1)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
