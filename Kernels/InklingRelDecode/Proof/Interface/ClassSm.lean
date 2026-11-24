-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Facts
public import Kernels.InklingRelDecode.Proof.Thread.SmDischarge

@[expose] public section

/-!
# The softmax region's obligations, discharged (`Open.smOb`)

`DComp.SmObligations` is `score` (the `Code.StepAt` of 17 sites, proved by `stepAt_score`) and
`exit` (the link from the loop's last event to the bridge, `exit_of_slack`). The one premise of
`exit` that is about the launch is `ScoreRest.rowSlack`:
`(d.e.splits * d.e.ntok + 11) * 12 * 128 ≤ 2 ^ 31` for the entry numbers of every state. It is a
field of `Sm.Ent.Ok` now (`Ent.Ok.slack`: proved at
the region's first state by `SmEntry.entOk` from `Pre.outRangeSlack`, kept by every successor,
which keeps `d.e`), so `Sm.Inv` gives it and `SmOb` has no premise left.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0}

/-- **`ScoreRest`**: the row slack of the entry numbers, from the invariant. -/
theorem scoreRest (g : Nat) : DComp.ScoreRest Q L mem0 g where
  rowSlack := fun _ _ hi => hi.ok.slack

/-- **The softmax region's obligations of every default-partition thread** (the field
`Open.smOb`). -/
theorem smOb : SmOb Q L mem0 :=
  fun g _ _ => DComp.smObligations_of_rest (scoreRest g)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
