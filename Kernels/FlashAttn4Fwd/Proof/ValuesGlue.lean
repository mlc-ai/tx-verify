-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.ResultFacts
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ValuesRun
public import Kernels.FlashAttn4Fwd.Proof.Safety.HasUb

@[expose] public section

/-! # `ResultGoal` from the value facts

This file sits at the top of the proof tree, outside the layer order: it discharges the value
premise of `result_goal_of` (`OutputValues`) with `Values.outputValues`, from the threads'
computations (`ValueFacts`) and the value links between the roles (`ScoreLoads`, `StatsReads`,
`PvChain`), collected per consistent complete execution in `ValueInputs`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The premises of the output values, for one execution. -/
structure ValueInputs (P : Params) (L : Launch) (X : Execution) : Prop where
  facts : ValueFacts P L X
  scores : ScoreLoads P L X
  stats : StatsReads L X
  pv : PvChain P L X
  /-- Every Tensor Memory load returns single-precision floats. -/
  loads : Safety.LoadFloats L X
  /-- Every correction `ld.shared` returns the bytes of a single-precision float. -/
  statsReads : Safety.StatsFloats L X

/-- **`ResultGoal`** from the thread layer's exports (`ResultRemaining`) and the value premises
(`ValueInputs`). -/
theorem result_goal_of_values {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hR : ResultRemaining P L mem0)
    (hv : ∀ X, Consistent L kernel asms mem0 X → Complete L X → ValueInputs P L X) :
    ResultGoal kernel asms L mem0 (Post P mem0) :=
  result_goal_of hpre hR fun X hX hd =>
    have hi := hv X hX hd
    Values.outputValues hpre hi.facts hi.scores hi.stats hi.pv hi.loads hi.statsReads

end

end PTX.Kernels.FlashAttn4Fwd.Proof
