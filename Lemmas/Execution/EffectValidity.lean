-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness

@[expose] public section

namespace PTX

/-- A bundle of existing Core obligations, for lemmas that do not need memory
read-source consistency. This introduces no execution rule or assumption. -/
structure EffectValidity (L : Launch) (X : Execution) : Prop where
  tma : TmaOk X
  tensor : TensorOk L X
  store : TensorStoreOk L X
  clc : ClcOk L X
  tmemPair : Tmem.Pair.HistoriesOk L X
  tcCommit : AsyncCopy.CommitOk X

theorem Consistent.effectValidity {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (h : Consistent L K A mem0 X) : EffectValidity L X :=
  ⟨h.tma, h.tensor, h.store, h.clc, h.tmemPair, h.tcCommit⟩

end PTX
