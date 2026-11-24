-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Execution.Legacy
public import Lemmas.Tmem.TmemPairHistory
public import Lemmas.Snoc.SnocResourceWaiting
public import Lemmas.Snoc.Collectives
public import Lemmas.CtaBarrier.CtaBarrierExecution
public import Lemmas.Cluster.ClusterBarrierExecution
public import Lemmas.Tcgen05.MmaOperandObservations
public import Lemmas.Tcgen05.TcMmaReadMono
public import Lemmas.Clc.ClcExecution

@[expose] public section

namespace PTX
noncomputable section

theorem Execution.Legacy.snoc {X : Execution} {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} (hx : X.Legacy) (hk : e.kind.Legacy) :
    (X.snoc g e r).Legacy := by
  intro i pc kind hp
  rw [snoc_get] at hp
  split_ifs at hp
  · cases e
    cases hp
    exact hk
  · exact hx _ _ _ hp

end
end PTX
