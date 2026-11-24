-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcCollectiveOrdinaryWaiting

@[expose] public section

/-! Appending a warp-collective TC instruction preserves the full memory/dependency
model. Existing independent effects and mbarrier histories are not reset. The caller
proves the new allocation/load value obligations through `TmaOk`, and that the thread's previous
last event is ready (`LastReady`). -/
namespace PTX
noncomputable section

theorem consistent_tccoll_snoc {L : Launch} {X : Execution} {g : Nat} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {e : Event} {r : Nat → Option AsyncCopy.Ref}
    (hX : Consistent L K A mem0 X) (hg : g < L.threads) {t t1 : TState} {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) (hcoll : isTcColl e = true) (hlast : LastReady L X g)
    (hextra : ExtensionObligations L A (X.snoc g e r))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e r))
    (htma : TmaOk (X.snoc g e r)) :
    Consistent L K A mem0 (X.snoc g e r) :=
  consistent_tccoll_snoc_of_orderOk hX hg hrun hl he hcoll hlast
    ((snoc_tccoll_sinkFrame hX hg hcoll).orderOk hX.orderOk) hextra hasm htma

end
end PTX
