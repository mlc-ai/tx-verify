-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Snoc.SnocObjectHistory
public import Lemmas.Snoc.PlainAsyncExtend
public import Lemmas.Snoc.SnocReady

@[expose] public section

/-! Source/object instruction extension. The caller proves the actual object transition,
async validity and memory-order constraints; source traces, reads-from, shuffle values and
readiness are derived here. No kernel-specific restriction enters the semantics. -/
namespace PTX
open AsyncCopy
noncomputable section

/-- **Appending an event that reads and writes no memory**, with object histories that only
gain records of the appended event. The thread's previous last event is ready (`LastReady`), the
appended event is ready if it has returned, and the execution-order axioms, the memory axioms of
the extension and its metadata obligations are given. -/
theorem consistent_snoc_history {L : Launch} {X : Execution} {g : Nat} {e : Event}
    {r : Nat → Option Ref} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    {t t1 : TState} {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) (hk : ∀ k, e.kind ≠ .tc k)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hrd : ∀ a bs, e.kind ≠ .rd a bs) (hwr : ∀ a bs, e.kind ≠ .wr a bs)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    (hexit : isMatrix e = true → ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hlast : LastReady L X g)
    {records : Loc → List (MBarrier.Record Ref)} (hrec : SnocRecords X g records)
    (hnew : Returned (X.snocHistory g e r records) (X.newId g) →
      Ready L (X.snocHistory g e r records) (X.newId g))
    (htma : TmaOk (X.snocHistory g e r records))
    (horder : OrderOk L K A (X.snocHistory g e r records))
    (hnf : NoFuture L (X.snocHistory g e r records))
    (hhid : Hidden L (X.snocHistory g e r records))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snocHistory g e r records))
    (hextra : ExtensionObligations L A (X.snocHistory g e r records)) :
    Consistent L K A mem0 (X.snocHistory g e r records) := by
  refine {
    thr := ?_, outside := ?_, rf := snoc_history_rf hX hk hrd hwr hrmw records,
    ctaBar := hextra.ctaBar, cluster := hextra.cluster,
    dependency := ⟨ready_snocHistory hX hrec hexit hlast hnew, horder.depAcyclic⟩,
    shfl := snoc_shflOk (r := r) hX.shfl hns, vote := hextra.vote, warpValue := hextra.warpValue,
    matrix := hextra.matrix, elect := hextra.elect, warpBar := hextra.warpBar,
    observation := horder.observation, object := horder.object,
    asyncObject := horder.asyncObject, initFence := horder.initFence,
    noFuture := hnf, hidden := hhid, tma := htma, clc := hextra.clc,
    tensor := hextra.tensor, store := hextra.store, reduce := hextra.reduce,
    atomic := hextra.atomic, fenceSc := hextra.fenceSc,
    tmemPair := hextra.tmemPair, tmemPairCompletion := hextra.tmemPairCompletion,
    tmemPairResult := hextra.tmemPairResult, tcCommit := hextra.tcCommit,
    mmaCompletion := hextra.mmaCompletion, tcRead := hextra.tcRead, asm := hasm }
  · intro h hh
    by_cases hhg : h = g
    · subst hhg
      refine ⟨o, ?_⟩
      change Run K A L h {} ((X.snoc h e r).tr h) o
      rw [snoc_tr, ite_eq_left rfl]; exact hrun.snoc hl he
    · change Produces K A L h ((X.snoc g e r).tr h)
      rw [snoc_tr, ite_eq_right hhg]; exact hX.thr h hh
  · intro h hh
    change (X.snoc g e r).tr h = []
    rw [snoc_tr, ite_eq_right (by omega)]; exact hX.outside h hh

end
end PTX
