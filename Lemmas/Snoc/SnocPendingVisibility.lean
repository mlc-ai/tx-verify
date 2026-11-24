-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocObjectVisibility
public import Lemmas.Snoc.SnocAsyncSilent

@[expose] public section

namespace PTX
open PTX AsyncCopy

section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}

private theorem snoc_asyncCovers_old {i : EvId} {p : Part} {loc : Loc}
    (hi : i.2 < (X.tr i.1).length) :
    AsyncCovers (X.snoc g e r) i p loc → AsyncCovers X i p loc := by
  rintro ⟨a,w,hIntent,hCover⟩
  exact ⟨a,w,(snoc_intent_at (v := .async i p) hi).mp hIntent,hCover⟩

private theorem snoc_asyncFinished_retained (hv : EffectValidity L X)
    (hPresent : ∀ {i p}, (X.snoc g e r).AsyncPresent i p → X.AsyncPresent i p)
    {x w : EvId} {p : Part} (hw : w.2 < (X.tr w.1).length)
    (h : AsyncFinished L (X.snoc g e r) x p w) : AsyncFinished L X x p w := by
  rcases h with ⟨k,hVis,hGroup,hDone⟩ | ⟨ws,hObserve,hScope⟩
  · obtain ⟨hGroup',hDone'⟩ := snoc_groupWait_retained hPresent hw hGroup hDone
    exact .inl ⟨k,hVis,hGroup',hDone'⟩
  · exact .inr ⟨ws,snoc_asyncObserved_old hv hw hObserve,hScope⟩

private theorem snoc_asyncOnlyFinished_retained
    (hPresent : ∀ {i p}, (X.snoc g e r).AsyncPresent i p → X.AsyncPresent i p)
    {x w : EvId} {p : Part} (hw : w.2 < (X.tr w.1).length)
    (h : AsyncOnlyFinished (X.snoc g e r) x p w) : AsyncOnlyFinished X x p w := by
  obtain ⟨hVis,hGroup,hDone⟩ := h
  obtain ⟨hGroup',hDone'⟩ := snoc_groupWait_retained hPresent hw hGroup hDone
  exact ⟨hVis,hGroup',hDone'⟩

private theorem snoc_asyncBefore_old (hv : EffectValidity L X)
    (hPresent : ∀ {i p}, (X.snoc g e r).AsyncPresent i p → X.AsyncPresent i p)
    (hBase : ∀ {x y : EvId}, y.2 < (X.tr y.1).length →
      (baseCausality L (X.snoc g e r) x y ↔ baseCausality L X x y))
    {loc : Loc} {a b : EvId × Part}
    (ha : a.1.2 < (X.tr a.1.1).length) (hb : b.1.2 < (X.tr b.1.1).length) :
    AsyncBefore L (X.snoc g e r) loc a b → AsyncBefore L X loc a b := by
  rintro ⟨hac,hbc,⟨w,hFinish,hAfter⟩ | ⟨w,hFinish,hAfter⟩⟩
  · have hOld := (hBase hb).mp hAfter
    exact ⟨snoc_asyncCovers_old ha hac,snoc_asyncCovers_old hb hbc,
      .inl ⟨w,snoc_asyncFinished_retained hv hPresent (baseCausality_events hOld).1 hFinish,hOld⟩⟩
  · have hOld := (po_snoc_old (g := g) (e := e) (r := r) hb).mp hAfter
    have hw : w.2 < (X.tr w.1).length := by
      rw [hOld.1]
      exact hOld.2.1.trans hb
    exact ⟨snoc_asyncCovers_old ha hac,snoc_asyncCovers_old hb hbc,
      .inr ⟨w,snoc_asyncOnlyFinished_retained hPresent hw hFinish,hOld⟩⟩

/-- With all async effects retained, an append preserving base paths into old instructions
also preserves their byte visibility. -/
theorem snoc_modelCausality_retained_effects (hv : EffectValidity L X)
    (hPresent : ∀ {i p}, (X.snoc g e r).AsyncPresent i p → X.AsyncPresent i p)
    (hBase : ∀ {x y : EvId}, y.2 < (X.tr y.1).length →
      (baseCausality L (X.snoc g e r) x y ↔ baseCausality L X x y))
    (hAlloc : ∀ {x y : EvId} {l : Loc}, y.2 < (X.tr y.1).length →
      (Tmem.Pair.AllocResultBefore L (X.snoc g e r) l x y ↔
        Tmem.Pair.AllocResultBefore L X l x y))
    {loc : Loc} {src dst : Ref} (hx : src.issuer.2 < (X.tr src.issuer.1).length)
    (hy : dst.issuer.2 < (X.tr dst.issuer.1).length) :
    modelCausality L (X.snoc g e r) loc src dst ↔ modelCausality L X loc src dst := by
  refine ⟨?_,modelCausality_snoc_mono hv.tma.2.1⟩
  intro hc
  cases src with
  | thread x =>
    cases dst with
    | thread y => exact hc.imp (hBase hy).mp (hAlloc hy).mp
    | async y p =>
      refine ⟨snoc_asyncCovers_old hy hc.1,?_⟩
      rcases hc.2 with h | ⟨⟨spec,⟨pc,he⟩,hg⟩,h⟩
      · exact .inl ((Kind.AsyncSilent.proxyBefore_snoc_old hBase hy).mp h)
      · exact .inr ⟨⟨spec,⟨pc,(snoc_get_old (r := r) hy).symm.trans he⟩,hg⟩,(hBase hy).mp h⟩
  | async x p =>
    cases dst with
    | thread y =>
      obtain ⟨hCover,w,hFinish,hAfter⟩ := hc
      have hOld : ObservedCompletionBefore L X loc x p w y := by
        rcases hAfter with hAfter | hReuse
        · apply Or.inl
          cases p <;> first
            | exact (Kind.AsyncSilent.proxyBefore_snoc_old hBase hy).mp hAfter
            | exact (hBase hy).mp hAfter
        · exact .inr ((TcReadReuseBefore.congr L (snoc_get_old hx) (snoc_get_old hy)
            (hBase hy)).mp hReuse)
      have hw : w.2 < (X.tr w.1).length := by
        rcases hOld with hOld | hReuse
        · cases p <;> first
            | exact (baseCausality_events hOld).1
            | (obtain ⟨f,_,_,_,_,_,_,hwf,_⟩ := hOld; exact (baseCausality_events hwf).1)
        · exact (baseCausality_events (hReuse.base L)).1
      exact ⟨snoc_asyncCovers_old hx hCover,w,
        snoc_asyncFinished_retained hv hPresent hw hFinish,hOld⟩
    | async y q =>
      have chain {a b : EvId × Part} (h : AsyncChain L (X.snoc g e r) loc a b) :
          a.1.2 < (X.tr a.1.1).length → b.1.2 < (X.tr b.1.1).length → AsyncChain L X loc a b := by
        induction h with
        | direct h =>
          intro ha hb
          exact .direct (snoc_asyncBefore_old hv hPresent hBase ha hb h)
        | tail _ hp hd ih =>
          intro ha hb
          have hp' := hPresent hp
          obtain ⟨_,he⟩ := asyncPresent_issuer hv hp'
          have hIndex := len_of_get he
          exact .tail (ih ha hIndex) hp' (snoc_asyncBefore_old hv hPresent hBase hIndex hb hd)
      have pair {i : EvId} (hi : i.2 < (X.tr i.1).length) :
          PairTc (X.snoc g e r) i → PairTc X i := by
        rintro (⟨d,s,acc,mask,⟨pc,h⟩,hGroup⟩ | ⟨c,⟨pc,h⟩,hGroup⟩)
        · exact .inl ⟨d,s,acc,mask,⟨pc,(snoc_get_old (r := r) hi).symm.trans h⟩,hGroup⟩
        · exact .inr ⟨c,⟨pc,(snoc_get_old (r := r) hi).symm.trans h⟩,hGroup⟩
      exact ⟨hc.1.imp_right (fun h => ⟨h.1,h.2.imp (pair hx) (pair hy)⟩),chain hc.2 hx hy⟩

/-- A non-TC append preserving base paths into older instructions also preserves visibility. -/
theorem snoc_modelCausality_old_effects (hv : EffectValidity L X) (hNotTc : ∀ k, e.kind ≠ .tc k)
    (hBase : ∀ {x y : EvId}, y.2 < (X.tr y.1).length →
      (baseCausality L (X.snoc g e r) x y ↔ baseCausality L X x y))
    (hAlloc : ∀ {x y : EvId} {l : Loc}, y.2 < (X.tr y.1).length →
      (Tmem.Pair.AllocResultBefore L (X.snoc g e r) l x y ↔
        Tmem.Pair.AllocResultBefore L X l x y))
    {loc : Loc} {src dst : Ref} (hx : src.issuer.2 < (X.tr src.issuer.1).length)
    (hy : dst.issuer.2 < (X.tr dst.issuer.1).length) :
    modelCausality L (X.snoc g e r) loc src dst ↔ modelCausality L X loc src dst :=
  snoc_modelCausality_retained_effects hv (snoc_asyncPresent_of_not_tc hNotTc).mp hBase hAlloc
    hx hy

end
end PTX
