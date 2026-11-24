-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocObjectVisibility
public import Lemmas.Snoc.SnocAsyncSilent
public import Lemmas.Order.CommitOperandFrame
public import Lemmas.Tmem.AllocResult

@[expose] public section

/-! # Causality between old accesses after an append

Appending an event of any kind to a thread adds no asynchronous effect, so once the base causality
into old events is unchanged (`hbo`, which the callers have from the kind of the event: no barrier,
warp barrier, releasing arrival or `fence.sc`), the model causality between two accesses issued in
the old execution is unchanged too (`modelCausality_snoc_old_of`), and so is their byte causality
(`byteCausality_snoc_old_of`). A new `tcgen05.commit` tracks
old Tensor Core operations, but it has no notification yet (`CommitOk`), so no old wait observes
it. -/

namespace PTX.TcIssue
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}

theorem started_issuer_lt (ht : TcEffectsOk X) {i : EvId}
    (hs : X.async.mmaStarted i = true) : i.2 < (X.tr i.1).length := by
  rcases ht.1 i hs with ⟨d, s, accum, mask, operands, ⟨pc, hi⟩, _⟩ |
    ⟨c, operands, ⟨pc, hi⟩, _⟩ | ⟨s, operands, ⟨pc, hi⟩, _⟩ <;>
    exact len_of_get hi

theorem snoc_mmaRead_old (ht : TcEffectsOk X) {i : EvId} {isB : Bool}
    {k : Nat} {loc : Loc} {byte : Option Byte} :
    (X.snoc g e r).MmaRead i isB k loc byte ↔ X.MmaRead i isB k loc byte := by
  cases ho : X.async.mmaOperands i with
  | none => simp [Execution.MmaRead, Execution.snoc, ho]
  | some operands =>
    have hs : X.async.mmaStarted i = true := by simp [Snapshot.mmaStarted, ho]
    simp only [Execution.MmaRead, Execution.MmaFootprint, Execution.MmaIssue, Execution.CpIssue,
      snoc_get_old (started_issuer_lt ht hs), snoc_async]

theorem snoc_asyncPresent (ht : TcEffectsOk X) {i : EvId} {p : Part} :
    (X.snoc g e r).AsyncPresent i p ↔ X.AsyncPresent i p := by
  cases p <;> first
    | rfl
    | simp only [Execution.AsyncPresent, snoc_mmaRead_old ht]

end
end PTX.TcIssue

namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}

/-- A group wait of an old event after any append covers the stages it covers in `X`. -/
theorem snoc_groupWait_old (ht : TcEffectsOk X) {x w : EvId} {k : GroupWait}
    (hw : w.2 < (X.tr w.1).length) (hgw : GroupWaitsFor (X.snoc g e r) k x w)
    (hs : ∀ q ∈ GroupWaitStages (X.snoc g e r) x k, (X.snoc g e r).AsyncPresent x q) :
    GroupWaitsFor X k x w ∧ ∀ q ∈ GroupWaitStages X x k, X.AsyncPresent x q :=
  snoc_groupWait_retained (TcIssue.snoc_asyncPresent ht).mp hw hgw hs

theorem snoc_asyncFinished_old (hv : EffectValidity L X) {x w : EvId} {p : Part}
    (hw : w.2 < (X.tr w.1).length)
    (h : AsyncFinished L (X.snoc g e r) x p w) : AsyncFinished L X x p w := by
  rcases h with ⟨k, hvis, hgw, hs⟩ | ⟨ws, h, hs⟩
  · obtain ⟨h1, h2⟩ := snoc_groupWait_old hv.tma.2.1 hw hgw hs
    exact .inl ⟨k, hvis, h1, h2⟩
  · exact .inr ⟨ws, snoc_asyncObserved_old hv hw h, hs⟩

theorem snoc_asyncOnlyFinished_old (ht : TcEffectsOk X) {x w : EvId} {p : Part}
    (hw : w.2 < (X.tr w.1).length)
    (h : AsyncOnlyFinished (X.snoc g e r) x p w) : AsyncOnlyFinished X x p w := by
  obtain ⟨hvis, hgw, hs⟩ := h
  obtain ⟨h1, h2⟩ := snoc_groupWait_old ht hw hgw hs
  exact ⟨hvis, h1, h2⟩

theorem snoc_asyncCovers_old {x : EvId} {p : Part} {l : Loc} (hx : x.2 < (X.tr x.1).length)
    (h : AsyncCovers (X.snoc g e r) x p l) : AsyncCovers X x p l := by
  obtain ⟨a, w, ha, hc⟩ := h
  exact ⟨a, w, (snoc_intent_at (g := g) (e := e) (r := r) (v := .async x p) hx).mp ha, hc⟩

section
variable (hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
  (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f))
include hbo

theorem snoc_asyncBefore_old (hv : EffectValidity L X) {l : Loc} {a b : EvId × Part}
    (ha : a.1.2 < (X.tr a.1.1).length) (hb : b.1.2 < (X.tr b.1.1).length)
    (h : AsyncBefore L (X.snoc g e r) l a b) : AsyncBefore L X l a b := by
  obtain ⟨hc, hc', hh⟩ := h
  refine ⟨snoc_asyncCovers_old ha hc, snoc_asyncCovers_old hb hc', ?_⟩
  rcases hh with ⟨w, ho, hafter⟩ | ⟨w, ho, hafter⟩
  · have hafter' := (hbo hb).mp hafter
    exact .inl ⟨w, snoc_asyncFinished_old hv (baseCausality_events hafter').1 ho, hafter'⟩
  · have hafter' := (po_snoc_old (g := g) (e := e) (r := r) hb).mp hafter
    have hwo : w.2 < (X.tr w.1).length := by rw [hafter'.1]; have := hafter'.2.1; omega
    exact .inr ⟨w, snoc_asyncOnlyFinished_old hv.tma.2.1 hwo ho, hafter'⟩

/-- **Causality between two accesses issued in `X` is that of `X`** after any append whose base
causality into old events is that of `X`. -/
theorem modelCausality_snoc_old_of (hv : EffectValidity L X) {x y : Ref} {l : Loc}
    (hx : x.issuer.2 < (X.tr x.issuer.1).length) (hy : y.issuer.2 < (X.tr y.issuer.1).length)
    (h : modelCausality L (X.snoc g e r) l x y) : modelCausality L X l x y := by
  cases x with
  | thread x =>
    cases y with
    | thread y => exact h.imp (hbo hy).mp fun h => h.of_prefix le_snoc hx hy
    | async y q =>
      refine ⟨snoc_asyncCovers_old hy h.1, ?_⟩
      rcases h.2 with hp | ⟨⟨s, ⟨pc, hc⟩, hgen⟩, hb⟩
      · exact .inl ((Kind.AsyncSilent.proxyBefore_snoc_old hbo hy).mp hp)
      · exact .inr ⟨⟨s, ⟨pc, (snoc_get_old (r := r) hy).symm.trans hc⟩, hgen⟩, (hbo hy).mp hb⟩
  | async x p =>
    cases y with
    | thread y =>
      obtain ⟨hc, w, ho, hb⟩ := h
      have hb' : ObservedCompletionBefore L X l x p w y := by
        rcases hb with hb | hb
        · left
          cases p <;> first
            | exact (Kind.AsyncSilent.proxyBefore_snoc_old hbo hy).mp hb
            | exact (hbo hy).mp hb
        · right
          exact (TcReadReuseBefore.congr L (snoc_get_old hx).symm (snoc_get_old hy).symm
            (hbo hy).symm).mpr hb
      have hwo : w.2 < (X.tr w.1).length := by
        rcases hb' with hb' | hb'
        · cases p <;> first
            | exact (baseCausality_events hb').1
            | (obtain ⟨f, -, -, -, -, -, -, hwf, -⟩ := hb'; exact (baseCausality_events hwf).1)
        · exact (baseCausality_events hb'.base).1
      exact ⟨snoc_asyncCovers_old hx hc, w, snoc_asyncFinished_old hv hwo ho, hb'⟩
    | async y q =>
      have transport {a b : EvId × Part} (h : AsyncChain L (X.snoc g e r) l a b) :
          a.1.2 < (X.tr a.1.1).length → b.1.2 < (X.tr b.1.1).length →
          AsyncChain L X l a b := by
        induction h with
        | direct hd =>
          intro ha hb
          exact .direct (snoc_asyncBefore_old hbo hv ha hb hd)
        | tail _ hp hd ih =>
          intro ha hb
          have hp' := (TcIssue.snoc_asyncPresent hv.tma.2.1).mp hp
          obtain ⟨event, he⟩ := asyncPresent_issuer hv hp'
          have hm := len_of_get he
          exact .tail (ih ha hm) hp' (snoc_asyncBefore_old hbo hv hm hb hd)
      have hpt : ∀ {k : EvId}, k.2 < (X.tr k.1).length → PairTc (X.snoc g e r) k → PairTc X k := by
        rintro k hk (⟨d, s, acc, mask, ⟨pc, hm⟩, hs⟩ | ⟨c, ⟨pc, hc⟩, hn⟩)
        · exact .inl ⟨d, s, acc, mask, ⟨pc, by rwa [snoc_get_old hk] at hm⟩, hs⟩
        · exact .inr ⟨c, ⟨pc, by rwa [snoc_get_old hk] at hc⟩, hn⟩
      exact ⟨h.1.imp_right fun hp => ⟨hp.1, hp.2.imp (hpt hx) (hpt hy)⟩, transport h.2 hx hy⟩

/-- **Byte causality between two accesses issued in `X` is that of `X`** after any append whose
base causality into old events is that of `X`: the base paths are those of `X`
(`modelCausality_snoc_old_of`), and an old wait observes only commits of `X`. -/
theorem byteCausality_snoc_old_of (hv : EffectValidity L X) {x y : Ref} {l : Loc}
    (hx : x.issuer.2 < (X.tr x.issuer.1).length) (hy : y.issuer.2 < (X.tr y.issuer.1).length)
    (h : ByteCausality L (X.snoc g e r) l x y) : ByteCausality L X l x y :=
  ByteCausality.le_reflect le_snoc hv.tma.2.1 hv.tcCommit
    (fun hf h => modelCausality_snoc_old_of hbo hv hx hf h)
    (fun hw h => snoc_asyncObserved_old hv hw h) hy h

end

end
end PTX
