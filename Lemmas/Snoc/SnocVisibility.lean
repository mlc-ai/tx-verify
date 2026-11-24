-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcExtend
public import Lemmas.Async.AsyncOrigins
public import Lemmas.Tmem.AllocResult

@[expose] public section

/-! Source extension preserves established visibility. Newly issued operations may
introduce additional pending intents, but cannot erase an old synchronization proof. -/
namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}

theorem snoc_intent_at {v : Ref} {a : Acc} {w : Bool}
    (hv : v.issuer.2 < (X.tr v.issuer.1).length) :
    (X.snoc g e r).Intent v a w ↔ X.Intent v a w := by
  cases v with
  | thread i =>
    simp only [Ref.issuer] at hv
    simp only [Execution.Intent, Execution.Access, Execution.Reads, Execution.Writes,
      Execution.Rmw, snoc_get_old hv]
  | async i p =>
    cases p <;> simp only [Ref.issuer] at hv <;>
      simp only [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint, and_false,
        Execution.Copy, Execution.BulkPrefetch, Execution.MmaFootprint, Execution.MmaIssue,
        Execution.CpIssue,
        Execution.TensorIssue, Execution.TensorStoreIssue, Execution.TensorPrefetchIssue,
        Execution.ClcIssue, snoc_get_old hv]

theorem snoc_intent_mono {v : Ref} {a : Acc} {w : Bool} (hv : X.Intent v a w) :
    (X.snoc g e r).Intent v a w := by
  obtain ⟨ev, he⟩ := intent_issuer hv
  exact (snoc_intent_at (len_of_get he)).mpr hv

theorem snoc_asyncCovers_mono {i : EvId} {p : Part} {l : Loc} (h : AsyncCovers X i p l) :
    AsyncCovers (X.snoc g e r) i p l := by
  obtain ⟨a, w, hi, hc⟩ := h
  exact ⟨a, w, snoc_intent_mono hi, hc⟩

theorem snoc_proxyBefore_mono {i j : EvId} {l : Loc} (h : ProxyBefore L X i j l) :
    ProxyBefore L (X.snoc g e r) i j l := by
  obtain ⟨f, sp, scope, ⟨pc,hf⟩, hthread, hcov, hcluster, hif, hfj⟩ := h
  exact ⟨f, sp, scope, ⟨pc, snoc_get_of_old hf⟩, hthread, hcov, hcluster, baseCausality_snoc hif,
      baseCausality_snoc hfj⟩

theorem snoc_bulkWait_mono {mode : BulkGroup.WaitMode} {i w : EvId}
    (h : BulkWaitsFor X mode i w) : BulkWaitsFor (X.snoc g e r) mode i w := by
  obtain ⟨pc,n,hp,hs⟩ := h
  exact ⟨pc,n,snoc_get_of_old hp,by simpa only [bulkStateBefore,snoc_take (len_of_get hp).le] using
    hs⟩

theorem snoc_notifyOn_mono {i : EvId} {t : Target} {m : Loc} (h : NotifyOn X i t m) :
    NotifyOn (X.snoc g e r) i t m := by
  cases t with
  | copy =>
    obtain ⟨bytes, s, hi, rest⟩ := h
    obtain ⟨pc, hb⟩ := issuedBy_some.mp hi
    exact ⟨bytes, s, issuedBy_some.mpr ⟨pc, snoc_get_of_old hb⟩, rest⟩
  | load =>
    obtain ⟨o, a, ho, ⟨pc, hi⟩, rest⟩ := h
    exact ⟨o, a, ho, ⟨pc, snoc_get_of_old hi⟩, rest⟩
  | cta c =>
    obtain ⟨s, ts, ⟨pc, hi⟩, rest⟩ := h
    exact ⟨s, ts, ⟨pc, snoc_get_of_old hi⟩, rest⟩

theorem snoc_notifies_mono {i : EvId} {p : Part} {n : Ref} {m : Loc} (h : Notifies X i p n m) :
    Notifies (X.snoc g e r) i p n m := by
  have mma : Notifies X i .mmaDone n m → Notifies (X.snoc g e r) i .mmaDone n m := by
    rintro ⟨c, s, rank, rfl, ht, ⟨pc, hc⟩, htg, hn'⟩
    exact ⟨c, s, rank, rfl, (tracksMma_snoc_old (len_of_get hc)).mpr ht,
      ⟨pc, snoc_get_of_old hc⟩, htg, hn'⟩
  have copy : ∀ {p : Part}, (p = .read .copy ∨ p = .write .copy) → Notifies X i p n m →
      Notifies (X.snoc g e r) i p n m := by
    rintro p (rfl | rfl) (⟨hn, ho⟩ | ⟨j, noinc, hn, ⟨h1, h2, ⟨s, ⟨pc, hg⟩, hs⟩, m', ni, pc'', ha'⟩,
      ⟨pc', ha⟩, harr⟩)
    all_goals first
      | exact .inl ⟨hn, snoc_notifyOn_mono ho⟩
      | exact .inr ⟨j, noinc, hn, ⟨h1, h2, ⟨s, ⟨pc, snoc_get_of_old hg⟩, hs⟩, m', ni, pc'',
          snoc_get_of_old ha'⟩, ⟨pc', snoc_get_of_old ha⟩, harr⟩
  cases p
  case mmaRead | mmaDone => exact mma h
  case readCopy => exact copy (.inl rfl) h
  case writeCopy => exact copy (.inr rfl) h
  all_goals
    simp only [Notifies, Part.target] at h ⊢
    try exact ⟨h.1, snoc_notifyOn_mono h.2⟩

theorem snoc_asyncObserved_mono {i w : EvId} {p : Part} {acq : Bool} {ws : MbarScope}
    (h : AsyncObserved X i p w acq ws) : AsyncObserved (X.snoc g e r) i p w acq ws := by
  obtain ⟨n, m, hn, ⟨pc, q, hw⟩, hu⟩ := h
  exact ⟨n, m, snoc_notifies_mono hn, ⟨pc, q, snoc_get_of_old hw⟩, hu⟩

theorem snoc_asyncGroupWait_mono {i w : EvId} (h : AsyncGroupWaitsFor X i w) :
    AsyncGroupWaitsFor (X.snoc g e r) i w := by
  obtain ⟨pc,n,hp,hs⟩ := h
  exact ⟨pc,n,snoc_get_of_old hp,by
    simpa only [asyncStateBefore,snoc_take (len_of_get hp).le] using hs⟩

theorem snoc_groupWaitsFor_mono {k : GroupWait} {i w : EvId} (h : GroupWaitsFor X k i w) :
    GroupWaitsFor (X.snoc g e r) k i w := by
  cases k with
  | bulk mode => exact snoc_bulkWait_mono h
  | cpAsync => exact snoc_asyncGroupWait_mono h

/-- An operation that a group wait covers is an event of `X`. -/
theorem groupWaitsFor_issuer {k : GroupWait} {i w : EvId} (h : GroupWaitsFor X k i w) :
    i.2 < (X.tr i.1).length := by
  cases k with
  | bulk mode =>
    obtain ⟨pc, remaining, -, hobs⟩ := h
    obtain ⟨ev, hev, -⟩ := issue_of_waitsFor (act := bulkAction) (fun g index k i h => by
      unfold bulkAction at h
      split at h <;> grind) hobs
    exact len_of_get hev
  | cpAsync =>
    obtain ⟨pc, remaining, -, hobs⟩ := h
    obtain ⟨ev, hev, -⟩ := issue_of_waitsFor (act := asyncAction) (fun g index k i h => by
      unfold asyncAction at h
      split at h <;> grind) hobs
    exact len_of_get hev

theorem snoc_groupWaitStages_old {i : EvId} {k : GroupWait} (hi : i.2 < (X.tr i.1).length) :
    GroupWaitStages (X.snoc g e r) i k = GroupWaitStages X i k := by
  unfold GroupWaitStages; rw [snoc_get_old hi]

theorem snoc_asyncPresent_mono {i : EvId} {p : Part} (h : X.AsyncPresent i p) :
    (X.snoc g e r).AsyncPresent i p := by
  cases p <;> simp only [Execution.AsyncPresent, snoc_async] at h ⊢
  all_goals try exact h
  case mmaRead isB index =>
    obtain ⟨l,b,footprint,operands,ho,hb⟩ := h
    have hi : X.Intent (.async i (.mmaRead isB index)) {loc:=l,size:=1} false := ⟨rfl,rfl,footprint⟩
    exact ⟨l,b,(snoc_intent_mono hi).2.2,operands,ho,hb⟩

theorem snoc_asyncFinished_mono (_ht : TcEffectsOk X) {i w : EvId} {p : Part}
    (h : AsyncFinished L X i p w) : AsyncFinished L (X.snoc g e r) i p w := by
  rcases h with ⟨k, hv, hw, hs⟩ | ⟨ws, h, hs⟩
  · refine .inl ⟨k, hv, snoc_groupWaitsFor_mono hw, ?_⟩
    rw [snoc_groupWaitStages_old (groupWaitsFor_issuer hw)]
    exact fun q hq => snoc_asyncPresent_mono (hs q hq)
  · exact .inr ⟨ws, snoc_asyncObserved_mono h, hs⟩

theorem snoc_asyncOnlyFinished_mono {i w : EvId} {p : Part}
    (h : AsyncOnlyFinished X i p w) : AsyncOnlyFinished (X.snoc g e r) i p w := by
  obtain ⟨hv, hw, hs⟩ := h
  refine ⟨hv, snoc_groupWaitsFor_mono hw, ?_⟩
  rw [snoc_groupWaitStages_old (groupWaitsFor_issuer hw)]
  exact fun q hq => snoc_asyncPresent_mono (hs q hq)

theorem modelCausality_snoc_mono (ht : TcEffectsOk X) {l : Loc} {v w : Ref}
    (h : modelCausality L X l v w) :
    modelCausality L (X.snoc g e r) l v w := by
  cases v with
  | thread i =>
    cases w with
    | thread j => exact h.imp baseCausality_snoc (fun ha => ha.mono le_snoc)
    | async j q =>
      refine ⟨snoc_asyncCovers_mono h.1, ?_⟩
      rcases h.2 with hp | ⟨hg, hb⟩
      · exact .inl (snoc_proxyBefore_mono hp)
      · obtain ⟨sp, ⟨pc, hc⟩, hgen⟩ := hg
        exact .inr ⟨⟨sp, ⟨pc, snoc_get_of_old hc⟩, hgen⟩, baseCausality_snoc hb⟩
  | async i p =>
    cases w with
    | thread j =>
      obtain ⟨hc,waiter,ho,hb⟩ := h
      refine ⟨snoc_asyncCovers_mono hc,waiter,snoc_asyncFinished_mono ht ho,?_⟩
      exact observedCompletionBefore_map
        (fun ⟨pc, hi⟩ => ⟨pc, snoc_get_of_old hi⟩)
        (fun ⟨pc, hi⟩ => ⟨pc, snoc_get_of_old hi⟩)
        (fun ⟨pc, hw⟩ => ⟨pc, snoc_get_of_old hw⟩)
        baseCausality_snoc snoc_proxyBefore_mono hb
    | async j q =>
      have hpt : ∀ {k : EvId}, PairTc X k → PairTc (X.snoc g e r) k := by
        rintro k (⟨d, s, acc, mask, ⟨pc, hm⟩, hs⟩ | ⟨c, ⟨pc, hc⟩, hn⟩)
        · exact .inl ⟨d, s, acc, mask, ⟨pc, snoc_get_of_old hm⟩, hs⟩
        · exact .inr ⟨c, ⟨pc, snoc_get_of_old hc⟩, hn⟩
      refine ⟨h.1.imp_right fun hp => ⟨hp.1, hp.2.imp hpt hpt⟩,
        AsyncChain.map h.2 ?_ (fun hp _ => snoc_asyncPresent_mono hp)⟩
      intro a b hd
      obtain ⟨hc,hc',hd⟩ := hd
      refine ⟨snoc_asyncCovers_mono hc,snoc_asyncCovers_mono hc',?_⟩
      rcases hd with ⟨waiter,ho,hb⟩ | ⟨waiter,ho,hb⟩
      · exact .inl ⟨waiter,snoc_asyncFinished_mono ht ho,baseCausality_snoc hb⟩
      · exact .inr ⟨waiter,snoc_asyncOnlyFinished_mono ho,(po_snoc_old hb.2.2.1).mpr hb⟩

end
end PTX
