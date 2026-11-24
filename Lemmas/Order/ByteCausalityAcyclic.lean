-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandOrder
public import Lemmas.Order.GuardObserver
import Lemmas.Order.Order
import Lemmas.Order.OrderWaits
import Lemmas.Tmem.AllocResultDependency

@[expose] public section

namespace PTX

open AsyncCopy

variable {L : Launch} {K : Kernel} {X : Execution}

/-- Expand byte causality into base causality and dependency paths through synchronization
guards. The intermediate issuing instruction may be a later notification instruction. -/
private def IssuePath (L : Launch) (K : Kernel) (X : Execution) (e f : Ref) : Prop :=
  baseCausality L X e.issuer f.issuer ∨
    ∃ n w, (n = e.issuer ∨ po X e.issuer n) ∧
      Relation.TransGen (DepStep L K X) (.thread n, false) (.thread w, true) ∧
      GuardSource K X w ∧ (∀ m tx count sc, ¬ X.Arrive w m tx count true sc) ∧
      baseCausality L X w f.issuer

private theorem IssuePath.of_completion (hv : EffectValidity L X) (hg : SyncGuarded L K X)
    {i w : EvId} {p : Part} {f : Ref}
    (hf : AsyncFinished L X i p w ∨ AsyncOnlyFinished X i p w)
    (hb : baseCausality L X w f.issuer) : IssuePath L K X (.async i p) f := by
  obtain ⟨n, hn, path, guard, hna⟩ := observer_enables hv hg hf
  exact .inr ⟨n, w, hn, path, guard, hna, hb⟩

private theorem IssuePath.of_allocResult {l : Loc} {store load : EvId}
    (h : Tmem.Pair.AllocResultBefore L X l store load) :
    IssuePath L K X (.thread store) (.thread load) := by
  obtain ⟨j, dst, a, bytes, hresult, hj, hbyte, ⟨tag, hget⟩, hrdByte⟩ := h
  obtain ⟨out, hw⟩ := hresult.writes
  have hfill : Tmem.Pair.AllocResultFill L X (load.1, j) (.thread store) := ⟨dst, hresult⟩
  obtain ⟨hwarp, hleader, _, _, k, site, group, count, _, _, hk, _, hpart, hkl, hkj, _⟩ :=
    hresult
  by_cases hlane : laneOf L load.1 = 0
  · have ht : store.1 = load.1 := Tmem.Pair.sameWarp_leader_eq hwarp hleader hlane
    rw [ht] at hkl
    have hind := hkl.unique hkj
    have hne : store ≠ load := by
      rintro rfl
      obtain ⟨_, hwrite⟩ := hw
      rw [hget] at hwrite
      cases hwrite
    have hlt : store.2 < load.2 := by
      have hidx : store.2 ≠ load.2 := fun h => hne (Prod.ext ht h)
      omega
    exact .inl (.single (.inl (po_of_overlap (X := X) (a := { loc := dst, size := 4 })
      (b := a) (we := true) (wf := false) (.inr (.inl ⟨out, hw, rfl⟩))
      (.inl ⟨bytes, ⟨tag, hget⟩, rfl⟩) ht hlt ⟨l, hbyte, hrdByte⟩)))
  · have hnode := allocResult_witnessed L X (load.1, j) hpart hlane
    have hp := po_of_source_not_access (X := X) (e := (load.1, j)) (f := load)
      rfl hj (len_of_get hget)
      (show (X.get (load.1, j)).bind Event.acc = none by rw [hpart]; rfl)
    have hguard : GuardSource K X (load.1, j) := .inr ⟨_, false, hpart, rfl⟩
    have hn : ∀ m tx count sc, ¬ X.Arrive (load.1, j) m tx count true sc := by
      rintro m tx count sc ⟨_, h⟩
      rw [hpart] at h
      cases h
    exact .inr ⟨store, (load.1, j), .inl rfl,
      .single (DepStep.of_witness L (Witness.of_need L hnode hfill.present hfill)),
      hguard, hn, .single (.inl hp)⟩

private theorem IssuePath.of_model (hv : EffectValidity L X) (hg : SyncGuarded L K X)
    {l : Loc} {e f : Ref} (h : modelCausality L X l e f) :
    Relation.TransGen (IssuePath L K X) e f := by
  cases e with
  | thread e =>
    cases f with
    | thread f =>
      exact .single (h.elim Or.inl IssuePath.of_allocResult)
    | async i p =>
      rcases h.2 with ⟨fence, sp, sc, hf, hl, hc, hs, ha, hb⟩ | ⟨_, hb⟩
      · exact .single (.inl (ha.trans hb))
      · exact .single (.inl hb)
  | async i p =>
    cases f with
    | thread f =>
      obtain ⟨hc, w, hf, hcb⟩ := h
      exact .single (of_completion hv hg (.inl hf) (observedCompletionBefore_baseCausality hcb))
    | async j q =>
      have edge {a b : EvId × Part} (h : AsyncBefore L X l a b) :
          IssuePath L K X (.async a.1 a.2) (.async b.1 b.2) := by
        rcases h.2.2 with ⟨w, hf, hb⟩ | ⟨w, hf, hp⟩
        · exact of_completion hv hg (.inl hf) hb
        · exact of_completion hv hg (.inr hf) (.single (.inl hp))
      have chain {a b : EvId × Part} (h : AsyncChain L X l a b) :
          Relation.TransGen (IssuePath L K X) (.async a.1 a.2) (.async b.1 b.2) := by
        induction h with
        | direct h => exact .single (edge h)
        | tail _ _ h ih => exact ih.tail (edge h)
      exact chain h.2

private theorem IssuePath.of_byte (hv : EffectValidity L X) (hg : SyncGuarded L K X)
    {l : Loc} {e f : Ref} (h : ByteCausality L X l e f) :
    Relation.TransGen (IssuePath L K X) e f := by
  induction h with
  | direct h => exact of_model hv hg h
  | commitOperand _ _ _ _ _ hobs hnext _ ih =>
    obtain ⟨sc, observed, _⟩ := hobs
    obtain ⟨n, hn, path, guard, hna⟩ := asyncObserved_enables hv hg observed
    exact ih.tail (.inr ⟨n, _, hn, path, guard, hna, .single (.inl hnext)⟩)

/-- Combine a path's prefixes, synchronization guards, and final base-causality suffix. -/
private theorem IssuePath.decompose (hv : EffectValidity L X) (hg : SyncGuarded L K X)
    (hok : GuardOk L X) {e f : Ref} (h : Relation.TransGen (IssuePath L K X) e f) :
    baseCausality L X e.issuer f.issuer ∨ ∃ i n first last,
      (i = e.issuer ∨ baseCausality L X e.issuer i) ∧ (n = i ∨ po X i n) ∧
      Relation.TransGen (DepStep L K X) (.thread n, false) (.thread first, true) ∧
      Relation.ReflTransGen (DepStep L K X) (.thread first, true) (.thread last, true) ∧
      GuardSource K X last ∧ (∀ m tx count sc, ¬ X.Arrive last m tx count true sc) ∧
      baseCausality L X last f.issuer := by
  induction h with
  | single h =>
    rcases h with hb | ⟨n, w, hn, hp, hw, hna, hb⟩
    · exact .inl hb
    · exact .inr ⟨e.issuer, n, w, w, .inl rfl, hn, hp, .refl, hw, hna, hb⟩
  | @tail mid dst _ hnext ih =>
    rcases ih with hb | ⟨i, n, first, last, hi, hn, hp, path, hw, hna, hb⟩ <;>
      rcases hnext with hb' | ⟨n', w', hn', hp', hw', hna', hb'⟩
    · exact .inl (hb.trans hb')
    · exact .inr ⟨mid.issuer, n', w', w', .inr hb, hn', hp', .refl, hw', hna', hb'⟩
    · exact .inr ⟨i, n, first, last, hi, hn, hp, path, hw, hna, hb.trans hb'⟩
    · have between := reach_notifier hg hv.tma.2.2.1 hok hw hna hb hn'
      exact .inr ⟨i, n, first, w', hi, hn, hp, path.trans (between.trans hp').to_reflTransGen,
        hw', hna', hb'⟩

/-- Byte causality has no cycle in a guarded execution. Its commit operand and allocator edges
contribute dependencies through their respective synchronization guards. -/
theorem ByteCausality.acyclic (hv : EffectValidity L X) (hc : ObjectCoherent L X)
    (he : DepStepAcyclic L K X) (hg : SyncGuarded L K X) (hok : GuardOk L X)
    (l : Loc) (n : Ref) : ¬ Relation.TransGen (ByteCausality L X l) n n := by
  intro h
  have path {e f : Ref} (h : Relation.TransGen (ByteCausality L X l) e f) :
      Relation.TransGen (IssuePath L K X) e f := by
    induction h with
    | single h => exact IssuePath.of_byte hv hg h
    | tail _ h ih => exact ih.trans (IssuePath.of_byte hv hg h)
  rcases IssuePath.decompose hv hg hok (path h) with hb |
    ⟨i, start, first, last, hi, hn, hp, reaches, hguard, hna, hb⟩
  · exact baseCausality_irrefl hc.cause hb
  · have back : baseCausality L X last i := hi.elim (fun h => h.symm ▸ hb) hb.trans
    have between := reach_notifier hg hv.tma.2.2.1 hok hguard hna back hn
    exact he _ ((between.trans hp).trans_right reaches)

end PTX
