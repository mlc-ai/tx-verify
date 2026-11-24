-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.OrderBaseCausality
public import Core.Assembly.Execution
public import Lemmas.Order.WaitOrderEnables
public import Lemmas.Async.AsyncMBarrier
public import Lemmas.MBarrier.BarrierOrdinal
public import Mathlib.Logic.Relation

@[expose] public section

/-! # Causality as waits and program order

These are proofs from the Core rules. Causality between present events is a `Waits` path
(`baseCausality_waits`, `waits_po`, `waits_self`, `MSync.waits`), and program order transfers
between executions that agree on a thread's events (`po_congr`, `SameAccess.congr`,
`po_of_source_not_access`). -/

namespace PTX
noncomputable section

section
variable {L : Launch} {X : Execution}

/-- Agreeing on the events from `a` to `b` gives the same vector-access chain. -/
theorem SameAccess.congr {Y : Execution} {a b : EvId} (hs : b.1 = a.1) (hab : a.2 ≤ b.2)
    (h : ∀ x : EvId, x.1 = a.1 → a.2 ≤ x.2 → x.2 ≤ b.2 → Y.get x = X.get x) :
    SameAccess Y a b ↔ SameAccess X a b := by
  unfold SameAccess
  rw [h a rfl le_rfl hab]
  refine and_congr ?_ (forall_congr' fun k => imp_congr_right fun hk => ?_)
  · rw [h b hs hab le_rfl]
  · rw [h (a.1, a.2 + k) rfl (by simp) (by simp only; omega)]

/-- Executions that agree on the old events have the same program order into an old event. -/
theorem po_congr {Y : Execution} {a b : EvId} (hb : b.2 < (X.tr b.1).length)
    (hY : b.2 < (Y.tr b.1).length)
    (h : ∀ x : EvId, x.2 < (X.tr x.1).length → Y.get x = X.get x) : po Y a b ↔ po X a b := by
  unfold po
  by_cases hs : a.1 = b.1
  · by_cases hlt : a.2 < b.2
    · have hsame := SameAccess.congr (X := X) (Y := Y) hs.symm hlt.le
        (fun x h1 _ hx => h x (by rw [h1, hs]; omega))
      simp only [hs, hlt, true_and, hsame, hb, hY]
    · simp [hlt]
  · simp [hs]

/-- Program order out of an event that is no memory operation. -/
theorem po_of_source_not_access {e f : EvId} (hs : e.1 = f.1) (hlt : e.2 < f.2)
    (hf : f.2 < (X.tr f.1).length) (h : (X.get e).bind Event.acc = none) : po X e f :=
  ⟨hs, hlt, hf, fun hh => by
    have h2 := hh.2 (f.2 - e.2) le_rfl
    have hf' : (e.1, e.2 + (f.2 - e.2)) = f := Prod.ext hs (by simp only; omega)
    rw [hf', h] at h2
    have := hh.1
    rw [h2] at this
    cases this⟩

theorem waits_self {e : EvId} (he : e.2 < (X.tr e.1).length) :
    Waits L X (.thread e, false) (.thread e, true) :=
  .inl ⟨rfl, rfl, rfl, (X.tr e.1)[e.2], List.getElem?_eq_getElem he⟩

/-- The return of an earlier instruction precedes issue of a later one. This says
nothing about completion of their independent async memory effects. -/
theorem waits_po {g i j : Nat} (hij : i < j) (hj : j < (X.tr g).length) :
    Relation.TransGen (Waits L X) (.thread (g, i), true) (.thread (g, j), false) := by
  induction j, hij using Nat.le_induction with
  | base => exact .single (.inr (.inl ⟨rfl, rfl, (g, i), (g, i + 1), rfl, rfl, rfl, rfl, hj⟩))
  | succ j hij ih =>
    have h1 : j < (X.tr g).length := by omega
    have e2 : Waits L X (.thread (g, j), true) (.thread (g, j + 1), false) :=
      .inr (.inl ⟨rfl, rfl, (g, j), (g, j + 1), rfl, rfl, rfl, rfl, hj⟩)
    exact ((ih h1).tail (waits_self h1)).tail e2

theorem MSync.waits {e f : EvId} (h : MSync L X e f) :
    Relation.TransGen (Waits L X) (.thread e, true) (.thread f, false) := by
  obtain ⟨⟨gx, ix⟩, ⟨gw, iw⟩, m, rs, ws, hr, ⟨_, hphase⟩, _, hwf, hwlt, hf, hxe, hle⟩ := h
  cases e with | mk ge ie =>
    cases f with | mk gf jf =>
      simp only at hwf hwlt hf hxe hle hr
      subst gx gw
      have hx := hr.lt
      obtain ⟨i, j, r, w, phase, hi, hir, _, hj, hjw, _, _, hij, _⟩ := hphase
      have hmw : Waits L X (.thread (ge, ix), true) (.thread (gf, iw), true) :=
        .inr (.inr (.inr (.inr (.inr (.inr (.inl
          ⟨rfl, rfl, m, i, j, r, w, hi, hir, hj, hjw, hij⟩))))))
      have hw2 := waits_po (L := L) hwlt hf
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · subst heq; exact (Relation.TransGen.single hmw).trans hw2
      · exact (((waits_po hlt hx).tail (waits_self hx)).tail hmw).trans hw2

theorem baseCausality_waits {e f : EvId} (h : baseCausality L X e f) :
    Relation.TransGen (Waits L X) (.thread e, true) (.thread f, false) := by
  have step : ∀ a b, (po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
      WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b) →
      Relation.TransGen (Waits L X) (.thread a, true) (.thread b, false) := by
    rintro ⟨ga, ia⟩ ⟨gb, ib⟩
      (⟨h1, h2, h3, -⟩ | ⟨hc, k, i, j, hi, hj, h1, h2, h3⟩ | hm | hc | hw | ha | hf)
    · simp only at h1 h2 h3; subst h1; exact waits_po h2 h3
    · simp only at hi hj h1 h2 h3
      have hbar : Waits L X (.thread (ga, i), false) (.thread (gb, j), true) :=
        .inr (.inr (.inl ⟨(ga, i), (gb, j), rfl, rfl,
          hi.present, hj.present, .inr (.inl ⟨rfl, rfl, hc, k, hi, hj⟩)⟩))
      exact ((waits_po h1 hi.lt).tail hbar).trans (waits_po h2 h3)
    · exact hm.waits
    · obtain ⟨_, i, j, ⟨phase, ha, hw⟩, hi, hei, hjf, hf⟩ := hc
      simp only at hi hei hjf hf ha hw
      have hj : j < (X.tr gb).length := by omega
      have hevent : ∃ ev, X.get (ga, i) = some ev :=
        ⟨(X.tr ga)[i], List.getElem?_eq_getElem hi⟩
      have fevent : ∃ ev, X.get (gb, j) = some ev :=
        ⟨(X.tr gb)[j], List.getElem?_eq_getElem hj⟩
      have hwc : ClusterWaits L X (ga, i) (gb, j) false true :=
        ⟨hevent, fevent, .inr (.inr (.inl ⟨rfl, rfl, phase,
          L.clusterOfCta (ga / L.block), ha, hw⟩))⟩
      have hbar : Waits L X (.thread (ga, i), false) (.thread (gb, j), true) :=
        .inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inl ⟨(ga, i), (gb, j), rfl, rfl, hwc⟩)))))))
      exact ((waits_po hei hi).tail hbar).trans (waits_po hjf hf)
    · obtain ⟨i, j, hedge, hei, hjf, hf⟩ := hw
      have hi : i < (X.tr ga).length := by
        obtain ⟨_, mask, inst, ⟨pc, hi⟩, _⟩ := hedge
        exact len_of_get hi
      have hwbar : Waits L X (.thread (ga, i), false) (.thread (gb, j), true) :=
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨rfl, rfl, (ga, i), (gb, j), rfl, rfl, hedge⟩)))))))))
      exact ((waits_po hei hi).tail hwbar).trans (waits_po hjf hf)
    · exact .single (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (
      .inr ((Or.inl ⟨rfl, rfl, (ga, ia), (gb, ib), rfl, rfl, ha⟩))))))))))))
    · exact .single (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (
      .inr ((Or.inl ⟨rfl, rfl, (ga, ia), (gb, ib), rfl, rfl, hf⟩)))))))))))))))
  induction h with
  | single h => exact step _ _ h
  | @tail b c hab hbc ih =>
    exact (ih.tail (waits_self (baseCausality_events hab).2)).trans (step _ _ hbc)

end

end

end PTX
