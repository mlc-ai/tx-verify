-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.OrderBaseCausality
public import Core.Assembly.Execution
public import Lemmas.Order.WaitOrderEnables
public import Lemmas.Async.AsyncMBarrier
public import Lemmas.MBarrier.BarrierOrdinal
public import Mathlib.Logic.Relation

@[expose] public section

/-! # Events that are not memory accesses

These are proofs from the Core rules. Barrier, acquire-wait and asynchronous observation
events are not memory accesses (`CtaBarK.not_access`, `Execution.AcquireWait.not_access`,
`AsyncCopy.WaitObserves.not_access`, `AsyncCopy.AsyncObserved.not_access`,
`Execution.get_not_access`); without CTA barriers causality is program order and
synchronization (`baseCausality_of_noBar`). -/

namespace PTX
noncomputable section

section
variable {L : Launch} {X : Execution}

theorem SameAccess.source_some {e f : EvId} (h : SameAccess X e f) (hf : f.1 = e.1)
    (hle : e.2 ≤ f.2) : ((X.get e).bind Event.acc).isSome := by
  have hff : (e.1, e.2 + (f.2 - e.2)) = f := Prod.ext hf.symm (by simp only; omega)
  have := h.2 (f.2 - e.2) le_rfl
  rw [hff] at this
  have h1 := h.1
  rw [this] at h1
  cases hh : (X.get e).bind Event.acc <;> simp_all

theorem SameAccess.mono {e f f' : EvId} (h : SameAccess X e f) (hf : f.1 = e.1) (hs : f'.1 = e.1)
    (h1 : e.2 ≤ f'.2) (h2 : f'.2 ≤ f.2) : SameAccess X e f' := by
  have hf' : (e.1, e.2 + (f'.2 - e.2)) = f' := Prod.ext hs.symm (by simp only; omega)
  have hsome := h.source_some hf (h1.trans h2)
  refine ⟨?_, fun k hk => h.2 k (by omega)⟩
  have := h.2 (f'.2 - e.2) (by omega)
  rw [hf'] at this
  rw [this]
  cases hh : (X.get e).bind Event.acc <;> simp_all

theorem po_trans {a b c : EvId} (h1 : po X a b) (h2 : po X b c) : po X a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h2.2.2.1, fun h =>
    h1.2.2.2 (h.mono (h1.1.trans h2.1).symm h1.1.symm h1.2.1.le (h2.2.1.le))⟩

theorem Execution.BarK.lt {e : EvId} {k : Nat} (h : X.BarK e k) :
    e.2 < (X.tr e.1).length := by
  obtain ⟨⟨id, pc, hh⟩, _⟩ := h
  exact len_of_get hh

theorem Execution.get_not_access {e : EvId} {ev : Event} {k : Kind} (hev : X.get e = some ev)
    (h : ev.kind = k) (h1 : ∀ a bs, k ≠ .rd a bs) (h2 : ∀ a bs, k ≠ .nc a bs)
    (h3 : ∀ a bs, k ≠ .wr a bs) (h4 : ∀ a old new, k ≠ .rmw a old new) :
    (X.get e).bind Event.acc = none := by
  obtain ⟨pc, kind⟩ := ev
  simp only at h
  subst h
  cases kind <;> simp_all [Event.acc]

theorem Execution.AcquireWait.not_access {w : EvId} {m : Loc} (h : X.AcquireWait w m) :
    (X.get w).bind Event.acc = none := by
  obtain ⟨pc, parity, scope, hp⟩ := h
  simp [hp, Event.acc]

theorem AsyncCopy.WaitObserves.not_access {x : AsyncCopy.Ref} {w : EvId} {m : Loc} {acq : Bool}
    {ws : MbarScope} (h : AsyncCopy.WaitObserves X x w m acq ws) :
    (X.get w).bind Event.acc = none := by
  obtain ⟨⟨pc, parity, hp⟩, -⟩ := h
  simp [hp, Event.acc]

theorem AsyncCopy.AsyncObserved.not_access {i w : EvId} {p : AsyncCopy.Part} {acq : Bool}
    {ws : MbarScope} (h : AsyncCopy.AsyncObserved X i p w acq ws) :
    (X.get w).bind Event.acc = none := by
  obtain ⟨_, _, _, hw⟩ := h
  exact hw.not_access

theorem CtaBarK.not_access {e : EvId} {k : Nat} (h : CtaBarK L X e k) :
    (X.get e).bind Event.acc = none := by
  obtain ⟨count, pc, hp⟩ := h.2.1
  simp [Execution.IsBarrier] at hp
  simp [hp, Event.acc]

theorem CtaBarArrivalK.not_access {e : EvId} {k : Nat} (h : CtaBarArrivalK L X e k) :
    (X.get e).bind Event.acc = none := by
  obtain ⟨count, pc, _, hp⟩ := h.2.1
  simp [hp, Event.acc]

/-- Without collective synchronization, successful waits or a fence synchronization, causality
is program order. -/
theorem baseCausality_of_noBar (hnb : ∀ e k, ¬ CtaBarK L X e k) (hnw : ∀ w m, ¬ X.AcquireWait w m)
    (hnc : ∀ e f, ¬ ClusterSync L X e f)
    (hnwb : ∀ e f, ¬ WarpBarSync L X e f) (hnac : ∀ e f, ¬ synchronizesWith L X e f)
    (hnf : ∀ e f, ¬ FenceSync L X e f) {e f : EvId}
    (h : baseCausality L X e f) : po X e f := by
  induction h with
  | single h =>
    rcases h with h | ⟨_, k, i, j, -, hi, _⟩ | ⟨x, w, m, _, _, _, hw, _⟩ | hc | hw | ha | hf
    · exact h
    · exact absurd hi (hnb _ _)
    · exact absurd hw.acquireWait (hnw _ _)
    · exact absurd hc (hnc _ _)
    · exact absurd hw (hnwb _ _)
    · exact absurd ha (hnac _ _)
    · exact absurd hf (hnf _ _)
  | tail _ h ih =>
    rcases h with ⟨h1, h2, h3, h4⟩ | ⟨_, k, i, j, -, hi, _⟩ | ⟨x, w, m, _, _, _, hw, _⟩
        | hc | hw | ha | hf
    · obtain ⟨i1, i2, i3, i4⟩ := ih
      exact po_trans ⟨i1, i2, i3, i4⟩ ⟨h1, h2, h3, h4⟩
    · exact absurd hi (hnb _ _)
    · exact absurd hw.acquireWait (hnw _ _)
    · exact absurd hc (hnc _ _)
    · exact absurd hw (hnwb _ _)
    · exact absurd ha (hnac _ _)
    · exact absurd hf (hnf _ _)

end

end

end PTX
