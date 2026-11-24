-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Order.WaitOrderEnables
public import Lemmas.Async.AsyncMBarrier
public import Lemmas.MBarrier.BarrierOrdinal
public import Mathlib.Logic.Relation

@[expose] public section

/-! # Positions, program order and causality

These are proofs from the Core rules. A present event lies within its thread's trace
(`len_of_get`, `CtaBarK.present`, `CtaBarK.lt`, `MbarRelease.lt`); causality relates
present events and is irreflexive (`baseCausality_events`, `baseCausality_irrefl`); program order on
events that are not memory accesses (`po_of_not_access`); a completion ordered before an access is
ordered by causality (`CompletionBefore.baseCausality`). -/

namespace PTX
noncomputable section

section
variable {L : Launch} {X : Execution}

theorem TraceBefore.trans {a b c : EvId} (h1 : TraceBefore X a b) (h2 : TraceBefore X b c) :
    TraceBefore X a c := ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h2.2.2⟩

theorem po.trace {a b : EvId} (h : po X a b) : TraceBefore X a b := ⟨h.1, h.2.1, h.2.2.1⟩

/-- Program order into an event that is no memory operation. -/
theorem po_of_not_access {e f : EvId} (hs : e.1 = f.1) (hlt : e.2 < f.2)
    (hf : f.2 < (X.tr f.1).length) (h : (X.get f).bind Event.acc = none) : po X e f :=
  ⟨hs, hlt, hf, fun hh => by have := hh.1; rw [h] at this; cases this⟩

theorem CtaBarK.present {e : EvId} {k : Nat} (h : CtaBarK L X e k) :
    ∃ ev, X.get e = some ev := by
  obtain ⟨count, pc, hp⟩ := h.2.1
  exact ⟨_, hp⟩

theorem CtaBarK.lt {e : EvId} {k : Nat} (h : CtaBarK L X e k) :
    e.2 < (X.tr e.1).length := by
  obtain ⟨ev, hp⟩ := h.present
  exact len_of_get hp

theorem CtaBarArrivalK.present {e : EvId} {k : Nat} (h : CtaBarArrivalK L X e k) :
    ∃ ev, X.get e = some ev := by
  obtain ⟨count, pc, _, hp⟩ := h.2.1
  exact ⟨_, hp⟩

theorem CtaBarArrivalK.lt {e : EvId} {k : Nat} (h : CtaBarArrivalK L X e k) :
    e.2 < (X.tr e.1).length := by
  obtain ⟨ev, hp⟩ := h.present
  exact len_of_get hp

theorem Execution.Writes.lt {e : EvId} {a : Acc} {bs : List Byte} (h : X.Writes e a bs) :
    e.2 < (X.tr e.1).length := by obtain ⟨pc, hp⟩ := h; exact len_of_get hp

theorem MbarRelease.lt {e : EvId} {m : Loc} {scope : MbarScope}
    (h : MbarRelease X e m scope) : e.2 < (X.tr e.1).length := by
  obtain ⟨tx, count, pc, hp⟩ := h
  exact len_of_get hp

theorem MSync.events {e f : EvId} (h : MSync L X e f) :
    e.2 < (X.tr e.1).length ∧ f.2 < (X.tr f.1).length := by
  obtain ⟨x, w, m, rs, ws, hr, _, _, _, _, hf, hx, he⟩ := h
  have hxl := hr.lt
  rw [hx] at hxl
  exact ⟨by omega, hf⟩

/-- The two events of a fence synchronization are present. -/
theorem FenceSync.events {e f : EvId} (h : FenceSync L X e f) :
    e.2 < (X.tr e.1).length ∧ f.2 < (X.tr f.1).length := by
  have hwr : ∀ w a bs, X.MemWrites (.thread w) a bs → w.2 < (X.tr w.1).length := by
    intro w a bs hw
    rcases hw with ⟨pc, hp⟩ | ⟨old, pc, hp⟩
    · exact len_of_get hp
    · exact len_of_get hp
  have hrd : ∀ r b cs, StrongRead X r b cs → r.2 < (X.tr r.1).length := by
    intro r b cs hr
    obtain ⟨⟨pc, hp⟩, -⟩ | ⟨n, ⟨pc, hp⟩, -⟩ := hr
    · exact len_of_get hp
    · exact len_of_get hp
  have hfence : ∀ e sem s, X.ThreadFence e sem s → e.2 < (X.tr e.1).length := by
    rintro e sem s ⟨pc, hp⟩
    exact len_of_get hp
  rcases h with ⟨w, r, a, b, bs, cs, se, sf, hw, -, hr, hrel, hacq, htk, -⟩ |
    ⟨⟨s, s', hs, hs', -⟩, -⟩
  · refine ⟨?_, ?_⟩
    · rcases hrel with ⟨rfl, -, -⟩ | ⟨sem, hf, -, -, -⟩
      · exact hwr _ a bs hw
      · exact hfence e sem se hf
    · rcases hacq with ⟨rfl, -, -⟩ | ⟨sem, hf, -, -, -⟩
      · exact hrd _ b cs hr
      · exact hfence f sem sf hf
  · exact ⟨hfence e .sc s hs, hfence f .sc s' hs'⟩

theorem baseCausality_events {e f : EvId} (h : baseCausality L X e f) :
    e.2 < (X.tr e.1).length ∧ f.2 < (X.tr f.1).length := by
  have step : ∀ a b, (po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
      WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b) →
      a.2 < (X.tr a.1).length ∧ b.2 < (X.tr b.1).length := by
    rintro a b (⟨h1, h2, h3, -⟩ | ⟨_, k, i, j, hi, hj, h1, h2, h3⟩ | hm | hc | hw | ha | hfs)
    · exact ⟨by rw [h1]; omega, h3⟩
    · exact ⟨by have := hi.lt; simp at this; omega, h3⟩
    · exact hm.events
    · obtain ⟨_, i, j, _, hi, hei, _, hf⟩ := hc
      exact ⟨by omega, hf⟩
    · obtain ⟨i, j, ⟨_, mask, inst, ⟨pc, hi⟩, _⟩, hei, _, hf⟩ := hw
      have hi' := len_of_get hi
      dsimp only at hi'
      exact ⟨by omega, hf⟩
    · obtain ⟨x, y, bs, cs, he, hf, _⟩ := ha
      have hx : a.2 < (X.tr a.1).length := by
        rcases he with ⟨pc, hp⟩ | ⟨old, pc, hp⟩
        · exact len_of_get hp
        · exact len_of_get hp
      have hy : b.2 < (X.tr b.1).length := by
        rcases hf with ⟨pc, hp⟩ | ⟨new, pc, hp⟩
        · exact len_of_get hp
        · exact len_of_get hp
      exact ⟨hx, hy⟩
    · exact hfs.events
  induction h with
  | single h => exact step _ _ h
  | tail _ h ih => exact ⟨ih.1, (step _ _ h).2⟩

/-- Causality has no cycle through an instruction: its return reaches its own issue. -/
theorem baseCausality_irrefl (hac : ∀ n, ¬ Relation.TransGen (stageCausality L X) n n) {e : EvId} :
    ¬ baseCausality L X e e := by
  intro h
  have hp : X.RefPresent (.thread e) := ⟨_, List.getElem?_eq_getElem (baseCausality_events h).1⟩
  have e1 : stageCausality L X (.thread e, true) (.thread e, false) :=
    Or.inr (Or.inl ⟨rfl, rfl, e, e, rfl, rfl, h⟩)
  have e2 : stageCausality L X (.thread e, false) (.thread e, true) :=
    Or.inl (Or.inl ⟨rfl, rfl, rfl, hp⟩)
  exact hac _ (.tail (.single e1) e2)

/-- The observation of a completion precedes the later generic access by causality, through
the proxy fence for an MMA's shared-memory read. -/
theorem CompletionBefore.baseCausality {l : Loc} {p : AsyncCopy.Part} {w f : EvId}
    (h : CompletionBefore L X l p w f) : _root_.PTX.baseCausality L X w f := by
  cases p with
  | mmaRead =>
    obtain ⟨fence, sp, scope, -, -, -, -, h1, h2⟩ := h
    exact h1.trans h2
  | _ => exact h

/-- Two threads of one CTA meet in every pair of scopes. -/
theorem ScopesMeet.of_sameCta {L : Launch} {us ws : MbarScope} {g h : Nat} (hc : SameCta L g h) :
    ScopesMeet L us g ws h := by
  have hcl : L.clusterOfCta (g / L.block) = L.clusterOfCta (h / L.block) := by rw [hc.2.2]
  have hc' : SameCta L h g := ⟨hc.2.1, hc.1, hc.2.2.symm⟩
  cases us <;> cases ws <;>
    exact ⟨by first | exact hc | exact ⟨hc.1, hc.2.1, hcl⟩ | exact ⟨hc.1, hc.2.1⟩,
      by first | exact hc' | exact ⟨hc.2.1, hc.1, hcl.symm⟩ | exact ⟨hc.2.1, hc.1⟩⟩

end

end

end PTX
