-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBarEv

@[expose] public section

/-! # The named barrier of a state's event

The barrier of a state's site (`barIdOf`): barrier 2 at the start and end barriers of the
softmax, correction and MMA warps, the warp's statistics barrier at a softmax `gen` (`w + 3`) and
at a correction stage's `sync` (`w - 5 + 4 st`). The event fired from a followed state is on
barrier `id` exactly when the site's barrier is `id` (`fired_barId`): the site events of the
softmax and correction roles name their barrier (`Softmax.Ev`, `Correction.Ev`), the MMA warp's
barrier events are on barrier 2 (`mma_event_class`), and no other site is a barrier. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The named barrier of a state's site. -/
def barIdOf (L : Launch) (g : Nat) : ThreadD → Option Nat
  | .inr (.softmax s) => match s.site with
    | .bar0 | .barEnd => some 2
    | .gen _ => some (warpOf L g + 3)
    | _ => none
  | .inr (.corr c) => match c.site with
    | .bar0 | .barEnd => some 2
    | .sync st _ => some (warpOf L g - 5 + 4 * st.val)
    | _ => none
  | .inr (.mma m) => match m.site with
    | .bar0 | .bar1 => some 2
    | _ => none
  | _ => none

/-- A state whose site has a barrier is at a barrier site. -/
theorem barIdOf_kind {g : Nat} {d : ThreadD} {id : Nat} (h : barIdOf L g d = some id) :
    nextKind d = .bar := by
  rcases d with p | (s | l | m | s | s | c)
  all_goals simp only [barIdOf, reduceCtorEq] at h
  · revert h; split <;> simp [nextKind, mmaKind, *]
  · revert h; split <;> simp [nextKind, softmaxKind, *]
  · revert h; split <;> simp [nextKind, corrKind, *]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- An event at a followed state is not undefined behaviour. -/
theorem not_ub {g k : Nat} {d : ThreadD} {e : Event} (hg : g < L.threads)
    (hσ : St L X g k = some (some d)) (he : X.get (g, k) = some e) :
    ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  rintro pc f rfl
  rcases TcFacts_ub_stop hpre hX ht hok hg he with h | h <;> rw [hσ] at h <;> cases h

/-- **The event fired from a followed state is on the site's barrier.** -/
theorem fired_barId {g k id : Nat} {d : ThreadD} {e : Event} (hg : g < L.threads)
    (hσ : St L X g k = some (some d)) (he : X.get (g, k) = some e) :
    Execution.isBarId id e = (barIdOf L g d == some id) := by
  have hb := (fired_kind hpre hX hok hg hσ he).2.2.2
  have hbar : Execution.isBarId id e = true → isBar e = true := by
    intro h
    obtain ⟨c, m, hk⟩ := isBarId_of_kind h
    obtain ⟨pc, k'⟩ := e; simp only at hk; subst hk; rfl
  by_cases hk : nextKind d = .bar
  · have hk' : Frame.stateAt (code L) X g k = some (some d) := hσ
    have hw := (state_facts hpre hX ht hok hg
      (List.getElem?_eq_some_iff.mp he).1.le hσ).2.2
    rcases role_cases hw with ⟨p, rfl⟩ | ⟨-, s, rfl⟩ | ⟨-, l, rfl⟩ | ⟨hw', m, rfl⟩ |
        ⟨-, s, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', hw'', c, rfl⟩
    · obtain ⟨s⟩ := p; cases s <;> simp [nextKind, prologueKind] at hk
    · obtain ⟨s⟩ := s; cases s <;> simp [nextKind, idleKind] at hk
    · cases hs : l.site <;> simp [nextKind, loaderKind, hs] at hk
    · -- the MMA warp's barrier events are on barrier 2
      have hc := (mma_event_class hpre hX ht hw' he).1
      have hb' : isBar e = true := by rw [hb]; simp [hk]
      have h2 : Execution.isBarId 2 e = true := by
        rw [← hc]; obtain ⟨pc, k'⟩ := e
        cases k' <;> simp_all [isBar, Execution.isBar]
      obtain ⟨c, md, hk2⟩ := isBarId_of_kind h2
      have hid : barIdOf L g (.inr (.mma m)) = some 2 := by
        cases hs : m.site <;> simp_all [nextKind, mmaKind, barIdOf]
      rw [hid]
      obtain ⟨pc, k'⟩ := e
      simp only at hk2
      subst hk2
      by_cases h : id = 2
      · subst h; simp [Execution.isBarId]
      · simp [Execution.isBarId]
    · cases hs : s.site <;> simp [nextKind, storeKind, hs] at hk
    · rcases soft_origin hpre hX ht he hw' (not_ub hpre hX ht hok hg hσ he) with
        ⟨p, hp, -⟩ | ⟨s', t, ins, o, hs', -, -, -, -, -, hev⟩
      · rw [hk'] at hp; cases hp
      rw [hk'] at hs'
      cases hs'
      have hid3 := soft_statsId L g
      obtain ⟨pc, k'⟩ := e
      cases hs : s.site <;> simp only [nextKind, softmaxKind, hs, reduceCtorEq] at hk <;>
        simp only [Softmax.Ev, hs] at hev <;> subst hev <;>
        simp only [barIdOf, hs, Execution.isBarId, hid3] <;>
        by_cases h : id = 2 <;> simp [h]
    · rcases corr_origin hpre hX ht he hw' hw'' (not_ub hpre hX ht hok hg hσ he) with
        ⟨p, hp, -⟩ | ⟨c', t, ins, o, hs', -, -, -, -, -, hev⟩
      · rw [hk'] at hp; cases hp
      rw [hk'] at hs'
      cases hs'
      have hk0 := corr_kOf (L := L) hw' hw''
      have hne : e.kind ≠ .exit := by
        intro hx
        have : isBar e = false := by obtain ⟨pc, k'⟩ := e; simp only at hx; subst hx; rfl
        rw [hb] at this; simp [hk] at this
      have hev := (hev hne).2
      obtain ⟨pc, k'⟩ := e
      cases hs : c.site <;> simp only [nextKind, corrKind, hs, reduceCtorEq] at hk <;>
        simp only [hs] at hev <;> subst hev <;>
        simp only [barIdOf, hs, Execution.isBarId, hk0] <;>
        by_cases h : id = 2 <;> simp [h, eq_comm] <;> omega
  · have hn : barIdOf L g d = none := by
      cases h : barIdOf L g d with
      | none => rfl
      | some x => exact absurd (barIdOf_kind h) hk
    rw [hn]
    cases h : Execution.isBarId id e
    · rfl
    · have := hbar h
      rw [hb] at this
      simp [hk] at this

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
