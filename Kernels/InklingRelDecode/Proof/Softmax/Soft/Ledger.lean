-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Induct
import Kernels.InklingRelDecode.Proof.Softmax.PollStep
public import Kernels.InklingRelDecode.Proof.Softmax.Cnt

/-! # The round counter of the value machine and the polls of the trace

At a state of the value machine the successful polls of `s_ready` before it are the state's
round counter plus one once the poll of the round is past. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {L : Launch} {g : Nat}

/-- The polls of pc 1257 before position `k` match the counter of a state. -/
@[expose] public def Led (X : Execution) (g k : Nat) (y : Data.D) : Prop :=
  pollRound 1257 ((X.tr g).take k) = y.c.i + y.c.site.afterS.toNat

private theorem site_1257 (s : Site) (h : s.pc = 1257) : s = .waitS := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

theorem Site.pc_ne_1257 {s : Site} (h : s ≠ .waitS) : s.pc ≠ 1257 := fun e => h (site_1257 s e)

private theorem next_led {e : Entry} {d dn : Control.D} {ev : Event}
    (step : Control.next e L g d ev = some (some dn)) :
    (d.site ≠ .waitS ∧ dn.i = d.i ∧ dn.site.afterS = d.site.afterS) ∨
    (d.site ≠ .waitS ∧ (d.site = .bar21 ∨ d.site = .arrive) ∧ dn.i = d.i + 1 ∧
      dn.site.afterS = false ∧ d.site.afterS = true) ∨
    (d.site = .waitS ∧ ((dn.site = .shfl4 ∧ dn.i = d.i ∧ ∃ a b c s, ev.kind = .wait a b true c s) ∨
      (dn.site = .waitS ∧ dn.i = d.i ∧ ∃ a b c s, ev.kind = .wait a b false c s))) := by
  obtain ⟨s, i, v⟩ := d
  have loop : ∀ t i, (loopSite e t i).afterS = false := by
    intro t i
    unfold loopSite
    split <;> first | rfl | (split <;> rfl)
  by_cases hw : s = .waitS
  · subst hw
    simp only [Control.next] at step
    split at step
    · rename_i hk
      split at step
      · rename_i hok
        cases step
        subst hok
        exact .inr (.inr ⟨rfl, .inl ⟨by simp, rfl, _, _, _, _, hk⟩⟩)
      · rename_i hok
        cases step
        simp only [Bool.not_eq_true] at hok
        subst hok
        exact .inr (.inr ⟨rfl, .inr ⟨rfl, rfl, _, _, _, _, hk⟩⟩)
    · cases step
  cases s <;> simp only [Control.next, advance] at step
  all_goals try exact absurd rfl hw
  all_goals repeat' split at step
  all_goals cases step
  all_goals dsimp only
  all_goals first
    | exact .inl ⟨hw, rfl, rfl⟩
    | exact .inl ⟨hw, rfl, by rw [loop]; rfl⟩
    | exact .inr (.inl ⟨hw, by simp, rfl, by rw [loop], rfl⟩)

private theorem ok_poll {ev : Event} {a b c s} (hpc : ev.pc = 1257)
    (hk : ev.kind = .wait a b true c s) :
    okPollAt 1257 ev = true := by
  obtain ⟨p, kk⟩ := ev
  change p = 1257 at hpc
  change kk = _ at hk
  subst hk hpc
  simp [okPollAt]

private theorem no_poll {ev : Event} {a b c s} (hk : ev.kind = .wait a b false c s) :
    okPollAt 1257 ev = false := by
  obtain ⟨p, kk⟩ := ev
  change kk = _ at hk
  subst hk
  simp [okPollAt]

/-- **The counter follows the polls**: one step keeps `Led`. -/
public theorem led_step {X : Execution} {k : Nat} {ent : Entry} {old y : Data.D} {e : Event}
    (he : X.get (g, k) = some e) (pc : e.pc = old.c.site.pc)
    (hn : succ ent L g old e = some (some y)) (h : Led X g k old) : Led X g (k + 1) y := by
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  unfold Led at h ⊢
  dsimp only at h ⊢
  rcases next_led hnc with ⟨hw, hi, hs⟩ | ⟨hw, -, hi, hs, ho⟩ |
    ⟨hw, ⟨s4, hi, a, b, c, s, hk⟩ | ⟨s4, hi, a, b, c, s, hk⟩⟩
  · rw [poll_same he (by rw [pc]; exact Site.pc_ne_1257 hw), hi, hs]
    exact h
  · rw [poll_same he (by rw [pc]; exact Site.pc_ne_1257 hw), hi, hs]
    rw [ho] at h
    simpa using h
  · have p1257 : e.pc = 1257 := by rw [pc, hw]; rfl
    rw [poll_step he, ok_poll p1257 hk, hi, s4]
    rw [hw] at h
    simpa [Site.afterS] using h
  · have p1257 : e.pc = 1257 := by rw [pc, hw]; rfl
    rw [poll_step he, no_poll hk, hi, s4]
    rw [hw] at h
    simpa [Site.afterS] using h

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
