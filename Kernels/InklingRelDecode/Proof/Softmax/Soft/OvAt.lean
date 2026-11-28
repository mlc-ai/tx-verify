-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Ind
import Kernels.InklingRelDecode.Proof.Softmax.Data.CodeS
import Lemmas.Flow.TcLdKind
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The accumulator words of the value state

On the rescale path (from the wait of the accumulator load to the wait of the rescale store) the
value state's `ov` is what the accumulator load of the round returned. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {Q : Params} {L : Launch} {g : Nat} {ent : Control.Entry}

/-- The sites of the rescale path after the accumulator load. -/
def ovSite : Site → Bool
  | .waitLdO | .bar24 | .stO | .waitStO => true
  | _ => false

/-- **The accumulator words**: on the rescale path `ov` is the words of the round's load. -/
structure OvOk (X : Execution) (g k : Nat) (y : Data.D) : Prop where
  ev : ovSite y.c.site = true → ∃ k' a sh, k' < k ∧
    X.get (g, k') = some ⟨2260, .tc (.ld a y.v.ov sh)⟩ ∧
    pollRound 1257 ((X.tr g).take k') = y.c.i + 1
  len : ovSite y.c.site = true → y.v.ov.length = 64

theorem ovSite_loop (e : Control.Entry) (t i : Nat) : ovSite (loopSite e t i) = false := by
  unfold loopSite
  split <;> first | rfl | (split <;> rfl)

theorem rec_ov {d : Data.D} {e : Event} {s : Site} (h : d.c.site ≠ .ldO) :
    (record L d e s).ov = d.v.ov := by
  obtain ⟨⟨s0, i, hh⟩, v⟩ := d
  cases s0 <;> try (exact absurd rfl h)
  all_goals (unfold record; dsimp only; repeat' split)
  all_goals first | rfl | simp_all

theorem next_ov {d dn : Control.D} {ev : Event} {g : Nat}
    (step : Control.next ent L g d ev = some (some dn)) (h : ovSite dn.site = true) :
    (d.site = .ldO ∨ ovSite d.site = true) ∧ dn.i = d.i := by
  obtain ⟨s, i, v⟩ := d
  cases s <;> simp only [Control.next, advance] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first
    | (exfalso; rw [ovSite_loop] at h; exact Bool.false_ne_true h)
    | simp_all [ovSite]

/-- **The event of the accumulator load**: a load of 64 words at pc 2260. -/
theorem fired_ldO {old : Data.D} {e : Event} (hf : Fired ent L g old e)
    (hs : old.c.site = .ldO) (hu : ∀ f, e.kind ≠ .ub f) :
    ∃ a vals sh, e = ⟨2260, .tc (.ld a vals sh)⟩ ∧ vals.length = 64 := by
  obtain ⟨t, ins, o, ht, hc, fire⟩ := hf
  have ht := atS_code ht
  have pc : old.c.site.pc = 2260 := by rw [hs]; rfl
  change kernel.code[old.c.site.pc]? = some ins at hc
  change Fires old.c.site.pc (eventTmpl Assumptions.all L g t ins.op) e o at fire
  rw [pc] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemLoad_1)
  have hw : Assumptions.all.any (·.tcLdWait t.pc) = false := by
    rw [ht.1.trans pc]; decide +kernel
  obtain ⟨a, vals, hl, rfl⟩ := fires_tcLd_kind (fun s h => by cases h) fire hw hu
  exact ⟨a, vals, _, rfl, by rw [hl]; rfl⟩

theorem ov_step {X : Execution} {k : Nat} {old y : Data.D} {e : Event}
    (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (fd : Fired ent L g old e)
    (hn : succ ent L g old e = some (some y)) (led : Led X g k old) (J : OvOk X g k old) :
    OvOk X g (k + 1) y := by
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  have key : ∀ hs : ovSite c'.site = true, (∃ k' a sh, k' < k + 1 ∧
      X.get (g, k') = some ⟨2260, .tc (.ld a (record L old e c'.site).ov sh)⟩ ∧
      pollRound 1257 ((X.tr g).take k') = c'.i + 1) ∧ (record L old e c'.site).ov.length = 64 := by
    intro hs
    obtain ⟨hold, hi⟩ := next_ov hnc hs
    rcases hold with hl | hsc
    · obtain ⟨a, vals, sh, rfl, hl64⟩ := fired_ldO fd hl hu
      have rs : (record L old ⟨2260, .tc (.ld a vals sh)⟩ c'.site).ov = vals := by
        simp [record, hl]
      refine ⟨⟨k, a, sh, by omega, by rw [rs]; exact he, ?_⟩, by rw [rs]; exact hl64⟩
      have := led
      simp only [Led, hl, Site.afterS, Bool.toNat_true] at this
      rw [this, hi]
    · have hne : old.c.site ≠ .ldO := fun h => by simp [h, ovSite] at hsc
      rw [rec_ov hne]
      obtain ⟨k', a, sh, hk', hg, hp⟩ := J.ev hsc
      exact ⟨⟨k', a, sh, by omega, hg, by rw [hp, hi]⟩, J.len hsc⟩
  exact ⟨fun hs => key hs |>.1, fun hs => key hs |>.2⟩

/-- **The accumulator words of the value state along the trace.** -/
theorem soft_ov {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, Frame.stateAt (threadD Q L) X g k = some (some s) →
      Frame.NoUbBefore X g k → ∀ w ent y n, s = softDState w ent y n → ent.Ok →
        OvOk X g k y := by
  intro k hk s hs nub w ent y n hsd ok
  exact (soft_ind hp hX (fun _ k y => OvOk X g k y)
    (fun _ _ _ _ => ⟨fun h => by simp [ovSite] at h, fun h => by simp [ovSite] at h⟩)
    (fun k ent old y e ok he hu fd pc hn led inv J => ov_step he hu fd hn led J)
    k hk s hs nub).2 w ent y n hsd ok |>.2.2

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
