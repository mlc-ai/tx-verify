-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQ

@[expose] public section

/-! # Strict steps of guarded instructions under the tag invariant

`Code.advanceGQ` and `Code.ldWGQ` are `Code.advanceQ` and `Code.ldWQ` for an instruction with a
guard. A strict step is about an event of the instruction, which was emitted because its guard
held, so the proofs never read the guard; the segment after the event takes care of the skipped
case. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- **A continuing event of a possibly guarded instruction under the tag invariant**: the event
is one of an executed instruction, so the guard is not read. -/
theorem advanceGQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d dn : C.D} {op : Op}
    {gd : Option (Nat × Bool)}
    (hc : K.code[C.pc d]? = some ⟨gd, op⟩)
    (ha : ∀ {t u e}, Fires (C.pc d) (eventTmpl A L g t op) e (some u) → u = PTX.next t)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (hacc : C.acc d = [])
    (hs' : C.sub dn = 0) (hacc' : C.acc dn = []) (hi : C.inv dn)
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hq : afterWrites qt (C.pc d) [] ex = true)
    (seg : SegQ K A L g (QT qt) (C.pc d + 1) (C.facts d) (C.pc dn) (C.facts dn)) (e : Event) :
    C.StepForQ (QT qt) Wf d e := by
  intro t u ins h _ hins hQ _ hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain rfl := ha hf
  have hQ' : QT qt (PTX.next t) :=
    QT.after hQ hexT h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r tg hl => by simp at hl)
      (fun r _ => rfl) hq
  obtain ⟨t', hr, hg, hq'⟩ := landQ (At.next (at_of_atD h hs hacc)) hQ' seg hi hs' hacc'
  exact .inl ⟨dn, t', hn e, hr, hg, hq'⟩

/-- **A scalar weak load of a possibly guarded instruction under the tag invariant.** -/
theorem ldWGQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {P : Value → Prop} {d : C.D}
    {f : Value → C.D} {a : MemAccess} {r : Nat} {gd : Option (Nat × Bool)}
    (hc : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (hext : a.ext = .same) (hr : a.regs = [r])
    (hW : ∀ e, Wf e → e.pc = C.pc d → ∀ x bs, e.kind = .rd x bs →
      ∃ v, rebuild 3 bs = .ok v ∧ P v)
    (hn : ∀ x bs v, rebuild 3 bs = .ok v → P v →
      C.next d ⟨C.pc d, .rd x bs⟩ = some (some (f v)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hoff : ∀ p ∈ C.facts d, p.1 ≠ r)
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hv : ∀ v, P v → ∀ tg, (qt (C.pc d + 1)).lookup r = some tg → tg.ok (some v))
    (hq : ∀ p ∈ qt (C.pc d + 1), p.1 ≠ r →
      (qt (C.pc d)).lookup p.1 = some p.2 ∨ ex.lookup p.1 = some p.2)
    (hok : ∀ v, P v → C.sub (f v) = 0 ∧ C.acc (f v) = [] ∧ C.inv (f v) ∧
      SegQ K A L g (QT qt) (C.pc d + 1) ((r, v) :: C.facts d) (C.pc (f v)) (C.facts (f v)))
    (e : Event) : C.StepForQ (QT qt) Wf d e := by
  intro t u ins h _ hc' hQ hWe hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf hext
  obtain ⟨v, hy, hPv⟩ := hW _ hWe (by rw [← h.1]) x bs rfl
  have ht := at_of_atD h hs ha
  rw [hr, afterLoad_ok ht.2.1 ht.2.2.1 hy]
  obtain ⟨hs', ha', hi, seg⟩ := hok v hPv
  obtain ⟨hP, hS0, hA, hFl, hR⟩ := ht
  have hu : At { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] }
      (C.pc d + 1) ((r, v) :: C.facts d) :=
    ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl, hFl, Function.update_self ..,
      holds_update hR hoff⟩
  have hQ' : QT qt { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } := by
    have hQt : Typed (qt (C.pc d)) t := by simpa [QT, h.1] using hQ
    intro r' tg hl
    have hl' : (qt (C.pc d + 1)).lookup r' = some tg := by
      simpa [hP] using hl
    by_cases hrr : r' = r
    · subst hrr
      exact (hv v hPv tg hl') |> fun h' => by simpa [setReg] using h'
    · have hne : (setReg t r v).regs r' = t.regs r' := by simp [setReg, Function.update_of_ne hrr]
      show tg.ok ((setReg t r v).regs r')
      rw [hne]
      rcases hq _ (lookup_mem hl') hrr with h1 | h1
      · exact hQt r' tg h1
      · exact hexT r' tg h1
  obtain ⟨t', hr', hg, hq'⟩ := landQ hu hQ' seg hi hs' ha'
  exact .inl ⟨f v, t', hn x bs v hy hPv, hr', hg, hq'⟩

end PTX.Flow.Code
