-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQ

@[expose] public section

/-! # A scalar weak load under the tag invariant

`Code.ldWQ`: the strict step of a scalar weak load (`ld.global.b32`, `ld.global.b16`) into a
register `r` the facts do not name. The value the bytes rebuild to satisfies the event's
well-formedness `P` (`hW`), and goes into `r`: if the invariant tags `r` after the load, the value
has the tag (`hv`); the tags of the other registers are those before (`hq`). The facts gain the
value, and the machine goes on to `f v` by a strict segment. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- **A scalar weak load under the tag invariant.** -/
theorem ldWQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {P : Value → Prop} {d : C.D}
    {f : Value → C.D} {a : MemAccess} {r : Nat}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
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
