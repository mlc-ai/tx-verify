-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQ

@[expose] public section

/-! # A scalar `.nc` load under the tag invariant

`Code.ldNcQ`: the strict counterpart of `Code.step_loadNcU` for the invariant `QT qt`: the loaded
word is a 32-bit pattern (`hW`, a well-formedness of the event) that goes into the register `r`,
the facts gain it, and the machine goes on to `f y` by a strict segment. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- **A scalar `.nc` word load under the tag invariant.** -/
theorem ldNcQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d : C.D} {f : BitVec 64 → C.D}
    {a : MemAccess} {r base w : Nat} {sp : Space}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r])
    (hW : ∀ e, Wf e → ∀ x bs, e.kind = .nc x bs → ∃ y, rebuild 3 bs = .ok (.bits 32 y))
    (hn : ∀ x bs y, rebuild 3 bs = .ok (.bits 32 y) →
      C.next d ⟨C.pc d, .nc x bs⟩ = some (some (f y)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hoff : ∀ p ∈ C.facts d, p.1 ≠ r)
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hq : afterWrites qt (C.pc d) [(r, .bits 32)] ex = true)
    (hok : ∀ y, C.sub (f y) = 0 ∧ C.acc (f y) = [] ∧ C.inv (f y) ∧
      SegQ K A L g (QT qt) (C.pc d + 1) ((r, .bits 32 y) :: C.facts d) (C.pc (f y))
        (C.facts (f y))) (e : Event) : C.StepForQ (QT qt) Wf d e := by
  intro t u ins h _ hc' hQ hWe hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
  obtain ⟨y, hy⟩ := hW _ hWe x bs rfl
  have ht := at_of_atD h hs ha
  rw [hr, afterLoad_ok ht.2.1 ht.2.2.1 hy]
  obtain ⟨hs', ha', hi, seg⟩ := hok y
  obtain ⟨hP, hS0, hA, hFl, hR⟩ := ht
  have hu : At { setReg t r (.bits 32 y) with pc := t.pc + 1, sub := 0, acc := [] }
      (C.pc d + 1) ((r, .bits 32 y) :: C.facts d) :=
    ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl, hFl, Function.update_self ..,
      holds_update hR hoff⟩
  have hQ' : QT qt { setReg t r (.bits 32 y) with pc := t.pc + 1, sub := 0, acc := [] } := by
    refine QT.after hQ hexT hP (by simp [hP]) (fun r' tg hl => ?_) (fun r' hl => ?_) hq
    · simp only [List.lookup] at hl
      split at hl
      · rename_i hr'
        simp only [beq_iff_eq] at hr'
        simp only [Option.some.injEq] at hl
        subst hl; subst hr'
        exact ⟨y, by simp [setReg]⟩
      · simp at hl
    · have : ¬ r' = r := fun h' => by simp [List.lookup, h'] at hl
      simp [setReg, Function.update_of_ne this]
  obtain ⟨t', hr', hg, hq'⟩ := landQ hu hQ' seg hi hs' ha'
  exact .inl ⟨f y, t', hn x bs y hy, hr', hg, hq'⟩

end PTX.Flow.Code
