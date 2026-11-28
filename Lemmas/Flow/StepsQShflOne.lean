-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQ

@[expose] public section

/-! # A shuffle with one destination under the tag invariant

`Code.shflOneQ` is `Code.shflAnyQ` for a shuffle that writes only its data register (no
validity predicate): the received word is 32 bits and goes into `r`. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

theorem shflOneQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d : C.D} {dn : Value → C.D}
    {mode : ShflMode} {ty : Option DType} {r : Nat} {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨none, .warp ⟨.shfl mode, ty, [some r], [a, b, c],
      some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r)
    (hW : ∀ e, Wf e → e.pc = C.pc d → ∀ m av bv cv recv ok, e.kind = .shfl m av bv cv recv ok →
      ∃ y, recv = .bits 32 y)
    (hn : ∀ m av bv cv recv ok, C.next d ⟨C.pc d, .shfl m av bv cv recv ok⟩ = some (some (dn recv)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hs' : ∀ recv, C.sub (dn recv) = 0)
    (ha' : ∀ recv, C.acc (dn recv) = []) (hi : ∀ y, C.inv (dn (.bits 32 y)))
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hq : afterWrites qt (C.pc d) [(r, .bits 32)] ex = true)
    (seg : ∀ y, SegQ K A L g (QT qt) (C.pc d + 1) ((r, .bits 32 y) :: C.facts d)
      (C.pc (dn (.bits 32 y))) (C.facts (dn (.bits 32 y)))) (e : Event) :
    C.StepForQ (QT qt) Wf d e := by
  intro t u ins h _ hc hQ hWe hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  obtain ⟨y, rfl⟩ := hW _ hWe rfl _ av bv cv recv ok rfl
  have hu := At.set (v := .bits 32 y) h0 hr
  have hQ' : QT qt (PTX.next (setReg t r (.bits 32 y))) := by
    refine QT.after hQ hexT h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r' tg hl => ?_)
      (fun r' hl => ?_) hq
    · by_cases h1 : r' = r
      · subst h1
        simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
        subst hl
        exact ⟨y, by simp [PTX.next, setReg]⟩
      · have e1 : (r' == r) = false := by simpa using h1
        simp [List.lookup, e1] at hl
    · have h1 : r' ≠ r := fun h' => by simp [List.lookup, h'] at hl
      simp [PTX.next, setReg, Function.update_of_ne h1]
  obtain ⟨t', hr', hg, hq'⟩ := landQ hu hQ' (seg y) (hi y) (hs' _) (ha' _)
  exact .inl ⟨dn (.bits 32 y), t', hn _ av bv cv _ ok, hr', hg, hq'⟩

end PTX.Flow.Code
