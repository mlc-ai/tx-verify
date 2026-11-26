-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQ

@[expose] public section

/-! # A strict shuffle whose successor reads the received word

`Code.shflRecvQ` is `Code.shflAnyQ` (`Lemmas/Flow/StepsQ.lean`) for a machine that keeps the
received word: the successor is a function of it (a data shuffle of the index warp, whose later
stores depend on the words its quad's lanes sent). -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- **A shuffle under the tag invariant whose successor reads the received word**: the received
word is 32 bits (`hW`), the successor `dn y` a function of it; the word goes into `r`, the
validity into `p`. -/
theorem shflRecvQ {qt : Nat → Env} {ex : Env} {Wf : Event → Prop} {d : C.D}
    {dn : BitVec 64 → C.D} {mode : ShflMode}
    {ty : Option DType} {r p : Nat} {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨none, .warp ⟨.shfl mode, ty, [some r, some p], [a, b, c],
      some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r) (hp : ∀ q ∈ C.facts d, q.1 ≠ p) (hrp : r ≠ p)
    (hW : ∀ e, Wf e → ∀ m av bv cv recv ok, e.kind = .shfl m av bv cv recv ok →
      ∃ y, recv = .bits 32 y)
    (hn : ∀ m av bv cv y ok, C.next d ⟨C.pc d, .shfl m av bv cv (.bits 32 y) ok⟩ =
      some (some (dn y))) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hs' : ∀ y, C.sub (dn y) = 0) (ha' : ∀ y, C.acc (dn y) = []) (hi : ∀ y, C.inv (dn y))
    (hex : ∀ t, C.AtD d t → Typed ex t)
    (hq : afterWrites qt (C.pc d) [(r, .bits 32), (p, .pred)] ex = true)
    (seg : ∀ y ok, SegQ K A L g (QT qt) (C.pc d + 1)
      ((p, .pred ok) :: (r, .bits 32 y) :: C.facts d) (C.pc (dn y)) (C.facts (dn y))) (e : Event) :
    C.StepForQ (QT qt) Wf d e := by
  intro t u ins h _ hc hQ hWe hf
  have hexT := hex t h
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := some p) hf
  obtain ⟨y, rfl⟩ := hW _ hWe _ av bv cv recv ok rfl
  have hat1 : At (setReg t r (.bits 32 y)) (C.pc d) ((r, .bits 32 y) :: C.facts d) :=
    ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, Function.update_self .., holds_update h0.2.2.2.2 hr⟩
  have hp' : ∀ q ∈ (r, Value.bits 32 y) :: C.facts d, q.1 ≠ p := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hrp
    · exact hp q hq
  have hu := At.set (v := .pred ok) hat1 hp'
  have hQ' : QT qt (PTX.next (setReg (setReg t r (.bits 32 y)) p (.pred ok))) := by
    refine QT.after hQ hexT h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r' tg hl => ?_)
      (fun r' hl => ?_) hq
    · by_cases h1 : r' = p
      · subst h1
        have e0 : (r' == r) = false := beq_eq_false_iff_ne.mpr (Ne.symm hrp)
        simp [List.lookup, e0] at hl
        subst hl
        exact ⟨ok, by simp [PTX.next, setReg]⟩
      · by_cases h0 : r' = r
        · subst h0
          simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
          subst hl
          exact ⟨y, by simp [PTX.next, setReg, Function.update_of_ne h1]⟩
        · have e1 : (r' == r) = false := by simpa using h0
          have e2 : (r' == p) = false := by simpa using h1
          simp [List.lookup, e1, e2] at hl
    · obtain ⟨h0, h1⟩ := lookup2_none hl
      simp [PTX.next, setReg, Function.update_of_ne h0, Function.update_of_ne h1]
  obtain ⟨t', hr', hg, hq'⟩ := landQ hu hQ' (seg y ok) (hi y) (hs' y) (ha' y)
  exact .inl ⟨dn y, t', hn _ av bv cv y ok, hr', hg, hq'⟩

end PTX.Flow.Code
