-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQFP

@[expose] public section

/-! # The strict step of a shuffle with one destination -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged PTX.Flow.TyG

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A shuffle whose result goes into `r` (no validity predicate): the received word has the tag
`tr`, and `f` is the state after it. -/
theorem shflOneFP {qt : Nat → EnvF} {Wf : Event → Prop} {P : TState → Prop} {d : C.D}
    {f : Value → C.D} {mode : ShflMode} {ty : Option DType} {r : Nat} {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨none, .warp ⟨.shfl mode, ty, [some r], [a, b, c],
      some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r) {tr : TagF} {Pv : Value → Prop}
    (hW : ∀ e, Wf e → e.pc = C.pc d → ∀ m av bv cv recv ok, e.kind = .shfl m av bv cv recv ok →
      Pv recv)
    (hv : ∀ x, Pv x → tr.ok (some x))
    (hn : ∀ m av bv cv recv ok, Pv recv →
      C.next d ⟨C.pc d, .shfl m av bv cv recv ok⟩ = some (some (f recv)))
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hq : afterF qt (C.pc d) [(r, tr)] = true)
    (hok : ∀ x, Pv x → C.sub (f x) = 0 ∧ C.acc (f x) = [] ∧ C.inv (f x) ∧
      SegQ K A L g (fun t => QTF qt t ∧ P t) (C.pc d + 1) ((r, x) :: C.facts d) (C.pc (f x))
        (C.facts (f x))) (e : Event) : C.StepForQP (QTF qt) P Wf d e := by
  intro t u ins h _ hc hQ hWe hf hPu
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  have hy := hW _ hWe (by rw [← h.1]) _ av bv cv recv ok rfl
  simp only [Option.elim] at hPu ⊢
  obtain ⟨hs', ha', hi, seg⟩ := hok recv hy
  have hat1 := At.set (r := r) (v := recv) h0 (fun q hq he => hr q hq he)
  have hQ' : QTF qt (PTX.next (setReg t r recv)) := by
    refine QTF.after1 hQ h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r' hl => ?_)
      (fun q hq' => ?_) hq
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
      simp [PTX.next, setReg, Function.update_of_ne hl]
    · simp only [List.mem_singleton] at hq'
      subst hq'
      simpa [PTX.next, setReg] using hv recv hy
  obtain ⟨t', hr', hg, hq'⟩ := landQ (Q := fun t => QTF qt t ∧ P t) hat1 ⟨hQ', hPu⟩ seg hi hs' ha'
  exact .inl ⟨f recv, t', hn _ av bv cv recv ok hy, hr', hg, hq'.1⟩

end PTX.Flow.Code
