-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQFO

@[expose] public section

/-! # The strict step of a shuffle whose successor depends on the sent word

`shflOneFPa` is `shflOneFP` for a machine whose state after the shuffle records the word the
thread sent as well as the one it received. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged PTX.Flow.TyG

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A shuffle whose result goes into `r`: the received word has the tag `tr`, and `f` is the state
after it, given the sent and the received word. -/
theorem shflOneFPa {qt : Nat → EnvF} {Wf : Event → Prop} {P : TState → Prop} {d : C.D}
    {f : Value → Value → C.D} {mode : ShflMode} {ty : Option DType} {r : Nat}
    {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨none, .warp ⟨.shfl mode, ty, [some r], [a, b, c],
      some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r) {tr : TagF} {Pv : Value → Prop}
    (hW : ∀ e, Wf e → e.pc = C.pc d → ∀ m av bv cv recv ok, e.kind = .shfl m av bv cv recv ok →
      Pv recv)
    (hv : ∀ x, Pv x → tr.ok (some x))
    (hn : ∀ m av bv cv recv ok, Pv recv →
      C.next d ⟨C.pc d, .shfl m av bv cv recv ok⟩ = some (some (f av recv)))
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hq : afterF qt (C.pc d) [(r, tr)] = true)
    (hok : ∀ av x, Pv x → C.sub (f av x) = 0 ∧ C.acc (f av x) = [] ∧ C.inv (f av x) ∧
      SegQ K A L g (fun t => QTF qt t ∧ P t) (C.pc d + 1) ((r, x) :: C.facts d)
        (C.pc (f av x)) (C.facts (f av x))) (e : Event) : C.StepForQP (QTF qt) P Wf d e := by
  intro t u ins h _ hc hQ hWe hf hPu
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  simp only [Option.elim] at hPu ⊢
  have hy := hW _ hWe (by rw [← h.1]) _ av bv cv recv ok rfl
  have hat1 := At.set (r := r) (v := recv) (at_of_atD h hs ha) (fun q hq he => hr q hq he)
  obtain ⟨hs1, ha1, hi1, seg⟩ := hok av recv hy
  have hQ1 : QTF qt (PTX.next (setReg t r recv)) := by
    refine QTF.after1 hQ h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r' hl => ?_)
      (fun q hq' => ?_) hq
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
      simp [PTX.next, setReg, Function.update_of_ne hl]
    · simp only [List.mem_singleton] at hq'
      subst hq'
      simpa [PTX.next, setReg] using hv recv hy
  obtain ⟨t1, hr1, hg1, hq2⟩ := landQ (Q := fun t => QTF qt t ∧ P t) hat1 ⟨hQ1, hPu⟩ seg hi1 hs1 ha1
  exact .inl ⟨f av recv, t1, hn _ av bv cv recv ok hy, hr1, hg1, hq2.1⟩

end PTX.Flow.Code
