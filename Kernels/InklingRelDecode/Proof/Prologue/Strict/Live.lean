-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Safe
import Lemmas.Flow.Step.ShapeRegs
import Kernels.InklingRelDecode.Flow.Code.Part000

@[expose] public section

/-! # The prologue is not lost on an event that is not undefined behaviour

The successor of a state of the prologue is `none` only on a load site fired by something that is
no read, or on an election site fired by something that is no election. The template of a load
fires a read or undefined behaviour, and that of an election an election or undefined
behaviour. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow Control

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem ld_load : ∀ i : Fin 3, Lib.globalLoad (Site.ld i).pc (2055 + i.val) 32 = true := by
  decide +kernel

/-- The code at `pc` is an election with two destinations. -/
def electOne (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨_, .warp ⟨.elect, _, [_, some _], [], some _⟩⟩ => true
  | _ => false

theorem el_code : (∀ i : Fin 12, electOne (Site.el i).pc = true) ∧
    ∀ (b : Fin 3) (j : Fin 4), electOne (Site.pel b j).pc = true := by decide +kernel

theorem elect_kind {pc : Nat} {ins : Instr} {t : TState} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins) (h : electOne pc = true)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    (∃ mk inst ld, e.kind = .elect mk inst ld) ∨ ∃ f, e.kind = .ub f := by
  unfold electOne at h
  rw [hc] at h
  split at h
  · rename_i gd ty dst p mk heq
    simp only [Option.some.injEq] at heq
    subst heq
    exact fires_elect_kind hf
  · cases h

/-- **The successor of a state of the prologue on an event that is not undefined behaviour is not
`none`.** -/
theorem live_pro {d : Data.D} {t : TState} {ins : Instr} {v : Event} {o : Option TState}
    (hc : kernel.code[d.c.site.pc]? = some ins)
    (hf : Fires d.c.site.pc (eventTmpl Assumptions.all L g t ins.op) v o)
    (hu : ∀ f, v.kind ≠ .ub f) : Data.succ Q L g d v ≠ none := by
  have key : Control.next Q L g d.c v ≠ none → Data.succ Q L g d v ≠ none := by
    intro h hn
    exact h (Option.map_eq_none_iff.mp hn)
  apply key
  obtain ⟨⟨s, a, y, p, won, bc⟩, vs⟩ := d
  cases s with
  | ld i =>
    have hk := Lib.global_load_kind hc (ld_load i) hf
    rcases hk with ⟨a', bs, hk⟩ | ⟨f, hk⟩
    · fin_cases i <;> simp [Control.next, hk]
    · exact absurd hk (hu f)
  | el i =>
    rcases elect_kind hc (el_code.1 i) hf with ⟨mk, inst, ld, hk⟩ | ⟨f, hk⟩
    · simp [Control.next, hk]
    · exact absurd hk (hu f)
  | pel b j =>
    rcases elect_kind hc (el_code.2 b j) hf with ⟨mk, inst, ld, hk⟩ | ⟨f, hk⟩
    · simp [Control.next, hk]
    · exact absurd hk (hu f)
  | pb b j => fin_cases j <;> simp [Control.next]
  | lb b h => fin_cases h <;> simp [Control.next]
  | st9 j => fin_cases j <;> simp [Control.next]
  | _ => simp [Control.next]

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
