-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotTcData

@[expose] public section

/-! # An instruction of a data event fires that event or undefined behaviour

A proof tool, the converse of `fires_tcData_op`. A Tensor Memory load, store or wait that no
assumption selects with a hook fires a data event, or is undefined behaviour
(`fires_tcData_of_op`). With `fires_tcData_op`, a consistent execution's data events without
undefined behaviour are exactly those at the positions of data instructions. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- A template that is a data event's or undefined behaviour. -/
def TcDataOrUb : Tmpl → Prop
  | .ub _ | .tcLd .. | .tc (.ld ..) _ | .tc .waitLd _ | .tc (.st ..) _ | .tc .waitSt _ => True
  | _ => False

theorem ofExec_tcDataOrUb {r : Exec Tmpl} (h : PTX.EventFrame.AllOk TcDataOrUb r) :
    TcDataOrUb (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- The template of a data instruction is a data event's or undefined behaviour. -/
theorem tcTmpl_tcDataOrUb {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : tcDataOp op = true) : TcDataOrUb (tcTmpl L g t op) := by
  cases op <;> simp only [tcDataOp, Bool.false_eq_true] at hop
  case tcLd ds ta shape red =>
    cases shape <;> simp only [tcTmpl] <;> apply ofExec_tcDataOrUb <;>
    repeat' first
      | (apply PTX.EventFrame.allOk_bind; intro _)
      | split
      | exact trivial
  case tcSt ta ss shape =>
    cases shape <;> simp only [tcTmpl] <;> apply ofExec_tcDataOrUb <;>
    repeat' first
      | (apply PTX.EventFrame.allOk_bind; intro _)
      | split
      | exact trivial
  all_goals simp only [tcTmpl]
  all_goals apply ofExec_tcDataOrUb
  all_goals repeat' first
    | (apply PTX.EventFrame.allOk_bind; intro _)
    | split
    | exact trivial

/-- An event of a data template is a data event or undefined behaviour. -/
theorem fires_tcDataOrUb {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState}
    (hm : TcDataOrUb m) (hf : Fires pc m e o) : isTcData e = true ∨ ∃ f, e.kind = .ub f := by
  cases m <;> simp only [TcDataOrUb] at hm <;> simp only [Fires] at hf
  case ub f => exact .inr ⟨f, by rw [hf.1]⟩
  case tcLd a n sh k =>
    obtain ⟨vals, -, rfl, -⟩ := hf
    exact .inl rfl
  case tc k u =>
    obtain ⟨rfl, -⟩ := hf
    cases k <;> first | exact .inl rfl | exact hm.elim

/-- **A data instruction fires a data event or undefined behaviour**, at a site no assumption
selects with the load or store hook. -/
theorem fires_tcData_of_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    (hop : tcDataOp op = true) (hld : A.any (·.tcLdWait t.pc) = false)
    (hst : A.any (·.tcStWaitLd t.pc) = false) :
    isTcData e = true ∨ ∃ f, e.kind = .ub f := by
  refine fires_tcDataOrUb ?_ hf
  cases op <;> simp only [tcDataOp, Bool.false_eq_true] at hop
  case tcLd ds ta sh red =>
    rw [eventTmpl_tcLd_noWait hld]
    exact tcTmpl_tcDataOrUb rfl
  case tcSt ta ss sh =>
    rw [eventTmpl_tcSt_noWait hst]
    exact tcTmpl_tcDataOrUb rfl
  case tcWaitLd => simpa only [eventTmpl] using tcTmpl_tcDataOrUb (L := L) (g := g) (t := t) rfl
  case tcWaitSt => simpa only [eventTmpl] using tcTmpl_tcDataOrUb (L := L) (g := g) (t := t) rfl

end
end PTX.Flow
