-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TcStLen

@[expose] public section

/-! # The words a Tensor Memory store writes are its source registers' values

A proof tool beside `Lemmas/Flow/TcStLen.lean`. A `tcgen05.st` of an unpacked `32x32b` shape fires
a store event whose values are those of its source registers at the state it fires from
(`fires_tcSt_vals`): the word `i` is the value of register `r` when the instruction's source
operand `i` is register `r`. -/

namespace PTX.Flow
open PTX PTX.EventFrame

noncomputable section

/-- A template whose `32x32b` store event, if any, holds the values of the registers `regs` that
the source operands `ss` name. -/
def StVals (ss : List Opnd) (regs : Nat → Option Value) : Tmpl → Prop
  | .tc (.st _ vals .s32x32b) _ => vals.length = ss.length ∧
      ∀ i (hi : i < vals.length) r, ss[i]? = some (.reg r) → regs r = some vals[i]
  | _ => True

/-- A `mapM` into `Except` that succeeds maps each element to the element at its index. -/
theorem except_mapM_get {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r →
      ∀ (i : Nat) (x : α) (y : β), l[i]? = some x → r[i]? = some y → f x = .ok y
  | [], r, h, i, x, y, hx, _ => by simp at hx
  | a :: l, r, h, i, x, y, hx, hy => by
    simp only [List.mapM_cons] at h
    cases hfa : f a with
    | error z => rw [hfa] at h; cases h
    | ok b =>
      rw [hfa] at h
      cases hl : l.mapM f with
      | error z => rw [hl] at h; cases h
      | ok rs =>
        rw [hl] at h
        cases h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
          subst hx hy
          exact hfa
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx hy
          exact except_mapM_get hl i x y hx hy

theorem ofExec_stVals {ss : List Opnd} {regs : Nat → Option Value} {r : Exec Tmpl}
    (h : AllOk (StVals ss regs) r) : StVals ss regs (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- **The store template holds the registers' values.** -/
theorem tcTmpl_stVals {L : Launch} {g : Nat} {u : TState} {ta : Nat} {ss : List Opnd}
    {sh : TcShape} : StVals ss u.regs (tcTmpl L g u (.tcSt ta ss sh)) := by
  cases sh
  all_goals simp only [tcTmpl]
  all_goals refine ofExec_stVals ?_
  all_goals generalize hv : List.mapM (readValue L g u 32) ss = r
  all_goals generalize readBits L g u 32 (Opnd.reg ta) = rb
  all_goals cases rb
  all_goals cases r with
    | error x => ?_
    | ok vals => ?_
  all_goals try have hl := except_mapM_length hv
  all_goals split_ifs <;> simp only [AllOk, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, pure, Except.pure]
  all_goals try split_ifs
  all_goals simp only [StVals]
  all_goals refine ⟨hl, fun i hi r hr => ?_⟩
  all_goals have hg := except_mapM_get hv i _ _ hr (List.getElem?_eq_getElem hi)
  all_goals simp only [readValue, readReg] at hg
  all_goals revert hg
  all_goals cases u.regs r <;> simp [pure, throw, throwThe, MonadExceptOf.throw, Except.pure]

/-- **A `32x32b` store fired by an instruction stores its source registers' values.** -/
theorem fires_tcSt_vals {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Nat} {vals : List Value} (hk : e.kind = .tc (.st a vals .s32x32b)) :
    ∃ ta ss sh, op = .tcSt ta ss sh ∧ vals.length = ss.length ∧
      ∀ i (hi : i < vals.length) r, ss[i]? = some (.reg r) → t.regs r = some vals[i] := by
  have hop := fires_tcSt_op hf hk
  cases op <;> simp only [tcStOp, Bool.false_eq_true] at hop
  rename_i ta ss sh
  refine ⟨ta, ss, sh, rfl, ?_⟩
  have h1 : ∀ u : TState, u.regs = t.regs → StVals ss t.regs (tcTmpl L g u (.tcSt ta ss sh)) :=
    fun u hu => by
      have := tcTmpl_stVals (L := L) (g := g) (u := u) (ta := ta) (ss := ss) (sh := sh)
      rwa [hu] at this
  have hm : StVals ss t.regs (eventTmpl A L g t (.tcSt ta ss sh)) := by
    simp only [eventTmpl, tcStTmpl]
    split
    · split
      · split <;> trivial
      · exact h1 _ rfl
    · exact h1 _ rfl
  generalize eventTmpl A L g t (.tcSt ta ss sh) = tm at hm hf
  cases tm <;> simp only [Fires] at hf
  all_goals first
    | (obtain ⟨rfl, -⟩ := hf; cases hk)
    | (obtain ⟨_, rfl, -⟩ := hf; cases hk)
    | (obtain ⟨_, _, rfl, -⟩ := hf; cases hk)
  exact hm

end
end PTX.Flow
