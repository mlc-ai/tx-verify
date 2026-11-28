-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TcStVals

@[expose] public section

/-! # The values of an unpacked Tensor Memory store of any shape are its source registers'

A proof tool. `TcStVals` says it for the `32x32b` shape; the rule reads each source register of any
shape that is not `.pack::16b` at the state of the store, so the value of the event at the
position of a source register is the register's (`fires_tcSt_valsAny`). -/

namespace PTX.Flow

open PTX PTX.Proof

noncomputable section

/-- A `mapM` into `Except` that succeeds maps each element to the element at its index. -/
theorem mapM_ok_idx {α β ε : Type} {f : α → Except ε β} :
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
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
          subst hx
          subst hy
          exact hfa
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx hy
          exact mapM_ok_idx hl i x y hx hy

/-- A `mapM` into `Except` that succeeds keeps the length. -/
theorem mapM_ok_len {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.length = l.length
  | [], r, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons] at h
    cases hfa : f a with
    | error z => rw [hfa] at h; cases h
    | ok b =>
      rw [hfa] at h
      cases hl : l.mapM f with
      | error z => rw [hl] at h; cases h
      | ok rs =>
        rw [hl] at h
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [mapM_ok_len hl]

/-- **An unpacked store event of any shape stores its source registers' values.** -/
theorem fires_tcSt_valsAny {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {pc : Nat} {e : Event} {o : Option TState} {ta a : Nat} {ss : List Opnd} {sh sh' : TcShape}
    {vals : List Value} (hsh : ∀ s, sh ≠ .packed16 s)
    (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e o)
    (hk : e.kind = .tc (.st a vals sh')) :
    vals.length = ss.length ∧
      ∀ i (hi : i < vals.length) r, ss[i]? = some (.reg r) → t.regs r = some vals[i] := by
  obtain ⟨u, hu, hf⟩ := fires_tcSt_core hf hk (by intro h; cases h)
  rw [tcTmpl_tcSt_plain hsh] at hf
  cases ha : readBits L g u 32 (.reg ta) <;> cases hm : ss.mapM (readValue L g u 32) <;>
    simp only [ofExec, ha, hm, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf <;>
    split_ifs at hf <;> simp only [Fires] at hf <;> rw [hf.1] at hk <;>
    simp only [reduceCtorEq, Kind.tc.injEq, TcKind.st.injEq] at hk
  rename_i vs _ _ _ _
  refine ⟨by rw [← hk.2.1, mapM_ok_len hm], fun i hi r hr => ?_⟩
  have hv : vs[i]? = some vals[i] := by rw [hk.2.1, List.getElem?_eq_getElem hi]
  have hg := mapM_ok_idx hm i _ _ hr hv
  simp only [readValue, readReg, hu, pure, Except.pure] at hg
  revert hg
  cases h : t.regs r <;> simp [throw, throwThe, MonadExceptOf.throw]

end
end PTX.Flow
