-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TcStAddr

@[expose] public section

/-! # The values a Tensor Memory store writes are its source registers' values

A proof tool: `fires_tcSt_word` states that a plain `tcgen05.st` stores at position `p` the value
the register of its source `p` holds. -/

namespace PTX.Flow
open PTX PTX.Proof

/-- A successful `mapM` in `Except` returns, at each position, the result of the element there. -/
theorem mapM_word_get {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → ∀ {p : Nat} {x : α}, l[p]? = some x →
      ∃ y, f x = .ok y ∧ r[p]? = some y
  | [], r, _, p, x, hx => by simp at hx
  | a :: l, r, h, p, x, hx => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hb : f a with
    | error e => rw [hb] at h; cases h
    | ok b =>
      rw [hb] at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok bs =>
        rw [hl] at h
        simp only [Except.ok.injEq] at h
        subst h
        cases p with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact ⟨b, hb, rfl⟩
        | succ p =>
          simp only [List.getElem?_cons_succ] at hx ⊢
          exact mapM_word_get hl hx

/-- **A `tcgen05.st` stores its source registers' values.** -/
theorem fires_tcSt_word {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat}
    {e : Event} {o : Option TState} {ta a : Nat} {ss : List Opnd} {sh sh' : TcShape}
    {vals : List Value} (hsh : ∀ s, sh ≠ .packed16 s)
    (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e o)
    (hk : e.kind = .tc (.st a vals sh'))
    {p r : Nat} {v : Value} (hs : ss[p]? = some (.reg r)) (hv : t.regs r = some v) :
    vals[p]? = some v := by
  obtain ⟨u, hu, hf⟩ := fires_tcSt_core hf hk (by intro h; cases h)
  rw [tcTmpl_tcSt_plain hsh] at hf
  cases ha : readBits L g u 32 (.reg ta) <;> cases hm : ss.mapM (readValue L g u 32) <;>
    simp only [ofExec, ha, hm, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf <;>
    split_ifs at hf <;> simp only [Fires] at hf <;> rw [hf.1] at hk <;>
    simp only [reduceCtorEq, Kind.tc.injEq, TcKind.st.injEq] at hk
  rename_i vs _ _ _ _
  rw [← hk.2.1]
  obtain ⟨y, hy, hget⟩ := mapM_word_get hm hs
  simp only [readValue, readReg, hu, hv, pure, Except.pure, Except.ok.injEq] at hy
  rw [hget, hy]

end PTX.Flow
