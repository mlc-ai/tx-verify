-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotTcSt

@[expose] public section

/-! # The values of a Tensor Memory store fill 4 bytes

A proof tool. The `tcgen05.st` rule reads each source register as a 32-bit value and stops with a
type mismatch unless every value fills 4 bytes (THREAD-TC), so every value of a fired store event
has 4 bytes (`fires_tcSt_bytes`); only a store instruction fires one (`fires_tcSt_op`). The shape
is not `.pack::16b`, whose event holds the values unpacked into 2-byte slices. -/

namespace PTX.Flow

open PTX PTX.Proof

noncomputable section

/-- **Every value of a Tensor Memory store event fills 4 bytes.** -/
theorem fires_tcSt_bytes {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh))
    (hsh : ∀ s, sh ≠ .packed16 s) :
    ∀ v ∈ vals, v.bytes = 4 := by
  have hop := fires_tcSt_op hf hk
  cases op <;> simp only [tcStOp, Bool.false_eq_true] at hop
  rename_i ta ss s
  obtain ⟨u, _, hf⟩ := fires_tcSt_core hf hk (by intro h; cases h)
  cases s with
  | packed16 s' =>
    simp only [tcTmpl] at hf
    cases hr : readBits L g u 32 (.reg ta) <;> cases hm : ss.mapM (readValue L g u 32) <;>
      simp only [ofExec, hr, hm, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hf <;>
      split_ifs at hf <;> simp only [Fires] at hf <;> rw [hf.1] at hk <;>
      simp only [reduceCtorEq, Kind.tc.injEq, TcKind.st.injEq] at hk
    exact absurd hk.2.2.symm (hsh s')
  | s32x32b | s16x64b | s16x128b | s16x256b | s16x32bx2 n =>
    simp only [tcTmpl] at hf
    cases hr : readBits L g u 32 (.reg ta) <;> cases hm : ss.mapM (readValue L g u 32) <;>
      simp only [ofExec, hr, hm, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hf <;>
      split_ifs at hf <;> simp only [Fires] at hf <;> rw [hf.1] at hk <;>
      simp only [reduceCtorEq, Kind.tc.injEq, TcKind.st.injEq] at hk
    rename_i vs _ _ h4
    rw [← hk.2.1]
    simpa using List.all_eq_true.mp h4

end

end PTX.Flow
