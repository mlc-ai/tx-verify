-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DivStep
public import Lemmas.Flow.Arith32Wide

@[expose] public section

/-! # `or.b32` of a register fact and a received word

A proof tool. A shuffle's received word is a `Value` that the machine does not know to be a 32-bit
word. `or.b32` reads its operand as bits (`readBits`): any value with a bit pattern is read, a
predicate, a pointer or an opaque value faults. `rvw v` is the word the instruction reads
(`v`'s bit pattern, `0` where it has none); `SegU.or_rv_left` and `SegU.or_rv_right` are the
UB-tolerant pieces for the received word as the first or the second source: a value without a bit
pattern kills the thread, any other continues with `or32 (rvw v) y` as a fact. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

namespace Arith32

/-- The word a bit-reading instruction takes from a value (`0` for a value without a pattern). -/
def rvw (v : Value) : BitVec 64 :=
  match v with
  | .bits _ x => x
  | _ => (v.bitPattern.map (BitVec.ofNat 64)).getD 0

end Arith32

open Arith32

set_option maxRecDepth 100000

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- What `readBits` returns for a register that holds a value with a bit pattern. -/
theorem readBits_rvw {t : TState} {r : Nat} {v : Value} (h : t.regs r = some v)
    (hp : v.bitPattern.isSome = true) : readBits L g t 32 (.reg r) = .ok (r32 (rvw v)) := by
  unfold readBits
  simp only [readReg, h]
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hp
  rcases v with ⟨w, x⟩ | ⟨f, x⟩ | b | ⟨w, ge, tg, o⟩ | c | _ | f | ⟨lo, hi⟩ | ⟨wh, o, sz⟩
  · simp [rvw, r32, bind, Except.bind, pure, Except.pure]
  all_goals first
    | (exfalso; simp [Value.bitPattern] at hn; done)
    | simp [hn, rvw, r32, bind, Except.bind, pure, Except.pure]


theorem readBits_b32 {t : TState} {r : Nat} {y : BitVec 64} (h : t.regs r = some (.bits 32 y)) :
    readBits L g t 32 (.reg r) = .ok (r32 y) := by
  simp [readBits, readReg, h, r32, bind, Except.bind, pure, Except.pure]

/-- `or.b32 d, a, r` with the register `a` holding a value with a bit pattern. -/
theorem Seg.or_rv_left {pc d a r : Nat} {v : Value} {y : BitVec 64} {F : List (Nat × Value)}
    (hc : K.code[pc]? =
      some ⟨none, .int ⟨.or, .int .b 32, false, [some d], [.reg a, .reg r]⟩⟩)
    (ha : (a, v) ∈ F) (hr : (r, Value.bits 32 y) ∈ F) (hp : v.bitPattern.isSome = true)
    (hd : ∀ q ∈ F, q.1 ≠ d)
    (hL : ∀ (t : TState), t.pc = pc → ∀ as ∈ A,
      as.localRule L g t (.int ⟨.or, .int .b 32, false, [some d], [.reg a, .reg r]⟩) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    Seg K A L g 1 pc F (pc + 1) ((d, .bits 32 (or32 (rvw v) y)) :: F) := by
  intro t h
  refine ⟨_, ?_, At.set h hd⟩
  have hx := holds_mem h.2.2.2.2 ha
  have hy := holds_mem h.2.2.2.2 hr
  have hrb := readBits_rvw (L := L) (g := g) hx hp
  simp [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, Op.isLocal, Op.varyingSregs,
    Opnd.varying?, List.filterMap, hA.exec, execLocalRule_of_none (hL t h.1),
    execLocal_int (i := ⟨.or, .int .b 32, false, [some d], [.reg a, .reg r]⟩) rfl,
    execInt, DType.width, hrb, readBits_b32 (L := L) (g := g) hy, bind, Except.bind, pure,
    Except.pure, or32]

/-- `or.b32 d, r, a` with the register `a` holding a value with a bit pattern. -/
theorem Seg.or_rv_right {pc d a r : Nat} {v : Value} {y : BitVec 64} {F : List (Nat × Value)}
    (hc : K.code[pc]? =
      some ⟨none, .int ⟨.or, .int .b 32, false, [some d], [.reg r, .reg a]⟩⟩)
    (ha : (a, v) ∈ F) (hr : (r, Value.bits 32 y) ∈ F) (hp : v.bitPattern.isSome = true)
    (hd : ∀ q ∈ F, q.1 ≠ d)
    (hL : ∀ (t : TState), t.pc = pc → ∀ as ∈ A,
      as.localRule L g t (.int ⟨.or, .int .b 32, false, [some d], [.reg r, .reg a]⟩) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    Seg K A L g 1 pc F (pc + 1) ((d, .bits 32 (or32 y (rvw v))) :: F) := by
  intro t h
  refine ⟨_, ?_, At.set h hd⟩
  have hx := holds_mem h.2.2.2.2 ha
  have hy := holds_mem h.2.2.2.2 hr
  have hrb := readBits_rvw (L := L) (g := g) hx hp
  simp [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, Op.isLocal, Op.varyingSregs,
    Opnd.varying?, List.filterMap, hA.exec, execLocalRule_of_none (hL t h.1),
    execLocal_int (i := ⟨.or, .int .b 32, false, [some d], [.reg r, .reg a]⟩) rfl,
    execInt, DType.width, hrb, readBits_b32 (L := L) (g := g) hy, bind, Except.bind, pure,
    Except.pure, or32]


theorem readBits_none {t : TState} {r : Nat} {v : Value} (h : t.regs r = some v)
    (hp : v.bitPattern.isSome = false) : ∃ f, readBits L g t 32 (.reg r) = .error f := by
  have hn : v.bitPattern = none := by cases h' : v.bitPattern <;> simp_all
  unfold readBits
  simp only [readReg, h]
  rcases v with ⟨w, x⟩ | ⟨f, x⟩ | b | ⟨w, ge, tg, o⟩ | c | _ | f | ⟨lo, hi⟩ | ⟨wh, o, sz⟩
  · simp [Value.bitPattern] at hp
  · exact ⟨.typeMismatch, by simp [hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]⟩
  · exact ⟨.typeMismatch, by simp [hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]⟩
  · exact ⟨.noRule, by simp [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]⟩
  · exact ⟨.typeMismatch, by simp [hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]⟩
  · exact ⟨.noRule, by simp [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]⟩
  · exact ⟨.typeMismatch, by simp [hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]⟩
  · exact ⟨.typeMismatch, by simp [hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]⟩
  · exact ⟨.typeMismatch, by simp [hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]⟩

/-- **`or.b32` of a register fact and a received word** (the word first), UB-tolerant. -/
theorem SegU.or_rv_left {pc d a r b : Nat} {v : Value} {y : BitVec 64} {F G : List (Nat × Value)}
    (hc : K.code[pc]? =
      some ⟨none, .int ⟨.or, .int .b 32, false, [some d], [.reg a, .reg r]⟩⟩)
    (ha : (a, v) ∈ F) (hr : (r, Value.bits 32 y) ∈ F) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hL : ∀ (t : TState), t.pc = pc → ∀ as ∈ A,
      as.localRule L g t (.int ⟨.or, .int .b 32, false, [some d], [.reg a, .reg r]⟩) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc)
    (h : SegU K A L g (pc + 1) ((d, .bits 32 (or32 (rvw v) y)) :: F) b G) :
    SegU K A L g pc F b G := by
  by_cases hp : v.bitPattern.isSome = true
  · exact SegU.comp (SegU.of_seg (Seg.or_rv_left hc ha hr hp hd hL hA)) h
  · intro t ht
    obtain ⟨f, hx⟩ := readBits_none (L := L) (g := g) (holds_mem ht.2.2.2.2 ha)
      (by simpa using hp)
    refine .inr (dead_of_error (op := .int ⟨.or, .int .b 32, false, [some d],
      [.reg a, .reg r]⟩) (ht.1 ▸ hc) rfl ht.2.2.2.1 (f := f) ?_)
    simp [hA.exec (ht.1), execLocalRule_of_none (hL t ht.1),
      execLocal_int (i := ⟨.or, .int .b 32, false, [some d], [.reg a, .reg r]⟩) rfl,
      execInt, DType.width, hx, bind, Except.bind]

/-- **`or.b32` of a register fact and a received word** (the word second), UB-tolerant. -/
theorem SegU.or_rv_right {pc d a r b : Nat} {v : Value} {y : BitVec 64}
    {F G : List (Nat × Value)}
    (hc : K.code[pc]? =
      some ⟨none, .int ⟨.or, .int .b 32, false, [some d], [.reg r, .reg a]⟩⟩)
    (ha : (a, v) ∈ F) (hr : (r, Value.bits 32 y) ∈ F) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hL : ∀ (t : TState), t.pc = pc → ∀ as ∈ A,
      as.localRule L g t (.int ⟨.or, .int .b 32, false, [some d], [.reg r, .reg a]⟩) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc)
    (h : SegU K A L g (pc + 1) ((d, .bits 32 (or32 y (rvw v))) :: F) b G) :
    SegU K A L g pc F b G := by
  by_cases hp : v.bitPattern.isSome = true
  · exact SegU.comp (SegU.of_seg (Seg.or_rv_right hc ha hr hp hd hL hA)) h
  · intro t ht
    obtain ⟨f, hx⟩ := readBits_none (L := L) (g := g) (holds_mem ht.2.2.2.2 ha)
      (by simpa using hp)
    refine .inr (dead_of_error (op := .int ⟨.or, .int .b 32, false, [some d],
      [.reg r, .reg a]⟩) (ht.1 ▸ hc) rfl ht.2.2.2.1 (f := f) ?_)
    have hy := holds_mem ht.2.2.2.2 hr
    simp [hA.exec (ht.1), execLocalRule_of_none (hL t ht.1),
      execLocal_int (i := ⟨.or, .int .b 32, false, [some d], [.reg r, .reg a]⟩) rfl,
      execInt, DType.width, hx, readBits_b32 (L := L) (g := g) hy, bind, Except.bind]

end
end PTX.Flow
