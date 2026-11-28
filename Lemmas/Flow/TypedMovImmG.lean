-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQFJ

@[expose] public section

/-! # `mov.b32 d, 0f...`: a constant is a datum

`absMovImm` tags the register of a 32-bit move of a `0f` constant as `.f32` data. `absF4` is
`absF3` with this rule, `segQF4_runW` the typed run of it. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- `mov.b32 d, 0fXXXXXXXX`. -/
def absMovImm (_ : EnvF) : Op → Option (List (Nat × TagF))
  | .move m =>
    match m.kind, m.ty, m.dsts, m.srcs with
    | .scalar, .int _ 32, [some d], [.f32imm _] =>
      if m.rule == some .threadMove then some [(d, .dat32)] else none
    | _, _, _, _ => none
  | _ => none

theorem absMovImm_sound {a b : Nat} (hN : PlainShape A L g a b) (hS : PlainSegs A a b) :
    AbsSound A L g a b absMovImm := by
  intro env op outs t h ha hb ht
  cases op <;> simp only [absMovImm, reduceCtorEq] at h
  rename_i m
  rcases m with ⟨kind, ty, dsts, srcs⟩
  simp only at h
  split at h
  · rename_i k d x
    by_cases hr : ((MoveInstr.mk .scalar (.int k 32) [some d] [.f32imm x]).rule ==
        some RuleId.threadMove) = true
    · simp only [hr, ite_true] at h
      obtain rfl := Option.some.inj h
      simp only [beq_iff_eq] at hr
      have hex := execLocalA_plain hN hS ha hb
        (op := .move (MoveInstr.mk .scalar (.int k 32) [some d] [.f32imm x]))
        (.inr (.inl ⟨_, rfl⟩))
      rw [execLocal_move hr] at hex
      obtain ⟨y, hy⟩ : ∃ y, readValue L g t 32 (.f32imm x) = .ok (.bits 32 y) := ⟨_, rfl⟩
      have hex' : execMove L g t (.move (MoveInstr.mk .scalar (.int k 32) [some d] [.f32imm x])) =
          .ok (next (setReg t d (.bits 32 y))) := by
        simp [execMove, hy, Value.bytes, DType.width, bind, Except.bind, pure, Except.pure]
      rw [hex'] at hex
      obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .dat32) ⟨_, rfl, dat32_bits y⟩
      exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
    · simp [hr] at h
  · simp at h

/-- The family of `SegQFJ.lean` and the constant move. -/
def absF4 (env : EnvF) (op : Op) : Option (List (Nat × TagF)) :=
  (absF3 env op).or (absMovImm env op)

theorem absF4_sound {a b : Nat} (h : FloatPlain3 A L g a b) : AbsSound A L g a b absF4 :=
  (absF3_sound h).or (absMovImm_sound h.plain.plain.shape h.plain.plain.segs)

/-- A typed run of the family `absF4` whose abstract run writes exactly `W`. -/
theorem segQF4_runW (qt : Nat → EnvF) {a b : Nat} {F G : List (Nat × Value)} {W : List Nat}
    (hab : a ≤ b) (hlen : b ≤ K.code.length) (hP : FloatPlain3 A L g a b)
    (hc : checkW absF4 qt a b ((K.code.drop a).take (b - a)) W = true)
    (hw : ∀ p ∈ G, p.1 ∉ W) (hG : ∀ p ∈ G, p ∈ F) : SegQ K A L g (QTF qt) a F b G := by
  obtain ⟨h0, hW⟩ := checkW_sound hc
  exact segQF_of_typed qt (Ft := []) hab hlen (absF4_sound hP) trivial
    (checkF_gk h0 fun k hk => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
      exact hW ▸ hw p hp) hG

end PTX.Flow.TyG
