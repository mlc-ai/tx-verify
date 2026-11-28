-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedMovImmG

@[expose] public section

/-! # `mad.wide`, `bfe`, `not` and `mov.pred` of a constant

Integer instructions whose `execInt` arm only reads its sources as bit patterns (`readBits`) and
writes a bit pattern of the width of its result: `mad.wide` (two sources of the width and an
accumulator of twice the width), `bfe`, the bitwise `not`. A constant `mov.pred` writes a
predicate. `absF5` is `absF4` with these rules, `segQF5_runW` the typed run of it. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The width of the bit pattern of an old tag. -/
def bitsW : Option TagF → Option Nat
  | some (.old (.bits w)) | some (.old (.nz w)) => some w
  | _ => none

/-- A source read as a bit pattern: a constant or a register of bits. -/
def rbG (env : EnvF) : Opnd → Bool
  | .imm _ => true
  | .reg r => (bitsW (env.lookup r)).isSome
  | _ => false

/-- A source read as exactly `w` bits. -/
def rwG (env : EnvF) (w : Nat) : Opnd → Bool
  | .imm _ => true
  | .reg r => (bitsW (env.lookup r)) == some w
  | _ => false

theorem readBits_rbG {env : EnvF} {t : TState} {o : Opnd} (h : rbG env o = true)
    (ht : TypedF env t) (w : Nat) : ∃ x, readBits L g t w o = .ok x := by
  cases o with
  | imm v => exact ⟨_, rfl⟩
  | reg r =>
    simp only [rbG] at h
    cases hl : env.lookup r with
    | none => simp [hl, bitsW] at h
    | some tg =>
      have hk := ht r tg hl
      rw [hl] at h
      rcases tg with (_ | _ | _ | _) | _ | _ <;> simp [bitsW] at h hk
      · obtain ⟨x, hx⟩ := hk
        exact ⟨truncBits w x, by simp [readBits, readReg, hx, pure, Except.pure, bind, Except.bind]⟩
      · obtain ⟨x, hx, -⟩ := hk
        exact ⟨truncBits w x, by simp [readBits, readReg, hx, pure, Except.pure, bind, Except.bind]⟩
  | _ => simp [rbG] at h

/-- The write of one register with a value of the tag, as `AbsSound` states it. -/
theorem absStep {a b : Nat} {t : TState} {op : Op} {d : Nat} {v : Value} {tg : TagF}
    (hN : PlainShape A L g a b) (hS : PlainSegs A a b) (ha : a ≤ t.pc) (hb : t.pc < b)
    (hop : PlainOp op) (hex : execLocal L g t op = .ok (next (setReg t d v)))
    (hv : tg.ok (some v)) :
    ∃ u, execLocalA A L g t op = .ok u ∧
      u.pc = t.pc + 1 ∧ u.sub = t.sub ∧ u.acc = t.acc ∧ u.fault = t.fault ∧
      (∀ r, r ∉ [(d, tg)].map Prod.fst → u.regs r = t.regs r) ∧
      ∀ p ∈ [(d, tg)], p.2.ok (u.regs p.1) :=
  have ⟨hw1, hw2⟩ := wr1 (t := t) hv
  ⟨_, (execLocalA_plain hN hS ha hb hop).trans hex, rfl, rfl, rfl, rfl, hw1, hw2⟩

theorem absBits {a b : Nat} {t : TState} {i : IntInstr} {d w : Nat}
    (hN : PlainShape A L g a b) (hS : PlainSegs A a b) (ha : a ≤ t.pc) (hb : t.pc < b)
    (hr : i.rule = some .threadInt)
    (h : ∃ r, execInt L g t i = .ok (next (setReg t d (.bits w r)))) :
    ∃ u, execLocalA A L g t (.int i) = .ok u ∧
      u.pc = t.pc + 1 ∧ u.sub = t.sub ∧ u.acc = t.acc ∧ u.fault = t.fault ∧
      (∀ r, r ∉ [(d, TagF.old (.bits w))].map Prod.fst → u.regs r = t.regs r) ∧
      ∀ p ∈ [(d, TagF.old (.bits w))], p.2.ok (u.regs p.1) :=
  have ⟨_, hv, hok⟩ := fin_bits hr h
  absStep hN hS ha hb (.inl ⟨_, rfl⟩) hv hok

/-- `mad.wide`, `bfe` and `not` of bit patterns. -/
def absIntX (env : EnvF) : Op → Option (List (Nat × TagF))
  | .int i =>
    match i.op, i.ty, i.sat, i.dsts, i.srcs with
    | .mad .wide, .int _ w, false, [some d], [a, b, c] =>
      if i.rule == some .threadInt && rbG env a && rbG env b && rwG env (2 * w) c then
        some [(d, .old (.bits (2 * w)))] else none
    | .bfe, .int _ w, false, [some d], [a, b, c] =>
      if i.rule == some .threadInt && rbG env a && rbG env b && rbG env c then
        some [(d, .old (.bits w))] else none
    | .not, .int _ w, false, [some d], [a] =>
      if i.rule == some .threadInt && w != 1 && rbG env a then
        some [(d, .old (.bits w))] else none
    | _, _, _, _, _ => none
  | _ => none

theorem absIntX_sound {a b : Nat} (hN : PlainShape A L g a b) (hS : PlainSegs A a b) :
    AbsSound A L g a b absIntX := by
  intro env op outs t h ha hb ht
  cases op <;> simp only [absIntX, reduceCtorEq] at h
  rename_i i
  rcases i with ⟨iop, ty, sat, dsts, srcs⟩
  simp only at h
  split at h
  · rename_i k w d x y z
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨hr, h1⟩, h2⟩, h3⟩ := hc
    obtain ⟨p, hp⟩ := readBits_rbG (L := L) (g := g) h1 ht w
    obtain ⟨q, hq⟩ := readBits_rbG (L := L) (g := g) h2 ht w
    obtain ⟨s, hs⟩ := readBits_rbG (L := L) (g := g) (o := z) (by
      cases z <;> simp_all [rwG, rbG]) ht (2 * w)
    refine absBits hN hS ha hb hr ?_
    simp [execInt, intResult, hp, hq, hs, DType.width, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩
  · rename_i k w d x y z
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨hr, h1⟩, h2⟩, h3⟩ := hc
    obtain ⟨p, hp⟩ := readBits_rbG (L := L) (g := g) h1 ht w
    obtain ⟨q, hq⟩ := readBits_rbG (L := L) (g := g) h2 ht 32
    obtain ⟨s, hs⟩ := readBits_rbG (L := L) (g := g) h3 ht 32
    refine absBits hN hS ha hb hr ?_
    simp [execInt, intResult, hp, hq, hs, DType.width, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩
  · rename_i k w d x
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨hr, hw⟩, h1⟩ := hc
    obtain ⟨p, hp⟩ := readBits_rbG (L := L) (g := g) h1 ht w
    refine absBits hN hS ha hb hr ?_
    simp [execInt, hp, hw, DType.width, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩
  · simp at h

/-- `mov.pred d, imm`. -/
def absPredImm (_ : EnvF) : Op → Option (List (Nat × TagF))
  | .move m =>
    match m.kind, m.ty, m.dsts, m.srcs with
    | .scalar, .pred, [some d], [.imm _] =>
      if m.rule == some .threadMove then some [(d, .old .pred)] else none
    | _, _, _, _ => none
  | _ => none

theorem absPredImm_sound {a b : Nat} (hN : PlainShape A L g a b) (hS : PlainSegs A a b) :
    AbsSound A L g a b absPredImm := by
  intro env op outs t h ha hb ht
  cases op <;> simp only [absPredImm, reduceCtorEq] at h
  rename_i m
  rcases m with ⟨kind, ty, dsts, srcs⟩
  simp only at h
  split at h
  · rename_i d v
    split_ifs at h with hr
    obtain rfl := Option.some.inj h
    simp only [beq_iff_eq] at hr
    refine absStep hN hS ha hb (.inr (.inl ⟨_, rfl⟩)) ?_ (tg := .old .pred) ⟨decide (v ≠ 0), rfl⟩
    rw [execLocal_move hr]
    simp [execMove, readPred, bind, Except.bind, pure, Except.pure]
  · simp at h

/-- The special registers of a launch coordinate (`%tid.x`, `%ctaid.z`, ...). -/
def sregOk : SReg → Bool
  | ⟨.tid, some _⟩ | ⟨.ctaid, some _⟩ => true
  | _ => false

/-- `mov.<int> d, %tid.x` and `%ctaid.x`: the special register is a number, so the move writes a
bit pattern. -/
def absMovSreg (_ : EnvF) : Op → Option (List (Nat × TagF))
  | .move m =>
    match m.kind, m.ty, m.dsts, m.srcs with
    | .scalar, .int _ w, [some d], [.sreg s] =>
      if m.rule == some .threadMove && sregOk s then some [(d, .old (.bits w))] else none
    | _, _, _, _ => none
  | _ => none

theorem absMovSreg_sound {a b : Nat} (hN : PlainShape A L g a b) (hS : PlainSegs A a b) :
    AbsSound A L g a b absMovSreg := by
  intro env op outs t h ha hb ht
  cases op <;> simp only [absMovSreg, reduceCtorEq] at h
  rename_i m
  rcases m with ⟨kind, ty, dsts, srcs⟩
  simp only at h
  split at h
  · rename_i k w d s
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hr, hs⟩ := hc
    obtain ⟨v, hv, hw⟩ : ∃ v, sregValue L g s = some v ∧ s.width = 32 := by
      rcases s with ⟨n, dm⟩
      cases n <;> cases dm <;> simp [sregOk, sregValue, SReg.width] at hs ⊢
    obtain ⟨r, hx⟩ : ∃ r, execMove L g t (.move (MoveInstr.mk .scalar (.int k w) [some d]
        [.sreg s])) = .ok (next (setReg t d (.bits w r))) := by
      simp [execMove, readValue, hw, readBits, hv, bind, Except.bind, pure, Except.pure,
        DType.width, Value.bytes]
      exact ⟨_, rfl⟩
    refine absStep hN hS ha hb (.inr (.inl ⟨_, rfl⟩)) ?_ (tg := .old (.bits w)) ⟨r, rfl⟩
    rw [execLocal_move hr]
    exact hx
  · simp at h

/-- The family of `TypedMovImmG.lean` with the rules of this file. -/
def absF5 (env : EnvF) (op : Op) : Option (List (Nat × TagF)) :=
  (absF4 env op).or ((absIntX env op).or ((absPredImm env op).or (absMovSreg env op)))

theorem absF5_sound {a b : Nat} (h : FloatPlain3 A L g a b) : AbsSound A L g a b absF5 :=
  (absF4_sound h).or ((absIntX_sound h.plain.plain.shape h.plain.plain.segs).or
    ((absPredImm_sound h.plain.plain.shape h.plain.plain.segs).or
      (absMovSreg_sound h.plain.plain.shape h.plain.plain.segs)))

/-- A typed run of the family `absF5` whose abstract run writes exactly `W`. -/
theorem segQF5_runW (qt : Nat → EnvF) {a b : Nat} {F G : List (Nat × Value)} {W : List Nat}
    (hab : a ≤ b) (hlen : b ≤ K.code.length) (hP : FloatPlain3 A L g a b)
    (hc : checkW absF5 qt a b ((K.code.drop a).take (b - a)) W = true)
    (hw : ∀ p ∈ G, p.1 ∉ W) (hG : ∀ p ∈ G, p ∈ F) : SegQ K A L g (QTF qt) a F b G := by
  obtain ⟨h0, hW⟩ := checkW_sound hc
  exact segQF_of_typed qt (Ft := []) hab hlen (absF5_sound hP) trivial
    (checkF_gk h0 fun k hk => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
      exact hW ▸ hw p hp) hG

end PTX.Flow.TyG
