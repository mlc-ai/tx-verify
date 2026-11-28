-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedOpsG

@[expose] public section

/-! # The data-movement family of the float-tag engine

Unpacking a word into halves (`mov.b32 {lo, hi}, r`, `mov.b64 {lo, hi}, r`), packing two `.f32`
data into a 64-bit value (`mov.b64 r, {a, b}`) and `selp.f32` on `.f32` data. No assumption
takes these instructions (`PlainShape`: no local rule of the assumptions takes an integer, a move
or an integer conversion at the stretch's pcs), so the step is the Core rule's. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Flow.Havoc

/-- An integer, a move or an integer conversion. -/
def PlainOp (op : Op) : Prop :=
  (∃ i, op = .int i) ∨ (∃ m, op = .move m) ∨ (∃ c k w, op = .cvt c ∧ c.dst = .int k w)

/-- No local rule of an assumption takes an integer, a move or an integer conversion at a pc of
`[a, b)`. -/
def PlainShape (A : List Assumption) (L : Launch) (g a b : Nat) : Prop :=
  ∀ t : TState, a ≤ t.pc → t.pc < b → ∀ op, PlainOp op → ∀ x ∈ A, x.localRule L g t op = none

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem execLocalA_plain {a b : Nat} (hN : PlainShape A L g a b) (hS : PlainSegs A a b)
    {t : TState} (ha : a ≤ t.pc) (hb : t.pc < b) {op : Op} (hop : PlainOp op) :
    execLocalA A L g t op = execLocal L g t op :=
  execLocalA_noOverride (hN t ha hb op hop) (hS t.pc ha hb)

/-- A register of tag `.dat32`. -/
def d32 (env : EnvF) (r : Nat) : Bool := TagF.sat (env.lookup r) .dat32

theorem d32_ok {env : EnvF} {t : TState} {r : Nat} (h : d32 env r = true) (ht : TypedF env t) :
    ∃ x, t.regs r = some x ∧ Dat32 x :=
  TagF.sat_ok (v := t.regs r) (need := .dat32) h (fun tg e => ht r tg e)

theorem bits_dat32 {x : Value} (h : Dat32 x) : x.bytes = 4 := h.2.1

theorem regs_two (t : TState) (lo hi : Nat) (x y : Value) (r : Nat) :
    (setReg (setReg t lo x) hi y).regs r =
      if r = hi then some y else if r = lo then some x else t.regs r := by
  simp only [setReg, Function.update_apply]

/-! ### Unpack -/

/-- The tags the halves of an unpacked word get. -/
def unpackOuts (tg : Option TagF) (w lo hi : Nat) : Option (List (Nat × TagF)) :=
  match tg with
  | some (.old (.bits v)) =>
    if v == w then some [(lo, .old (.bits (w / 2))), (hi, .old (.bits (w / 2)))] else none
  | some .dat64 => if w == 64 then some [(lo, .dat32), (hi, .dat32)] else none
  | _ => none

/-- `mov.b<w> {lo, hi}, a` of a register of `w` bits, or of a 64-bit value of two data. -/
def absUnpack (env : EnvF) : Op → Option (List (Nat × TagF))
  | .move m =>
    match m.kind, m.ty, m.dsts, m.srcs with
    | .unpack, .int _ w, [some lo, some hi], [.reg a] =>
      if m.rule == some .threadMove then unpackOuts (env.lookup a) w lo hi else none
    | _, _, _, _ => none
  | _ => none

theorem exec_unpack {t : TState} {k : IType} {w lo hi a : Nat} {v : Value}
    (hv : t.regs a = some v) (hb : v.bytes = w / 8)
    (h1 : (splitValue w v).1.bytes = w / 16) (h2 : (splitValue w v).2.bytes = w / 16) :
    execMove L g t (.move ⟨.unpack, .int k w, [some lo, some hi], [.reg a]⟩) =
      .ok (next (setReg (setReg t lo (splitValue w v).1) hi (splitValue w v).2)) := by
  simp [execMove, readValue, readReg, hv, hb, h1, h2, DType.width, bind, Except.bind, pure,
    Except.pure]

/-- The two halves written: the other registers unchanged, both of the tag `tg`. -/
theorem wr2 {t : TState} {lo hi : Nat} {x y : Value} {tg : TagF} (hx : tg.ok (some x))
    (hy : tg.ok (some y)) :
    (∀ r, r ∉ [(lo, tg), (hi, tg)].map Prod.fst →
      (next (setReg (setReg t lo x) hi y)).regs r = t.regs r) ∧
    ∀ p ∈ [(lo, tg), (hi, tg)], p.2.ok ((next (setReg (setReg t lo x) hi y)).regs p.1) := by
  constructor
  · intro r hr
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    show (setReg (setReg t lo x) hi y).regs r = t.regs r
    rw [regs_two]
    simp [hr.1, hr.2]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    show p.2.ok ((setReg (setReg t lo x) hi y).regs p.1)
    rw [regs_two]
    rcases hp with rfl | rfl <;> dsimp only <;> split_ifs <;> simp_all

theorem dat64_split {x : Value} (h : Dat64 x) :
    x.bytes = 8 ∧ Dat32 (splitValue 64 x).1 ∧ Dat32 (splitValue 64 x).2 := by
  rcases h with ⟨y, rfl⟩ | ⟨lo, hi, rfl, h1, h2⟩
  · exact ⟨rfl, dat32_bits _, dat32_bits _⟩
  · exact ⟨by simp [Value.bytes, h1.2.1, h2.2.1], h1, h2⟩

theorem absUnpack_sound {a b : Nat} (hN : PlainShape A L g a b) (hS : PlainSegs A a b) :
    AbsSound A L g a b absUnpack := by
  intro env op outs t h ha hb ht
  cases op <;> simp only [absUnpack, reduceCtorEq] at h
  rename_i m
  rcases m with ⟨kind, ty, dsts, srcs⟩
  simp only at h
  split at h
  · rename_i k w lo hi r
    by_cases hr : ((MoveInstr.mk .unpack (.int k w) [some lo, some hi] [.reg r]).rule ==
        some RuleId.threadMove) = true
    · simp only [hr, ite_true] at h
      have hex := execLocalA_plain hN hS ha hb
        (op := .move (MoveInstr.mk .unpack (.int k w) [some lo, some hi] [.reg r]))
        (.inr (.inl ⟨_, rfl⟩))
      rw [execLocal_move (beq_iff_eq.mp hr)] at hex
      unfold unpackOuts at h
      split at h
      · rename_i v hl
        split_ifs at h with hv
        obtain rfl := Option.some.inj h
        obtain rfl : v = w := by simpa using hv
        obtain ⟨x, hx⟩ := ht r _ hl
        have hs : splitValue v (.bits v x) = (.bits (v / 2) (truncBits (v / 2) x),
            .bits (v / 2) (truncBits (v / 2) (BitVec.ofNat 64 (x.toNat / 2 ^ (v / 2))))) := rfl
        have hb1 : (Value.bits (v / 2) (truncBits (v / 2) x)).bytes = v / 16 := by
          simp only [Value.bytes]; omega
        have hb2 : (Value.bits (v / 2)
            (truncBits (v / 2) (BitVec.ofNat 64 (x.toNat / 2 ^ (v / 2))))).bytes = v / 16 := by
          simp only [Value.bytes]; omega
        have hex' := exec_unpack (L := L) (g := g) (t := t) (k := k) (lo := lo) (hi := hi)
          (w := v) (v := .bits v x) hx rfl (by rw [hs]; exact hb1)
          (by rw [hs]; exact hb2)
        rw [hex'] at hex
        obtain ⟨hw1, hw2⟩ := wr2 (t := t) (lo := lo) (hi := hi) (tg := .old (.bits (v / 2)))
          (x := (splitValue v (.bits v x)).1) (y := (splitValue v (.bits v x)).2)
          (by rw [hs]; exact ⟨_, rfl⟩) (by rw [hs]; exact ⟨_, rfl⟩)
        exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
      · rename_i hl
        split_ifs at h with hv
        obtain rfl := Option.some.inj h
        obtain rfl : w = 64 := by simpa using hv
        obtain ⟨x, hx, hd⟩ := ht r _ hl
        obtain ⟨hb8, hd1, hd2⟩ := dat64_split hd
        have hex' := exec_unpack (L := L) (g := g) (t := t) (k := k) (lo := lo) (hi := hi)
          (v := x) hx hb8 hd1.2.1 hd2.2.1
        rw [hex'] at hex
        obtain ⟨hw1, hw2⟩ := wr2 (t := t) (lo := lo) (hi := hi) (tg := .dat32)
          (x := (splitValue 64 x).1) (y := (splitValue 64 x).2) ⟨_, rfl, hd1⟩ ⟨_, rfl, hd2⟩
        exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
      · simp at h
    · simp [hr] at h
  · simp at h

/-! ### Pack -/

theorem dat64_join {x y : Value} (hx : Dat32 x) (hy : Dat32 y) : Dat64 (joinValue x y) := by
  unfold joinValue
  split
  · exact absurd rfl (hx.2.2 _ _ _)
  · rename_i w x' w' y'
    split_ifs with h
    · have hw : w = 32 := by
        have := hx.2.1
        simp only [Value.bytes] at this
        omega
      subst hw
      exact .inl ⟨_, rfl⟩
    · exact .inr ⟨_, _, rfl, hx, hy⟩
  · exact .inr ⟨_, _, rfl, hx, hy⟩

/-- `mov.b64 d, {a, b}` of two `.f32` data. -/
def absPack (env : EnvF) : Op → Option (List (Nat × TagF))
  | .move m =>
    match m.kind, m.ty, m.dsts, m.srcs with
    | .pack, .int _ 64, [some d], [.reg a, .reg b] =>
      if m.rule == some .threadMove && d32 env a && d32 env b then some [(d, .dat64)] else none
    | _, _, _, _ => none
  | _ => none

theorem exec_pack {t : TState} {k : IType} {d a b : Nat} {x y : Value}
    (hx : t.regs a = some x) (hy : t.regs b = some y) (h1 : x.bytes = 4) (h2 : y.bytes = 4) :
    execMove L g t (.move ⟨.pack, .int k 64, [some d], [.reg a, .reg b]⟩) =
      .ok (next (setReg t d (joinValue x y))) := by
  simp [execMove, readValue, readReg, hx, hy, h1, h2, DType.width, bind, Except.bind, pure,
    Except.pure]

theorem wr1 {t : TState} {d : Nat} {v : Value} {tg : TagF} (hv : tg.ok (some v)) :
    (∀ r, r ∉ [(d, tg)].map Prod.fst → (next (setReg t d v)).regs r = t.regs r) ∧
    ∀ p ∈ [(d, tg)], p.2.ok ((next (setReg t d v)).regs p.1) := by
  constructor
  · intro r hr
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
    simp [next, setReg, Function.update_of_ne hr]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    simpa [next, setReg] using hv

theorem absPack_sound {a b : Nat} (hN : PlainShape A L g a b) (hS : PlainSegs A a b) :
    AbsSound A L g a b absPack := by
  intro env op outs t h ha hb ht
  cases op <;> simp only [absPack, reduceCtorEq] at h
  rename_i m
  rcases m with ⟨kind, ty, dsts, srcs⟩
  simp only at h
  split at h
  · rename_i k d r1 r2
    by_cases hr : ((MoveInstr.mk .pack (.int k 64) [some d] [.reg r1, .reg r2]).rule ==
        some RuleId.threadMove && d32 env r1 && d32 env r2) = true
    · simp only [hr, ite_true] at h
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true] at hr
      obtain ⟨⟨hr0, h1⟩, h2⟩ := hr
      have hex := execLocalA_plain hN hS ha hb
        (op := .move (MoveInstr.mk .pack (.int k 64) [some d] [.reg r1, .reg r2]))
        (.inr (.inl ⟨_, rfl⟩))
      rw [execLocal_move (beq_iff_eq.mp hr0)] at hex
      obtain ⟨x, hx, hdx⟩ := d32_ok h1 ht
      obtain ⟨y, hy, hdy⟩ := d32_ok h2 ht
      rw [exec_pack hx hy hdx.2.1 hdy.2.1] at hex
      obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .dat64) ⟨_, rfl, dat64_join hdx hdy⟩
      exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
    · simp [hr] at h
  · simp at h

/-! ### `selp.f32` -/

/-- A `selp.f32` source: a register of `.f32` data or a `0f` constant. -/
def selSrc (env : EnvF) : Opnd → Bool
  | .reg r => d32 env r
  | .f32imm _ => true
  | _ => false

/-- `selp.f32 d, a, b, p`. -/
def absSelp (env : EnvF) : Op → Option (List (Nat × TagF))
  | .int i =>
    match i.op, i.ty, i.sat, i.dsts, i.srcs with
    | .selp, .float .f32, false, [some d], [a, b, .reg p] =>
      if i.rule == some .threadMove && selSrc env a && selSrc env b &&
          env.lookup p == some (.old .pred) then some [(d, .dat32)] else none
    | _, _, _, _, _ => none
  | _ => none

theorem selSrc_read {env : EnvF} {t : TState} {o : Opnd} (h : selSrc env o = true)
    (ht : TypedF env t) : ∃ v, readValue L g t 32 o = .ok v ∧ Dat32 v := by
  cases o <;> simp only [selSrc, Bool.false_eq_true] at h
  · rename_i r
    obtain ⟨x, hx, hd⟩ := d32_ok h ht
    exact ⟨x, by simp [readValue, readReg, hx, pure, Except.pure], hd⟩
  · exact ⟨_, rfl, dat32_bits _⟩

theorem absSelp_sound {a b : Nat} (hN : PlainShape A L g a b) (hS : PlainSegs A a b) :
    AbsSound A L g a b absSelp := by
  intro env op outs t h ha hb ht
  cases op <;> simp only [absSelp, reduceCtorEq] at h
  rename_i i
  rcases i with ⟨iop, ty, sat, dsts, srcs⟩
  simp only at h
  split at h
  · rename_i d o1 o2 p
    by_cases hr : ((IntInstr.mk .selp (.float .f32) false [some d] [o1, o2, .reg p]).rule ==
        some RuleId.threadMove && selSrc env o1 && selSrc env o2 &&
        env.lookup p == some (.old .pred)) = true
    · simp only [hr, ite_true] at h
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq] at hr
      obtain ⟨⟨⟨hr0, h1⟩, h2⟩, h3⟩ := hr
      have hex := execLocalA_plain hN hS ha hb
        (op := .int (IntInstr.mk .selp (.float .f32) false [some d] [o1, o2, .reg p]))
        (.inl ⟨_, rfl⟩)
      rw [execLocal_selp hr0] at hex
      obtain ⟨x, hx, hdx⟩ := selSrc_read (L := L) (g := g) h1 ht
      obtain ⟨y, hy, hdy⟩ := selSrc_read (L := L) (g := g) h2 ht
      obtain ⟨q, hq⟩ := ht p _ h3
      have hex' : execMove L g t (.int (IntInstr.mk .selp (.float .f32) false [some d]
          [o1, o2, .reg p])) = .ok (next (setReg t d (if q then x else y))) := by
        cases q <;> simp [execMove, readReg, hq, hx, hy, hdx.2.1, hdy.2.1, DType.width, bind,
          Except.bind, pure, Except.pure]
      rw [hex'] at hex
      have hv : Dat32 (if q then x else y) := by split_ifs <;> assumption
      obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .dat32) ⟨_, rfl, hv⟩
      exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
    · simp [hr] at h
  · simp at h

/-! ### Packing bit patterns -/

/-- `mov.b<w> d, {a, b}` of two registers of `w / 2` bits. -/
def absPackB (env : EnvF) : Op → Option (List (Nat × TagF))
  | .move m =>
    match m.kind, m.ty, m.dsts, m.srcs with
    | .pack, .int _ w, [some d], [.reg a, .reg b] =>
      if m.rule == some .threadMove && w % 2 == 0 && w ≤ 64 &&
          env.lookup a == some (.old (.bits (w / 2))) &&
          env.lookup b == some (.old (.bits (w / 2))) then some [(d, .old (.bits w))] else none
    | _, _, _, _ => none
  | _ => none

theorem exec_packB {t : TState} {k : IType} {w d a b : Nat} {x y : BitVec 64}
    (hx : t.regs a = some (.bits (w / 2) x)) (hy : t.regs b = some (.bits (w / 2) y))
    (h2 : w % 2 = 0) (h64 : w ≤ 64) :
    execMove L g t (.move ⟨.pack, .int k w, [some d], [.reg a, .reg b]⟩) =
      .ok (next (setReg t d (.bits w (x ||| (y <<< (w / 2)))))) := by
  have hw : 2 * (w / 2) = w := by omega
  simp [execMove, readValue, readReg, hx, hy, DType.width, Value.bytes, joinValue, hw, h64,
    bind, Except.bind, pure, Except.pure]
  omega

theorem absPackB_sound {a b : Nat} (hN : PlainShape A L g a b) (hS : PlainSegs A a b) :
    AbsSound A L g a b absPackB := by
  intro env op outs t h ha hb ht
  cases op <;> simp only [absPackB, reduceCtorEq] at h
  rename_i m
  rcases m with ⟨kind, ty, dsts, srcs⟩
  simp only at h
  split at h
  · rename_i k w d r1 r2
    by_cases hr : ((MoveInstr.mk .pack (.int k w) [some d] [.reg r1, .reg r2]).rule ==
        some RuleId.threadMove && w % 2 == 0 && w ≤ 64 &&
        env.lookup r1 == some (.old (.bits (w / 2))) &&
        env.lookup r2 == some (.old (.bits (w / 2)))) = true
    · simp only [hr, ite_true] at h
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
      obtain ⟨⟨⟨⟨hr0, h2⟩, h64⟩, h1⟩, h3⟩ := hr
      have hex := execLocalA_plain hN hS ha hb
        (op := .move (MoveInstr.mk .pack (.int k w) [some d] [.reg r1, .reg r2]))
        (.inr (.inl ⟨_, rfl⟩))
      rw [execLocal_move hr0] at hex
      obtain ⟨x, hx⟩ := ht r1 _ h1
      obtain ⟨y, hy⟩ := ht r2 _ h3
      rw [exec_packB hx hy h2 h64] at hex
      obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .old (.bits w)) ⟨_, rfl⟩
      exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
    · simp [hr] at h
  · simp at h

/-! ### `mov.pred` -/

/-- `mov.pred d, a` of a predicate. -/
def absMovePred (env : EnvF) : Op → Option (List (Nat × TagF))
  | .move m =>
    match m.kind, m.ty, m.dsts, m.srcs with
    | .scalar, .pred, [some d], [.reg a] =>
      if m.rule == some .threadMove && env.lookup a == some (.old .pred) then
        some [(d, .old .pred)] else none
    | _, _, _, _ => none
  | _ => none

theorem absMovePred_sound {a b : Nat} (hN : PlainShape A L g a b) (hS : PlainSegs A a b) :
    AbsSound A L g a b absMovePred := by
  intro env op outs t h ha hb ht
  cases op <;> simp only [absMovePred, reduceCtorEq] at h
  rename_i m
  rcases m with ⟨kind, ty, dsts, srcs⟩
  simp only at h
  split at h
  · rename_i d r
    by_cases hr : ((MoveInstr.mk .scalar .pred [some d] [.reg r]).rule ==
        some RuleId.threadMove && env.lookup r == some (.old .pred)) = true
    · simp only [hr, ite_true] at h
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq] at hr
      obtain ⟨hr0, h1⟩ := hr
      have hex := execLocalA_plain hN hS ha hb
        (op := .move (MoveInstr.mk .scalar .pred [some d] [.reg r])) (.inr (.inl ⟨_, rfl⟩))
      rw [execLocal_move hr0] at hex
      obtain ⟨q, hq⟩ := ht r _ h1
      have hex' : execMove L g t (.move (MoveInstr.mk .scalar .pred [some d] [.reg r])) =
          .ok (next (setReg t d (.pred q))) := by
        simp [execMove, readPred, readReg, hq, bind, Except.bind, pure, Except.pure]
      rw [hex'] at hex
      obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .old .pred) ⟨q, rfl⟩
      exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
    · simp [hr] at h
  · simp at h

/-- The data-movement family: unpack, pack, `selp.f32` and `mov.pred`. -/
def absMoveF (env : EnvF) (op : Op) : Option (List (Nat × TagF)) :=
  (absUnpack env op).or ((absPackB env op).or ((absPack env op).or
    ((absSelp env op).or (absMovePred env op))))

theorem absMoveF_sound {a b : Nat} (hN : PlainShape A L g a b) (hS : PlainSegs A a b) :
    AbsSound A L g a b absMoveF :=
  (absUnpack_sound hN hS).or ((absPackB_sound hN hS).or ((absPack_sound hN hS).or
    ((absSelp_sound hN hS).or (absMovePred_sound hN hS))))

end PTX.Flow.TyG
