-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxReadings
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxReads

@[expose] public section

/-! # Accepting an outcome run by its operand shapes

A proof tool for the softmax machine's conditions (`oCond`, `chainCond`). A run is accepted
when every register it reads holds a value of a known shape: a single-precision number (`f32`,
`num`, a 32-bit word `sbits`), a pair of half-precision numbers (`h2`), a pair of two such values
(`pr`), a predicate. `oTyVals` computes the shapes an item writes, or fails when the item's
condition does not follow from the shapes (each floating instruction on numbers has the ideal
outcome: `mulE_fin`, `fma2E_fin`, …); `chainTy` runs the pieces. When the shape check succeeds
(decided on concrete shapes) and the values have the shapes, the run is accepted
(`chainCond_of_chainTy`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A shape of a register value. -/
inductive OTy where
  | f32 | sbits | num | h2 | pr (a b : OTy) | pred | any
  deriving DecidableEq

/-- A value of a shape. -/
def OTy.Has : OTy → Value → Prop
  | .f32, v => ∃ x, v = .float .f32 x
  | .sbits, v => (∃ b : BitVec 64, v = .bits 32 b ∧ b.toNat < 2 ^ 32) ∧
      ∃ x, valFloat .f32 v = .ok x
  | .num, v => ∃ x, valFloat .f32 v = .ok x
  | .h2, v => ∃ x y, v = .pair (.float .f16 x) (.float .f16 y)
  | .pr a b, v => v.bytes = 8 ∧ a.Has (splitValue 64 v).1 ∧ b.Has (splitValue 64 v).2
  | .pred, v => ∃ b, v = .pred b
  | .any, _ => True

/-- A shape whose values read as single-precision numbers. -/
def OTy.isNum : OTy → Bool
  | .f32 | .sbits | .num => true
  | _ => false

/-- A shape whose values have four bytes. -/
def OTy.leaf4 : OTy → Bool
  | .f32 | .sbits | .num | .h2 => true
  | _ => false

/-- A shape whose values are neither words nor slices. -/
def OTy.nonBits : OTy → Bool
  | .f32 | .h2 => true
  | _ => false

/-- A pair of numbers. -/
def OTy.pairNum : OTy → Bool
  | .pr a b => a.isNum && b.isNum
  | _ => false

theorem OTy.num_of {s : OTy} {v : Value} (hs : s.isNum = true) (h : s.Has v) :
    ∃ x, valFloat .f32 v = .ok x := by
  cases s <;> simp only [OTy.isNum, reduceCtorEq] at hs
  · obtain ⟨x, rfl⟩ := h
    exact ⟨x, valFloat_float⟩
  · exact h.2
  · exact h

theorem OTy.bytes4 {s : OTy} {v : Value} (hs : s.leaf4 = true) (h : s.Has v) : v.bytes = 4 := by
  cases s <;> simp only [OTy.leaf4, reduceCtorEq] at hs
  · obtain ⟨x, rfl⟩ := h
    rfl
  · obtain ⟨⟨b, rfl, -⟩, -⟩ := h
    rfl
  · obtain ⟨x, hx⟩ := h
    exact valFloat_bytes hx
  · obtain ⟨x, y, rfl⟩ := h
    rfl

theorem OTy.join_pair {s : OTy} {a b : Value} (hs : s.nonBits = true) (h : s.Has a) :
    joinValue a b = .pair a b := by
  cases s <;> simp only [OTy.nonBits, reduceCtorEq] at hs
  · obtain ⟨x, rfl⟩ := h
    cases b <;> rfl
  · obtain ⟨x, y, rfl⟩ := h
    cases b <;> rfl

theorem OTy.join_pair' {s : OTy} {a b : Value} (hs : s.nonBits = true) (h : s.Has b) :
    joinValue a b = .pair a b := by
  cases s <;> simp only [OTy.nonBits, reduceCtorEq] at hs
  · obtain ⟨x, rfl⟩ := h
    cases a with
    | slice w o n => cases o <;> rfl
    | _ => rfl
  · obtain ⟨x, y, rfl⟩ := h
    cases a with
    | slice w o n => cases o <;> rfl
    | _ => rfl

/-- The pair of a 32-bit word with itself splits into it. -/
theorem join_self_bits {b : BitVec 64} (hb : b.toNat < 2 ^ 32) :
    splitValue 64 (joinValue (.bits 32 b) (.bits 32 b)) = (.bits 32 b, .bits 32 b) ∧
      (joinValue (.bits 32 b) (.bits 32 b)).bytes = 8 := by
  simp only [joinValue, splitValue, truncBits, and_self, show 2 * 32 ≤ 64 by norm_num,
    ↓reduceIte, Prod.mk.injEq, Value.bits.injEq, true_and, Value.bytes]
  refine ⟨?_, by norm_num⟩
  have key : b ||| b <<< 32 = BitVec.ofNat 64 (b.toNat * 2 ^ 32 + b.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
      Nat.or_comm, lor_eq_add (k := 32) (by omega) hb]
    omega
  have hX : b.toNat * 4294967296 + b.toNat < 18446744073709551616 := by omega
  have h1 : (b.toNat * 4294967296 + b.toNat) % 4294967296 = b.toNat := by
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hb
  have h2 : (b.toNat * 4294967296 + b.toNat) / 4294967296 = b.toNat := by
    rw [Nat.mul_comm, Nat.mul_add_div (by norm_num)]; omega
  have h3 : b.toNat % 18446744073709551616 = b.toNat := Nat.mod_eq_of_lt (by omega)
  have h4 : b.toNat % 4294967296 = b.toNat := Nat.mod_eq_of_lt (by omega)
  rw [key]
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_ofNat, Nat.reduceDiv, Nat.reducePow, Nat.mod_eq_of_lt hX, h1, h2,
      h3, h4]

/-! ### Constants -/

/-- The `0f` constants read as numbers: `+0` and `1`. -/
def goodK (k : Nat) : Bool := k == 0 || k == 1065353216

/-- The comparison constants: `-∞` and `-8`. -/
def setpK (k : Nat) : Bool := k == 4286578688 || k == 3238002688

theorem goodK_has {k : Nat} (h : goodK k = true) :
    OTy.sbits.Has (.bits 32 (BitVec.ofNat 64 k)) := by
  simp only [goodK, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl
  · exact ⟨⟨_, rfl, by decide⟩, _, valFloat_zero⟩
  · exact ⟨⟨_, rfl, by decide⟩, _, valFloat_one⟩

theorem setpK_read {k : Nat} (h : setpK k = true) :
    ∃ e, Assumption.readEReal .f32 (.bits 32 (BitVec.ofNat 64 k)) = some (.ok e) := by
  simp only [setpK, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl
  · exact ⟨⊥, rfl⟩
  · exact ⟨_, readEReal_of_valFloat neg8⟩

/-! ### Items -/

/-- The shape of a register or `0f` operand. -/
def opTy (T : Nat → OTy) : Opnd → Option OTy
  | .reg r => some (T r)
  | .f32imm k => if goodK k then some .sbits else none
  | _ => none

/-- The shapes an item writes, or `none` when its condition does not follow from the shapes. -/
def oTyVals (T : Nat → OTy) : OItem → Option (List (Nat × OTy))
  | .movImm d b => if goodK b then some [(d, .sbits)] else none
  | .mov d a => if (T a).leaf4 then some [(d, T a)] else none
  | .pack d a b =>
    if (T a).leaf4 && (T b).leaf4 && ((T a).nonBits || (T b).nonBits) then
      some [(d, .pr (T a) (T b))]
    else if a == b && T a == .sbits then some [(d, .pr .sbits .sbits)] else none
  | .unpack lo hi a => match T a with
    | .pr s u => if s.leaf4 && u.leaf4 then some [(lo, s), (hi, u)] else none
    | _ => none
  | .fma2 d a b c =>
    if (T a).pairNum && (T b).pairNum && (T c).pairNum then some [(d, .pr .f32 .f32)] else none
  | .add2 d a b => if (T a).pairNum && (T b).pairNum then some [(d, .pr .f32 .f32)] else none
  | .ex2 _ d a => if (T a).isNum then some [(d, .f32)] else none
  | .cvt d a b => if (T a).isNum && (T b).isNum then some [(d, .h2)] else none
  | .mul _ d a b => if (T a).isNum && (T b).isNum then some [(d, .f32)] else none
  | .sub _ d a b => if (T a).isNum && (T b).isNum then some [(d, .f32)] else none
  | .add _ d a b => if (T a).isNum && (T b).isNum then some [(d, .f32)] else none
  | .selp d a b p => match T p, opTy T a, opTy T b with
    | .pred, some sa, some sb =>
      if sa == sb && sa.leaf4 then some [(d, sa)]
      else if sa.isNum && sb.isNum then some [(d, .num)] else none
    | _, _, _ => none
  | .setp c _ p a k =>
    if (T a).isNum && setpK k && (fcmpBase c).isSome then some [(p, .pred)] else none

/-- Values of shapes `T`. -/
def OTy.All (T : Nat → OTy) (V : Nat → Value) : Prop := ∀ r, (T r).Has (V r)

/-- The shapes after writing `tys`. -/
def tyUpdO (T : Nat → OTy) (tys : List (Nat × OTy)) : Nat → OTy :=
  tys.foldl (fun (T : Nat → OTy) (p : Nat × OTy) => Function.update T p.1 p.2) T

theorem OTy.All.upd : ∀ {T : Nat → OTy} {V : Nat → Value} {tys : List (Nat × OTy)}
    {vs : List (Nat × Value)}, OTy.All T V →
    List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2.Has q.2) tys vs →
    OTy.All (tyUpdO T tys)
      (vs.foldl (fun (V : Nat → Value) (p : Nat × Value) => Function.update V p.1 p.2) V)
  | _, _, [], [], h, .nil => h
  | T, V, p :: tys, q :: vs, h, .cons hpq hr => by
    obtain ⟨h1, h2⟩ := hpq
    simp only [tyUpdO, List.foldl_cons]
    refine OTy.All.upd (T := Function.update T p.1 p.2) (V := Function.update V q.1 q.2)
      (fun r => ?_) hr
    by_cases hr : r = p.1
    · subst hr
      rw [Function.update_self, h1, Function.update_self]
      exact h2
    · rw [Function.update_of_ne hr, Function.update_of_ne (h1 ▸ hr)]
      exact h r

theorem opTy_has {T : Nat → OTy} {V : Nat → Value} (h : OTy.All T V) {o : Opnd} {s : OTy}
    (ho : opTy T o = some s) : s.Has (opndVal V o) := by
  cases o with
  | reg r =>
    simp only [opTy, Option.some.injEq] at ho
    subst ho
    exact h r
  | f32imm k =>
    simp only [opTy] at ho
    split_ifs at ho with hk
    simp only [Option.some.injEq] at ho
    subst ho
    exact goodK_has hk
  | _ => simp [opTy] at ho

theorem pairNum_read {s : OTy} {v : Value} (hs : s.pairNum = true) (h : s.Has v) :
    (∃ x, valFloat .f32 (splitValue 64 v).1 = .ok x) ∧
      ∃ y, valFloat .f32 (splitValue 64 v).2 = .ok y := by
  cases s with
  | pr a b =>
    simp only [OTy.pairNum, Bool.and_eq_true] at hs
    exact ⟨OTy.num_of hs.1 h.2.1, OTy.num_of hs.2 h.2.2⟩
  | _ => simp [OTy.pairNum] at hs

theorem has_pair_f32 (x y : ℝ) : (OTy.pr .f32 .f32).Has (.pair (.float .f32 x) (.float .f32 y)) :=
  ⟨rfl, ⟨x, rfl⟩, ⟨y, rfl⟩⟩

theorem setpE_ok {c : FCmp} {fz : Bool} {va vb : Value} {x y : EReal}
    (hc : (fcmpBase c).isSome = true) (hx : Assumption.readEReal .f32 va = some (.ok x))
    (hy : Assumption.readEReal .f32 vb = some (.ok y)) : ∃ r, setpE c fz va vb = .ok r := by
  obtain ⟨cmp, hcmp⟩ := Option.isSome_iff_exists.mp hc
  exact ⟨Assumption.erealCompare cmp x y, by simp only [setpE, idealSetp, hcmp, hx, hy,
    Assumption.bindRead, pure, Except.pure]⟩

/-- **An item whose shape check succeeds** accepts its operands and writes values of the
shapes. -/
theorem oTyVals_sound {T : Nat → OTy} {V : Nat → Value} (h : OTy.All T V) {it : OItem}
    {tys : List (Nat × OTy)} (ht : oTyVals T it = some tys) :
    it.cond V ∧ List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2.Has q.2) tys (it.vals V) := by
  cases it with
  | movImm d b =>
    simp only [oTyVals] at ht
    split_ifs at ht with hk
    obtain rfl := Option.some.inj ht
    exact ⟨trivial, .cons ⟨rfl, goodK_has hk⟩ .nil⟩
  | mov d a =>
    simp only [oTyVals] at ht
    split_ifs at ht with hk
    obtain rfl := Option.some.inj ht
    exact ⟨OTy.bytes4 hk (h a), .cons ⟨rfl, h a⟩ .nil⟩
  | pack d a b =>
    simp only [oTyVals] at ht
    split_ifs at ht with h1 h2
    · obtain rfl := Option.some.inj ht
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
      obtain ⟨⟨ha, hb⟩, hn⟩ := h1
      have hb4 := OTy.bytes4 hb (h b)
      have ha4 := OTy.bytes4 ha (h a)
      have hj : joinValue (V a) (V b) = .pair (V a) (V b) := by
        rcases hn with hn | hn
        · exact OTy.join_pair hn (h a)
        · exact OTy.join_pair' hn (h b)
      refine ⟨⟨ha4, hb4⟩, .cons ⟨rfl, ?_⟩ .nil⟩
      show (OTy.pr (T a) (T b)).Has (joinValue (V a) (V b))
      rw [hj]
      refine ⟨?_, h a, h b⟩
      simp only [Value.bytes, ha4, hb4]
    · obtain rfl := Option.some.inj ht
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨rfl, hs⟩ := h2
      have hv := h a
      rw [hs] at hv
      obtain ⟨⟨bb, hbb, hlt⟩, hx⟩ := hv
      obtain ⟨hsp, hby⟩ := join_self_bits hlt
      refine ⟨⟨by rw [hbb]; rfl, by rw [hbb]; rfl⟩, .cons ⟨rfl, ?_⟩ .nil⟩
      show (OTy.pr .sbits .sbits).Has (joinValue (V a) (V a))
      rw [hbb]
      refine ⟨hby, ?_, ?_⟩ <;> rw [hsp] <;> exact ⟨⟨bb, rfl, hlt⟩, hbb ▸ hx⟩
  | unpack lo hi a =>
    simp only [oTyVals] at ht
    split at ht
    · rename_i s u hT
      split_ifs at ht with hk
      obtain rfl := Option.some.inj ht
      simp only [Bool.and_eq_true] at hk
      have hv := h a
      rw [hT] at hv
      obtain ⟨h8, hs, hu⟩ := hv
      exact ⟨⟨h8, OTy.bytes4 hk.1 hs, OTy.bytes4 hk.2 hu⟩,
        .cons ⟨rfl, hs⟩ (.cons ⟨rfl, hu⟩ .nil)⟩
    · cases ht
  | fma2 d a b c =>
    simp only [oTyVals] at ht
    split_ifs at ht with hk
    obtain rfl := Option.some.inj ht
    simp only [Bool.and_eq_true] at hk
    obtain ⟨⟨ha, hb⟩, hc⟩ := hk
    obtain ⟨⟨x0, hx0⟩, ⟨x1, hx1⟩⟩ := pairNum_read ha (h a)
    obtain ⟨⟨y0, hy0⟩, ⟨y1, hy1⟩⟩ := pairNum_read hb (h b)
    obtain ⟨⟨z0, hz0⟩, ⟨z1, hz1⟩⟩ := pairNum_read hc (h c)
    have he := fma2E_fin hx0 hx1 hy0 hy1 hz0 hz1
    refine ⟨⟨_, he⟩, .cons ⟨rfl, ?_⟩ .nil⟩
    show (OTy.pr .f32 .f32).Has (okVal (.bits 64 0) (fma2E (V a) (V b) (V c)))
    rw [he]
    exact has_pair_f32 _ _
  | add2 d a b =>
    simp only [oTyVals] at ht
    split_ifs at ht with hk
    obtain rfl := Option.some.inj ht
    simp only [Bool.and_eq_true] at hk
    obtain ⟨ha, hb⟩ := hk
    obtain ⟨⟨x0, hx0⟩, ⟨x1, hx1⟩⟩ := pairNum_read ha (h a)
    obtain ⟨⟨y0, hy0⟩, ⟨y1, hy1⟩⟩ := pairNum_read hb (h b)
    have he := add2E_fin hx0 hx1 hy0 hy1
    refine ⟨⟨_, he⟩, .cons ⟨rfl, ?_⟩ .nil⟩
    show (OTy.pr .f32 .f32).Has (okVal (.bits 64 0) (add2E (V a) (V b)))
    rw [he]
    exact has_pair_f32 _ _
  | ex2 fz d a =>
    simp only [oTyVals] at ht
    split_ifs at ht with hk
    obtain rfl := Option.some.inj ht
    obtain ⟨x, hx⟩ := OTy.num_of hk (h a)
    have he := ex2E_fin (fz := fz) hx
    refine ⟨⟨_, he⟩, .cons ⟨rfl, ?_⟩ .nil⟩
    show OTy.f32.Has (okVal (.bits 32 0) (ex2E fz (V a)))
    rw [he]
    exact ⟨_, rfl⟩
  | cvt d a b =>
    simp only [oTyVals] at ht
    split_ifs at ht with hk
    obtain rfl := Option.some.inj ht
    simp only [Bool.and_eq_true] at hk
    obtain ⟨x, hx⟩ := OTy.num_of hk.1 (h a)
    obtain ⟨y, hy⟩ := OTy.num_of hk.2 (h b)
    have he := cvtPairE_of_valFloat hx hy
    refine ⟨⟨_, he⟩, .cons ⟨rfl, ?_⟩ .nil⟩
    show OTy.h2.Has (okVal (.bits 32 0) (cvtPairE (V a) (V b)))
    rw [he]
    exact ⟨_, _, rfl⟩
  | mul fz d a b =>
    simp only [oTyVals] at ht
    split_ifs at ht with hk
    obtain rfl := Option.some.inj ht
    simp only [Bool.and_eq_true] at hk
    obtain ⟨x, hx⟩ := OTy.num_of hk.1 (h a)
    obtain ⟨y, hy⟩ := OTy.num_of hk.2 (h b)
    have he := mulE_fin (fz := fz) hx hy
    refine ⟨⟨_, he⟩, .cons ⟨rfl, ?_⟩ .nil⟩
    show OTy.f32.Has (okVal (.bits 32 0) (mulE fz (V a) (V b)))
    rw [he]
    exact ⟨_, rfl⟩
  | sub fz d a b =>
    simp only [oTyVals] at ht
    split_ifs at ht with hk
    obtain rfl := Option.some.inj ht
    simp only [Bool.and_eq_true] at hk
    obtain ⟨x, hx⟩ := OTy.num_of hk.1 (h a)
    obtain ⟨y, hy⟩ := OTy.num_of hk.2 (h b)
    have he := subE_fin (fz := fz) hx hy
    refine ⟨⟨_, he⟩, .cons ⟨rfl, ?_⟩ .nil⟩
    show OTy.f32.Has (okVal (.bits 32 0) (subE fz (V a) (V b)))
    rw [he]
    exact ⟨_, rfl⟩
  | add fz d a b =>
    simp only [oTyVals] at ht
    split_ifs at ht with hk
    obtain rfl := Option.some.inj ht
    simp only [Bool.and_eq_true] at hk
    obtain ⟨x, hx⟩ := OTy.num_of hk.1 (h a)
    obtain ⟨y, hy⟩ := OTy.num_of hk.2 (h b)
    have he := floatE_add_fin (fz := fz) hx hy
    refine ⟨⟨_, he⟩, .cons ⟨rfl, ?_⟩ .nil⟩
    show OTy.f32.Has (okVal (.bits 32 0) (floatE (addI fz) [V a, V b]))
    rw [he]
    exact ⟨_, rfl⟩
  | selp d a b p =>
    simp only [oTyVals] at ht
    split at ht
    · rename_i sa sb hp ha hb
      have hsa := opTy_has h ha
      have hsb := opTy_has h hb
      split_ifs at ht with h1 h2
      · obtain rfl := Option.some.inj ht
        simp only [Bool.and_eq_true, beq_iff_eq] at h1
        obtain ⟨rfl, h4⟩ := h1
        refine ⟨?_, .cons ⟨rfl, ?_⟩ .nil⟩
        · show (if predOf (V p) then opndVal V a else opndVal V b).bytes = 4
          split
          · exact OTy.bytes4 h4 hsa
          · exact OTy.bytes4 h4 hsb
        · show sa.Has (if predOf (V p) then opndVal V a else opndVal V b)
          split
          · exact hsa
          · exact hsb
      · obtain rfl := Option.some.inj ht
        simp only [Bool.and_eq_true] at h2
        obtain ⟨xa, hxa⟩ := OTy.num_of h2.1 hsa
        obtain ⟨xb, hxb⟩ := OTy.num_of h2.2 hsb
        refine ⟨?_, .cons ⟨rfl, ?_⟩ .nil⟩
        · show (if predOf (V p) then opndVal V a else opndVal V b).bytes = 4
          split
          · exact valFloat_bytes hxa
          · exact valFloat_bytes hxb
        · show OTy.num.Has (if predOf (V p) then opndVal V a else opndVal V b)
          split
          · exact ⟨_, hxa⟩
          · exact ⟨_, hxb⟩
    · cases ht
  | setp c fz p a k =>
    simp only [oTyVals] at ht
    split_ifs at ht with hk
    obtain rfl := Option.some.inj ht
    simp only [Bool.and_eq_true] at hk
    obtain ⟨⟨ha, hK⟩, hc⟩ := hk
    obtain ⟨x, hx⟩ := OTy.num_of ha (h a)
    obtain ⟨e, he⟩ := setpK_read hK
    exact ⟨setpE_ok hc (readEReal_of_valFloat hx) he, .cons ⟨rfl, _, rfl⟩ .nil⟩

/-! ### Runs and pieces -/

/-- The shapes after a run, or `none` when an item's condition does not follow. -/
def oTyRun (T : Nat → OTy) : List OItem → Option (Nat → OTy)
  | [] => some T
  | it :: its => (oTyVals T it).bind fun tys => oTyRun (tyUpdO T tys) its

theorem oTyRun_sound : ∀ {its : List OItem} {T T' : Nat → OTy} {V : Nat → Value},
    OTy.All T V → oTyRun T its = some T' → oCond V its ∧ OTy.All T' (oFinal V its)
  | [], T, T', V, h, ht => by
    simp only [oTyRun, Option.some.injEq] at ht
    subst ht
    exact ⟨trivial, h⟩
  | it :: its, T, T', V, h, ht => by
    simp only [oTyRun] at ht
    cases hv : oTyVals T it with
    | none => rw [hv] at ht; cases ht
    | some tys =>
      rw [hv, Option.bind_some] at ht
      obtain ⟨hc, hf⟩ := oTyVals_sound h hv
      have h' := OTy.All.upd h hf
      obtain ⟨h1, h2⟩ := oTyRun_sound h' ht
      exact ⟨⟨hc, h1⟩, h2⟩

/-- The shapes a software `exp2` instance writes: its two results, and its constants. -/
def swTys (m : Assumption.SegMatch Assumption.CuteSlot) : List (Nat × OTy) :=
  [(m.regOf .y0, .f32), (m.regOf .y1, .f32)] ++
    (if m.shape.defines then m.shape.consts.map fun p => (m.regOf p.1, OTy.any) else [])

/-- The shapes after a piece. -/
def pieceTy (T : Nat → OTy) : Piece → Option (Nat → OTy)
  | .run its => oTyRun T its
  | .sw m => if (T (m.regOf .x0)).isNum && (T (m.regOf .x1)).isNum then
      some fun r => ((swTys m).lookup r).getD (T r) else none

theorem lookup_all : ∀ {tys : List (Nat × OTy)} {vs : List (Nat × Value)} {T : Nat → OTy}
    {V : Nat → Value}, OTy.All T V → List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2.Has q.2) tys vs →
    OTy.All (fun r => (tys.lookup r).getD (T r)) (fun r => (vs.lookup r).getD (V r))
  | [], [], _, _, h, .nil => h
  | p :: tys, q :: vs, T, V, h, .cons hpq hr => by
    obtain ⟨h1, h2⟩ := hpq
    intro r
    have ih := lookup_all h hr r
    obtain ⟨k, s⟩ := p
    obtain ⟨k', v⟩ := q
    simp only at h1 h2 ih
    subst h1
    simp only [List.lookup]
    split
    · exact h2
    · exact ih

theorem forall₂_consts : ∀ (cs : List (Assumption.CuteSlot × Value))
    (m : Assumption.SegMatch Assumption.CuteSlot),
    List.Forall₂ (fun (p : Nat × OTy) (q : Nat × Value) => p.1 = q.1 ∧ p.2.Has q.2)
      (cs.map fun p => (m.regOf p.1, OTy.any)) (cs.map fun p => (m.regOf p.1, p.2))
  | [], _ => .nil
  | _ :: cs, m => .cons ⟨rfl, trivial⟩ (forall₂_consts cs m)

theorem pieceTy_sound {T T' : Nat → OTy} {V : Nat → Value} (h : OTy.All T V) {p : Piece}
    (ht : pieceTy T p = some T') : p.cond V ∧ OTy.All T' (p.apply V) := by
  cases p with
  | run its => exact oTyRun_sound h ht
  | sw m =>
    simp only [pieceTy] at ht
    split_ifs at ht with hk
    obtain rfl := Option.some.inj ht
    simp only [Bool.and_eq_true] at hk
    refine ⟨⟨OTy.num_of hk.1 (h _), OTy.num_of hk.2 (h _)⟩, ?_⟩
    refine lookup_all h ?_
    unfold swTys segVals
    refine List.rel_append (.cons ⟨rfl, _, rfl⟩ (.cons ⟨rfl, _, rfl⟩ .nil)) ?_
    split
    · exact forall₂_consts _ m
    · exact .nil

/-- The shapes after a list of pieces. -/
def chainTy (T : Nat → OTy) : List Piece → Option (Nat → OTy)
  | [] => some T
  | p :: ps => (pieceTy T p).bind fun T' => chainTy T' ps

/-- **A list of pieces whose shape check succeeds is accepted.** -/
theorem chainCond_of_chainTy : ∀ {ps : List Piece} {T : Nat → OTy} {V : Nat → Value},
    OTy.All T V → (chainTy T ps).isSome = true → chainCond V ps
  | [], _, _, _, _ => trivial
  | p :: ps, T, V, h, hs => by
    simp only [chainTy] at hs
    cases hp : pieceTy T p with
    | none => rw [hp] at hs; cases hs
    | some T' =>
      rw [hp, Option.bind_some] at hs
      obtain ⟨hc, h'⟩ := pieceTy_sound h hp
      exact ⟨hc, chainCond_of_chainTy h' hs⟩

/-- **A run whose shape check succeeds is accepted.** -/
theorem oCond_of_oTyRun {its : List OItem} {T : Nat → OTy} {V : Nat → Value}
    (h : OTy.All T V) (hs : (oTyRun T its).isSome = true) : oCond V its := by
  obtain ⟨T', hT⟩ := Option.isSome_iff_exists.mp hs
  exact (oTyRun_sound h hT).1

/-! ### Initial shapes -/

/-- The shapes of a list of registers (`any` elsewhere). -/
def tyOfO (l : List (Nat × OTy)) (r : Nat) : OTy := (l.lookup r).getD .any

theorem forall_mem_cons' {α : Type} {P : α → Prop} {a : α} {l : List α} (h1 : P a)
    (h2 : ∀ p ∈ l, P p) : ∀ p ∈ a :: l, P p := List.forall_mem_cons.mpr ⟨h1, h2⟩

theorem forall_mem_nil' {α : Type} {P : α → Prop} : ∀ p ∈ ([] : List α), P p := nofun

theorem all_tyOfO {l : List (Nat × OTy)} {V : Nat → Value} (h : ∀ p ∈ l, p.2.Has (V p.1)) :
    OTy.All (tyOfO l) V := by
  intro r
  unfold tyOfO
  induction l with
  | nil => trivial
  | cons p l ih =>
    obtain ⟨k, s⟩ := p
    simp only [List.lookup]
    split
    · rename_i he
      have := h (k, s) (by simp)
      rw [beq_iff_eq] at he
      rw [he]
      exact this
    · exact ih fun q hq => h q (by simp [hq])

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
