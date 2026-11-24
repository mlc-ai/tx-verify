-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmScF
public import Kernels.InklingRelDecode.Proof.Thread.SmMask

@[expose] public section

/-! # The visibility mask's integers and predicates (pcs 1463-1627)

The mask of the score stage is a pure function of the entry numbers, the thread index and the
block number `n`, so its registers get a second table (`valuesZ`) in front of the state's:
`valueZ d r` is the entry of `valuesZ` and else `valueOf d r`. The segments of this part go from
the facts of one state under `valueZ` to those of another (the states differ in the S words only,
which are the current contents of the pair registers), and `seg_fp` evaluates the integer
instructions.

The arithmetic is exact under the stage's range assumption (`Rng`): the block's key `128 n`, the
position of the thread's query token and the largest column are below `2 ^ 31`, so no signed
32-bit quantity wraps. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-- The range assumption of the stage's integer arithmetic. -/
structure Rng (e : Ent) (T n : Nat) : Prop where
  blk : n * 128 + 256 < 2 ^ 31
  past : e.past + 64 + 64 < 2 ^ 31
  r23 : e.r23 < 2 ^ 31
  tid : T < 128

/-- The difference register of the column `k` (`k ≠ 1`): position minus column, as a word. -/
def diffN (e : Ent) (T n k : Nat) : Nat :=
  (e.past + tokOf T + 2 ^ 32 - (n * 128 + half T * 64 + k)) % 2 ^ 32

/-- The position minus `k`, as a word (the halves of the position pairs). -/
def posK (e : Ent) (T k : Nat) : Nat := (e.past + tokOf T + 2 ^ 32 - k) % 2 ^ 32

/-- The register of column 1 (`%r678`): the second half of `%rd13` plus the key. -/
def diff1 (e : Ent) (T n : Nat) : Nat :=
  (half T * 64 + n * 128 + 2 ^ 32 - (e.past + tokOf T)) % 2 ^ 32

/-- The column whose predicate is `%p(98 + j)`, for `j < 60` (the predicates `%p98 … %p157`). -/
def colOfP (j : Nat) : Nat := if j % 2 = 0 then 62 - j else 64 - j

/-- The registers the mask's integer part computes, by their ids. -/
def valuesZ (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let e := d.e
  let T := g % L.block
  let n := d.n
  (List.range 60).map (fun j => (98 + j, .pred (visK e T n (colOfP j)))) ++
  ([ (96, .pred (pr96 e n)), (162, .pred (decide (half T = 0))), (163, .pred (decide (half T ≠ 0))),
    (1268, b32 n), (164, .pred (pr166 e n)), (165, .pred true),
    (166, .pred (pr166 e n)), (179, .pred (pe0 e T n)), (180, .pred (pe1 e T n)),
    (97, .pred (pr97 e n)), (1010, b32 (n * 128 + 127)), (1011, b32 (half T * 64 + n * 128)),
    (1901, b32 (half T * 64)),
    (1018, b32 (diffN e T n 0)), (1139, b32 (diff1 e T n)), (1015, b32 (diffN e T n 2)),
    (1014, b32 (diffN e T n 3)),
    (1012, b32 (posK e T 2)), (1013, b32 (posK e T 3)), (1016, b32 (posK e T 0)),
    (1017, b32 (pos2Of e T)),
    (158, .pred (visK e T n 0)), (161, .pred (visK e T n 1)), (159, .pred (visK e T n 2)),
    (160, .pred (visK e T n 3)) ] ++
  ((List.range 30).map (fun q => (1022 + 4 * q, b32 (diffN e T n (2 * q + 4)))) ++
  ((List.range 30).map (fun q => (1021 + 4 * q, b32 (diffN e T n (2 * q + 5)))) ++
  ((List.range 30).map (fun q => (1019 + 4 * q, b32 (posK e T (2 * q + 4)))) ++
  (List.range 30).map (fun q => (1020 + 4 * q, b32 (posK e T (2 * q + 5))))))))

/-- The value of a register under the mask's table in front of the state's. -/
def valueZ (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((valuesZ L g d).lookup r).getD (valueOf L g d r)

/-- The registers live at `pc` with their values under `valueZ`. -/
def factsZ (L : Launch) (g : Nat) (pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueZ L g d)

/-- The value of a register under `valueZ`, evaluated. -/
macro "sz_vals" : tactic =>
  `(tactic| simp only [valueZ, valuesZ, valueOf, PTX.Flow.lookupLit, Option.getD_some,
    Option.getD_none])

theorem scored_n (d : D) (m : Nat) : (d.scored m).n = d.n := rfl
theorem scored_e (d : D) (m : Nat) : (d.scored m).e = d.e := rfl

theorem or_shl32 (a b : Nat) (ha : a < 2 ^ 32) : a ||| (b <<< 32) = a + b * 2 ^ 32 := by
  rw [Nat.or_comm, Nat.shiftLeft_eq, mul_comm]
  have := Nat.two_pow_add_eq_or_of_lt (show a < 2 ^ 32 from ha) b
  rw [← this]; omega

theorem join_nat (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b <<< 32).toNat = a + b * 2 ^ 32 := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show b * 2 ^ 32 < 2 ^ 64 by omega)]
  rw [Nat.or_comm, mul_comm]
  have := Nat.two_pow_add_eq_or_of_lt (show a < 2 ^ 32 from ha) b
  rw [← this]; omega

theorem or_mul32 (a b : Nat) (ha : a < 4294967296) : a ||| b * 4294967296 = a + b * 4294967296 := by
  have := or_shl32 a b (by omega)
  rw [Nat.shiftLeft_eq] at this
  simpa using this

theorem div_pair (x y : Nat) (hx : x < 4294967296) : (x + y * 4294967296) / 4294967296 = y := by
  omega

theorem mod_pair (x y : Nat) (hx : x < 4294967296) : (x + y * 4294967296) % 4294967296 = x := by
  omega

theorem trunc_lo (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    truncBits 32 (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b <<< 32) = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, join_nat a b ha hb]
  omega

theorem trunc_hi (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    truncBits 32 (BitVec.ofNat 64 ((BitVec.ofNat 64 a ||| BitVec.ofNat 64 b <<< 32).toNat /
      4294967296)) = BitVec.ofNat 64 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, join_nat a b ha hb]
  omega

/-- Evaluate a piece of the mask's integer part between the facts of `valueZ`. -/
syntax "sz_seg " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sz_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| seg_fp $h using
      sz_vals
      all_goals sm_close [tid_and96 _ hT, tid_and15 _ hT, or_disj16, tid_and64 _ hT,
        Nat.and_one_is_mod, land255, land127, land12 _ hT, tokOf, row, remOf, half, rowValid,
        Nat.reduceMul, kind_s_beq_s, kind_u_beq_s, ↓reduceIte, mulwide_s32, scored_n, scored_e,
        trunc_lo, trunc_hi, or_mul32, div_pair, mod_pair, diffN, diff1, posK, visK, pos2Of,
        posOf, $extra,*])

/-- Signed 32-bit `<=` of two words below `2 ^ 31`. -/
theorem cmp_le_s32 (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    PTX.compare .le .s 32 (truncBits 32 (BitVec.ofNat 64 a))
      (truncBits 32 (BitVec.ofNat 64 b)) = decide (a ≤ b) := by
  simp only [PTX.compare, toSigned32_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), ha, hb, ↓reduceIte, decide_eq_decide]
  omega

set_option hygiene false in
/-- `%p97 = (key + 127 <= past)`. -/
macro "sz_le" : tactic =>
  `(tactic| (simp only [Value.pred.injEq, scored_n, scored_e, pr97]
             rw [cmp_le_s32 _ _ (by omega) (by omega)]
             try rfl))

theorem p97_1463 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 1 1463 (factsZ L g 1463 d) 1464
      (factsZ L g 1464 d) := by
  have := hR.blk
  have hk : key d.n = d.n * 128 := Nat.mod_eq_of_lt (by omega)
  intro t h
  sz_seg h [hk]

theorem p97_1464 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 1 1464 (factsZ L g 1464 d) 1465
      (factsZ L g 1465 d) := by
  have := hR.blk
  have := hR.past
  have hk : key d.n = d.n * 128 := Nat.mod_eq_of_lt (by omega)
  intro t h
  seg_fp h using
    sz_vals
    all_goals sz_le

theorem p97_1465 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 1 1465 (factsZ L g 1465 d) 1466
      (factsZ L g 1466 d) := by
  intro t h
  sz_seg h

/-- Shared hypotheses of the mask's pieces. -/
theorem key_eq {n : Nat} (h : n * 128 + 256 < 2 ^ 31) : key n = n * 128 :=
  Nat.mod_eq_of_lt (by omega)

theorem diff_1467 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 4 1467 (factsZ L g 1467 d) 1471
      (factsZ L g 1471 d) := by
  have := hR.blk
  have := hR.past
  have hk := key_eq hR.blk
  intro t h
  sz_seg h [hk]

theorem diff_1471 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 2 1471 (factsZ L g 1471 d) 1473
      (factsZ L g 1473 d) := by
  have := hR.blk
  have := hR.past
  have hk := key_eq hR.blk
  intro t h
  sz_seg h [hk]

theorem diff_1473 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 12 1473 (factsZ L g 1473 d) 1485
      (factsZ L g 1485 d) := by
  have := hR.blk
  have := hR.past
  have hk := key_eq hR.blk
  intro t h
  sz_seg h [hk]

theorem diff_1485 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 12 1485 (factsZ L g 1485 d) 1497
      (factsZ L g 1497 d) := by
  have := hR.blk
  have := hR.past
  have hk := key_eq hR.blk
  intro t h
  sz_seg h [hk]

theorem diff_1497 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 12 1497 (factsZ L g 1497 d) 1509
      (factsZ L g 1509 d) := by
  have := hR.blk
  have := hR.past
  have hk := key_eq hR.blk
  intro t h
  sz_seg h [hk]

theorem diff_1509 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 12 1509 (factsZ L g 1509 d) 1521
      (factsZ L g 1521 d) := by
  have := hR.blk
  have := hR.past
  have hk := key_eq hR.blk
  intro t h
  sz_seg h [hk]

theorem diff_1521 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 12 1521 (factsZ L g 1521 d) 1533
      (factsZ L g 1533 d) := by
  have := hR.blk
  have := hR.past
  have hk := key_eq hR.blk
  intro t h
  sz_seg h [hk]

theorem diff_1533 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 12 1533 (factsZ L g 1533 d) 1545
      (factsZ L g 1545 d) := by
  have := hR.blk
  have := hR.past
  have hk := key_eq hR.blk
  intro t h
  sz_seg h [hk]

theorem diff_1545 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 12 1545 (factsZ L g 1545 d) 1557
      (factsZ L g 1557 d) := by
  have := hR.blk
  have := hR.past
  have hk := key_eq hR.blk
  intro t h
  sz_seg h [hk]

theorem diff_1557 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 6 1557 (factsZ L g 1557 d) 1563
      (factsZ L g 1563 d) := by
  have := hR.blk
  have := hR.past
  have hk := key_eq hR.blk
  intro t h
  sz_seg h [hk]

theorem diff_1563 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 1 1563 (factsZ L g 1563 d) 1564
      (factsZ L g 1564 d) := by
  have := hR.blk
  have := hR.past
  have hk := key_eq hR.blk
  intro t h
  sz_seg h [hk]

/-- **`%r549`, `%p97` and `%r1440`** (pcs 1463 to 1465). -/
theorem seg_p97 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 3 1463 (factsZ L g 1463 d) 1466
      (factsZ L g 1466 d) :=
  Seg.of_len (((p97_1463 d hT hR).comp (p97_1464 d hT hR)).comp (p97_1465 d hT hR)) rfl

/-- **The differences of the mask** (pcs 1467 to 1563): `%r550` and the difference registers. -/
theorem seg_diffs (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 97 1467 (factsZ L g 1467 d) 1564
      (factsZ L g 1564 d) := by
  have h1 := (diff_1467 d hT hR).comp (diff_1471 d hT hR)
  have h2 := h1.comp (diff_1473 d hT hR)
  have h3 := h2.comp (diff_1485 d hT hR)
  have h4 := h3.comp (diff_1497 d hT hR)
  have h5 := h4.comp (diff_1509 d hT hR)
  have h6 := h5.comp (diff_1521 d hT hR)
  have h7 := h6.comp (diff_1533 d hT hR)
  have h8 := h7.comp (diff_1545 d hT hR)
  have h9 := h8.comp (diff_1557 d hT hR)
  exact Seg.of_len (h9.comp (diff_1563 d hT hR)) rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
