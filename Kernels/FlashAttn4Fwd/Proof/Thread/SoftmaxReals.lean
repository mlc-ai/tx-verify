-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSites
public import Lemmas.Flow.Widen
public import Lemmas.Flow.Recip
public import Lemmas.Flow.MaxCore
public import Lemmas.Flow.OutRun

@[expose] public section

/-! # The real numbers of a softmax row

The values the softmax code computes, as the exact terms of the ideal arithmetic
(`idealArith`, `approx`, `swExp2`) in code order, so that a segment's computed values are
these terms up to unfolding. With `s` the scores of a tile (by column), `sc` the scale:

* `rmax0 s`: the first tile's row maximum (the three-input `max.f32` tree);
* `mx m s`: a loop tile's row maximum, including the reference maximum `m`;
* `mN`, `alpha`: the lazy rescale. The reference maximum moves to `mx` only when
  `sc · (m - mx) < -8` (`setp.ge.f32 … 0fC1000000`), and then `α = 2 ^ (sc · (m - mx))`,
  else `α = 1`;
* `p0`, `p1`: the probabilities `2 ^ (s j · sc + (0 - sc · m))` of the first tile (with its
  own maximum) and of a loop tile (with `mN`);
* `lsum0`, `lsum1`: the row sums as the `add.rn.f32x2` trees compute them; a loop tile's
  starts from `l · α`.

These are the real-valued facts the Result layer reads: the probabilities stored to Tensor
Memory are `p0`/`p1` as half-precision values, `α` and `l` are stored to the statistics word.
Generated from the PTX (`Tools/value_table.py` walk, one term per register). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The scale (`param_8`) as a real. -/
def sc (L : Launch) : ℝ := rd32 (scaleV L)

/-- The negated scaled maximum `0 - sc · m` (`mul.f32`, `sub.f32` from `0f00000000`). -/
def negM (L : Launch) (m : ℝ) : ℝ := 0 - sc L * m

/-- The first tile's row maximum. -/
def rmax0 (s : Nat → ℝ) : ℝ :=
  max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max
                                        (max (max (max (max (max (max (max (max (max (max (max (max
                                                                (max (max (s 0) (s 1)) (s 8)) (s 9))
                                                              (s 16)) (s 17)) (s 24)) (s 25))
                                                      (s 32)) (s 33)) (s 40)) (s 41)) (s 48))
                                            (s 49)) (s 56)) (s 57)) (s 64)) (s 65)) (s 72)) (s 73))
                              (s 80)) (s 81)) (s 88)) (s 89)) (s 96)) (s 97)) (s 104)) (s 105))
              (s 112)) (s 113)) (s 120)) (s 121)) (max (max (max (max (max (max (max (max (max (max
                          (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max
                                                        (max (max (max (max
                                                                (max (max (s 2) (s 3)) (s 10))
                                                                (s 11)) (s 18)) (s 19)) (s 26))
                                                        (s 27)) (s 34)) (s 35)) (s 42)) (s 43))
                                              (s 50)) (s 51)) (s 58)) (s 59)) (s 66)) (s 67))
                                  (s 74)) (s 75)) (s 82)) (s 83)) (s 90)) (s 91)) (s 98)) (s 99))
                  (s 106)) (s 107)) (s 114)) (s 115)) (s 122)) (s 123))) (max (max (max (max (max
              (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max
                                                (max (max (max (max (max (max (max
                                                              (max (max (s 4) (s 5)) (s 12)) (s 13))
                                                            (s 20)) (s 21)) (s 28)) (s 29)) (s 36))
                                                  (s 37)) (s 44)) (s 45)) (s 52)) (s 53)) (s 60))
                                      (s 61)) (s 68)) (s 69)) (s 76)) (s 77)) (s 84)) (s 85))
                        (s 92)) (s 93)) (s 100)) (s 101)) (s 108)) (s 109)) (s 116)) (s 117))
        (s 124)) (s 125))) (max (max (max (max (max (max (max (max (max (max (max (max (max (max (
                                max (max (max (max (max (max (max (max (max (max (max (max (max (max
                                                          (max (max (max (s 6) (s 7)) (s 14))
                                                            (s 15)) (s 22)) (s 23)) (s 30)) (s 31))
                                                  (s 38)) (s 39)) (s 46)) (s 47)) (s 54)) (s 55))
                                      (s 62)) (s 63)) (s 70)) (s 71)) (s 78)) (s 79)) (s 86))
                        (s 87)) (s 94)) (s 95)) (s 102)) (s 103)) (s 110)) (s 111)) (s 118))
        (s 119)) (s 126)) (s 127))

/-- A loop tile's row maximum, with the reference maximum `m`. -/
def mx (m : ℝ) (s : Nat → ℝ) : ℝ :=
  max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max
                                        (max (max (max (max (max (max (max (max (max (max (max (max
                                                                (max (max (max m (s 0)) (s 1))
                                                                  (s 8)) (s 9)) (s 16)) (s 17))
                                                          (s 24)) (s 25)) (s 32)) (s 33)) (s 40))
                                                (s 41)) (s 48)) (s 49)) (s 56)) (s 57)) (s 64))
                                    (s 65)) (s 72)) (s 73)) (s 80)) (s 81)) (s 88)) (s 89)) (s 96))
                    (s 97)) (s 104)) (s 105)) (s 112)) (s 113)) (s 120)) (s 121)) (max (max (max (
              max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max
                                              (max (max (max (max (max (max (max (max (max
                                                                (max (max (s 2) (s 3)) (s 10))
                                                                (s 11)) (s 18)) (s 19)) (s 26))
                                                        (s 27)) (s 34)) (s 35)) (s 42)) (s 43))
                                              (s 50)) (s 51)) (s 58)) (s 59)) (s 66)) (s 67))
                                  (s 74)) (s 75)) (s 82)) (s 83)) (s 90)) (s 91)) (s 98)) (s 99))
                  (s 106)) (s 107)) (s 114)) (s 115)) (s 122)) (s 123))) (max (max (max (max (max
              (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max
                                                (max (max (max (max (max (max (max
                                                              (max (max (s 4) (s 5)) (s 12)) (s 13))
                                                            (s 20)) (s 21)) (s 28)) (s 29)) (s 36))
                                                  (s 37)) (s 44)) (s 45)) (s 52)) (s 53)) (s 60))
                                      (s 61)) (s 68)) (s 69)) (s 76)) (s 77)) (s 84)) (s 85))
                        (s 92)) (s 93)) (s 100)) (s 101)) (s 108)) (s 109)) (s 116)) (s 117))
        (s 124)) (s 125))) (max (max (max (max (max (max (max (max (max (max (max (max (max (max (
                                max (max (max (max (max (max (max (max (max (max (max (max (max (max
                                                          (max (max (max (s 6) (s 7)) (s 14))
                                                            (s 15)) (s 22)) (s 23)) (s 30)) (s 31))
                                                  (s 38)) (s 39)) (s 46)) (s 47)) (s 54)) (s 55))
                                      (s 62)) (s 63)) (s 70)) (s 71)) (s 78)) (s 79)) (s 86))
                        (s 87)) (s 94)) (s 95)) (s 102)) (s 103)) (s 110)) (s 111)) (s 118))
        (s 119)) (s 126)) (s 127))

/-! ### The row maxima as computed values

The `max.f32` trees on the loaded words, as the read runs compute them (`ReadRun`, the outcome
`maxE` of each instruction): four chains over the column pairs `2 c, 2 c + 1` (mod 8) joined by a
two- and a three-input maximum. A loop tile's first chain starts from the reference maximum. On
halves that read as numbers they are the real maxima `rmax0`, `mx` (`rmax0V_read`, `mxV_read`). -/

/-- The value `max.f32 d, a, b` writes (`0` where it faults). -/
abbrev mx2 (a b : Value) : Value := okVal (.bits 32 0) (maxE [a, b])

/-- The value `max.f32 d, a, b, c` writes (`0` where it faults). -/
abbrev mx3 (a b c : Value) : Value := okVal (.bits 32 0) (maxE [a, b, c])

/-- Chain `c` of a row maximum on the halves `h`, from its first value, after `k` more column
pairs `8 k' + 2 c, 8 k' + 2 c + 1`. -/
def maxChainV (h : Nat → Value) (c : Nat) (first : Value) : Nat → Value
  | 0 => first
  | k + 1 => mx3 (maxChainV h c first k) (h (8 * (k + 1) + 2 * c)) (h (8 * (k + 1) + 2 * c + 1))

/-- The same chain on numbers. -/
def maxChainR (s : Nat → ℝ) (c : Nat) (first : ℝ) : Nat → ℝ
  | 0 => first
  | k + 1 => max (max (maxChainR s c first k) (s (8 * (k + 1) + 2 * c)))
      (s (8 * (k + 1) + 2 * c + 1))

/-- The first tile's row maximum as computed from the loaded words `w` (`%r3597` after the first
tile). -/
def rmax0V (w : Nat → Value) : Value :=
  mx3 (mx2 (maxChainV (half w) 0 (mx2 (half w 0) (half w 1)) 15)
      (maxChainV (half w) 1 (mx2 (half w 2) (half w 3)) 15))
    (maxChainV (half w) 2 (mx2 (half w 4) (half w 5)) 15)
    (maxChainV (half w) 3 (mx2 (half w 6) (half w 7)) 15)

/-- A loop tile's row maximum as computed from the reference maximum `m` and the loaded words
`w` (`%r2386`). -/
def mxV (m : Value) (w : Nat → Value) : Value :=
  mx3 (mx2 (maxChainV (half w) 0 (mx3 m (half w 0) (half w 1)) 15)
      (maxChainV (half w) 1 (mx2 (half w 2) (half w 3)) 15))
    (maxChainV (half w) 2 (mx2 (half w 4) (half w 5)) 15)
    (maxChainV (half w) 3 (mx2 (half w 6) (half w 7)) 15)

theorem rmax0_chains (s : Nat → ℝ) :
    rmax0 s = max (max (max (maxChainR s 0 (max (s 0) (s 1)) 15)
      (maxChainR s 1 (max (s 2) (s 3)) 15)) (maxChainR s 2 (max (s 4) (s 5)) 15))
      (maxChainR s 3 (max (s 6) (s 7)) 15) := by
  simp only [rmax0, maxChainR]

theorem mx_chains (m : ℝ) (s : Nat → ℝ) :
    mx m s = max (max (max (maxChainR s 0 (max (max m (s 0)) (s 1)) 15)
      (maxChainR s 1 (max (s 2) (s 3)) 15)) (maxChainR s 2 (max (s 4) (s 5)) 15))
      (maxChainR s 3 (max (s 6) (s 7)) 15) := by
  simp only [mx, maxChainR]

theorem mx2_read {a b : Value} {x y : ℝ} (ha : valFloat .f32 a = .ok x)
    (hb : valFloat .f32 b = .ok y) : mx2 a b = .float .f32 (max x y) :=
  okVal_of_ok (maxE_fin2 ha hb)

theorem mx3_read {a b c : Value} {x y z : ℝ} (ha : valFloat .f32 a = .ok x)
    (hb : valFloat .f32 b = .ok y) (hc : valFloat .f32 c = .ok z) :
    mx3 a b c = .float .f32 (max (max x y) z) :=
  okVal_of_ok (maxE_fin3 ha hb hc)

/-- A chain on halves that read as numbers is the chain on the numbers. -/
theorem maxChainV_read {h : Nat → Value} {s : Nat → ℝ}
    (hs : ∀ j < 128, valFloat .f32 (h j) = .ok (s j)) {c : Nat} (hc : c < 4) {first : Value}
    {x : ℝ} (hf : first = .float .f32 x) :
    ∀ k ≤ 15, maxChainV h c first k = .float .f32 (maxChainR s c x k)
  | 0, _ => hf
  | k + 1, hk => by
    rw [maxChainV, maxChainR, maxChainV_read hs hc hf k (by omega)]
    exact mx3_read valFloat_float (hs _ (by omega)) (hs _ (by omega))

/-- The scores of halves that read as numbers. -/
theorem half_read {w : Nat → Value} (hw : ∀ j < 128, ∃ x, valFloat .f32 (half w j) = .ok x) :
    ∀ j < 128, valFloat .f32 (half w j) = .ok (rd32 (half w j)) := by
  intro j hj
  obtain ⟨x, hx⟩ := hw j hj
  rw [hx, rd32, hx]
  rfl

/-- **The first tile's computed row maximum** is the real one when every half reads as a
number. -/
theorem rmax0V_read {w : Nat → Value}
    (hw : ∀ j < 128, ∃ x, valFloat .f32 (half w j) = .ok x) :
    rmax0V w = .float .f32 (rmax0 fun j => rd32 (half w j)) := by
  have hs := half_read hw
  have hc : ∀ c < 4, maxChainV (half w) c (mx2 (half w (2 * c)) (half w (2 * c + 1))) 15 =
      .float .f32 (maxChainR (fun j => rd32 (half w j)) c
        (max (rd32 (half w (2 * c))) (rd32 (half w (2 * c + 1)))) 15) := fun c hc =>
    maxChainV_read hs hc (mx2_read (hs _ (by omega)) (hs _ (by omega))) 15 le_rfl
  rw [rmax0V, rmax0_chains, hc 0 (by omega), hc 1 (by omega), hc 2 (by omega),
    hc 3 (by omega), mx2_read valFloat_float valFloat_float,
    mx3_read valFloat_float valFloat_float valFloat_float]

/-- **A loop tile's computed row maximum** is the real one when the reference maximum and every
half read as numbers. -/
theorem mxV_read {m : Value} {x : ℝ} (hm : valFloat .f32 m = .ok x) {w : Nat → Value}
    (hw : ∀ j < 128, ∃ x, valFloat .f32 (half w j) = .ok x) :
    mxV m w = .float .f32 (mx x fun j => rd32 (half w j)) := by
  have hs := half_read hw
  have hc : ∀ c < 4, maxChainV (half w) c (mx2 (half w (2 * c)) (half w (2 * c + 1))) 15 =
      .float .f32 (maxChainR (fun j => rd32 (half w j)) c
        (max (rd32 (half w (2 * c))) (rd32 (half w (2 * c + 1)))) 15) := fun c hc =>
    maxChainV_read hs hc (mx2_read (hs _ (by omega)) (hs _ (by omega))) 15 le_rfl
  have h0 := maxChainV_read hs (c := 0) (by omega)
    (mx3_read hm (hs 0 (by omega)) (hs 1 (by omega))) 15 le_rfl
  rw [mxV, mx_chains, h0, hc 1 (by omega), hc 2 (by omega), hc 3 (by omega),
    mx2_read valFloat_float valFloat_float,
    mx3_read valFloat_float valFloat_float valFloat_float]

/-! ### The computed values of a tile

The values the code computes from the loaded words, as the outcome runs write them (`OutRun`):
each floating instruction's outcome (the ideal value, or the Core rule's where the ideal rule
declines), with a default where it faults. The selections and comparisons read the outcomes of
`setp` (`okPred`). On halves that read as numbers they are the real terms above (the readings
below). -/

/-- The outcome of `add.rn.f32x2` (`0` where it faults). -/
abbrev add2V (a b : Value) : Value := okVal (.bits 64 0) (add2E a b)

/-- The outcome of `cvt.rn.f16x2.f32 d, a, b` (`0` where it faults). -/
abbrev cvtV (a b : Value) : Value := okVal (.bits 32 0) (cvtPairE a b)

/-- The value of `%r1682` after the first tile's maximum: `selp.f32 r, m, 0f00000000, p` after
`setp.neu.f32 p, m, 0fFF800000`, that is `m` unless the comparison with `-∞` reads it as `-∞`
(then the bits of `+0`). -/
def mSel (m : Value) : Value :=
  if okPred (setpE (.unord .ne) false m (.bits 32 (BitVec.ofNat 64 4286578688))) then m
  else .bits 32 (BitVec.ofNat 64 0)

theorem mSel_read {m : Value} {x : ℝ} (hm : valFloat .f32 m = .ok x) : mSel m = m := by
  have hinf : Assumption.readEReal .f32 (.bits 32 (BitVec.ofNat 64 4286578688)) =
      some (.ok ⊥) := by rfl
  have h : setpE (.unord .ne) false m (.bits 32 (BitVec.ofNat 64 4286578688)) = .ok true := by
    simp [setpE, idealSetp, fcmpBase, readEReal_of_valFloat hm, hinf, Assumption.bindRead,
      Assumption.erealCompare, pure, Except.pure]
  simp [mSel, h, okPred]

/-- The negated scaled maximum `0 - sc · x` (`mul.f32`, then `sub.f32` from `0f00000000`). -/
def negMV (L : Launch) (x : Value) : Value :=
  okVal (.bits 32 0) (subE false (.bits 32 (BitVec.ofNat 64 0))
    (okVal (.bits 32 0) (mulE false (scaleV L) x)))

/-- The exponent arguments of a pair of columns `u` (`fma.rn.f32x2` by the scale pair and the
pair of `negMV`). -/
def argPairV (L : Launch) (x u : Value) : Value :=
  okVal (.bits 64 0) (fma2E u (joinValue (scaleV L) (scaleV L)) (joinValue (negMV L x) (negMV L x)))

/-- The exponent argument of column `j` of the words `w`, with the maximum `x`. -/
def argV (L : Launch) (x : Value) (w : Nat → Value) (j : Nat) : Value :=
  if j % 2 = 0 then (splitValue 64 (argPairV L x (joinValue (w j) (w (j + 1))))).1
  else (splitValue 64 (argPairV L x (joinValue (w (j - 1)) (w j)))).2

/-- The columns whose exponential the software `exp2` computes (the others take
`ex2.approx.ftz.f32`). -/
def swCols : List Nat :=
  [38, 39, 40, 41, 48, 49, 50, 51, 58, 59, 60, 61, 70, 71, 72, 73, 80, 81, 82, 83, 90, 91, 92, 93]

/-- The probability of column `j` of the words `w`, with the maximum `x`: the software
`exp2`'s exact `2 ^ x` of the argument's number, or the outcome of `ex2.approx.ftz.f32`. -/
def pV (L : Launch) (x : Value) (w : Nat → Value) (j : Nat) : Value :=
  if swCols.contains j then .float .f32 (Assumption.cuteExp2.fn (rd32 (argV L x w j)))
  else okVal (.bits 32 0) (ex2E true (argV L x w j))

/-- The probability of column `j` of the first tile. -/
abbrev p0V (L : Launch) (d : D) (j : Nat) : Value := pV L (mSel d.m) d.w j

/-- The scaled distance of the reference maximum from a loop tile's maximum
(`sub.f32`, `mul.f32` by the scale). -/
def gapV (L : Launch) (m : Value) (w : Nat → Value) : Value :=
  okVal (.bits 32 0) (mulE false (scaleV L) (okVal (.bits 32 0) (subE false m (mSel (mxV m w)))))

/-- The lazy rescale keeps the reference maximum: `setp.ge.f32 p, gap, 0fC1000000`. -/
def keepV (L : Launch) (m : Value) (w : Nat → Value) : Bool :=
  okPred (setpE (.ord .ge) false (gapV L m w) (.bits 32 (BitVec.ofNat 64 3238002688)))

/-- The reference maximum after a loop tile (`%r177`). -/
def mNV (L : Launch) (d : D) : Value := if keepV L d.m d.w then d.m else mxV d.m d.w

/-- The rescale factor of a loop tile (`%r178`): the bits `0f3F800000` of `1` when the maximum
stays, else the outcome of `ex2.approx.ftz.f32` of the gap. -/
def alphaV (L : Launch) (d : D) : Value :=
  if keepV L d.m d.w then .bits 32 (BitVec.ofNat 64 1065353216)
  else okVal (.bits 32 0) (ex2E true (gapV L d.m d.w))

/-- The maximum a loop tile's exponents subtract (`%r2391`). -/
def mExpV (L : Launch) (d : D) : Value := if keepV L d.m d.w then d.m else mSel (mxV d.m d.w)

/-- The probability of column `j` of a loop tile. -/
abbrev p1V (L : Launch) (d : D) (j : Nat) : Value := pV L (mExpV L d) d.w j

/-- The first tile's row sum as the `add.rn.f32x2` tree computes it, as a pair of partial sums. -/
def sum0PairV (L : Launch) (d : D) : Value :=
    (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V
    (add2V (add2V (add2V (add2V (joinValue (p0V L d 0) (p0V L d 1)) (joinValue (p0V L d 8) (p0V L d
    9))) (joinValue (p0V L d 16) (p0V L d 17))) (joinValue (p0V L d 24) (p0V L d 25))) (joinValue
    (p0V L d 32) (p0V L d 33))) (joinValue (p0V L d 40) (p0V L d 41))) (joinValue (p0V L d 48) (p0V
    L d 49))) (joinValue (p0V L d 56) (p0V L d 57))) (joinValue (p0V L d 64) (p0V L d 65)))
    (joinValue (p0V L d 72) (p0V L d 73))) (joinValue (p0V L d 80) (p0V L d 81))) (joinValue (p0V L
    d 88) (p0V L d 89))) (joinValue (p0V L d 96) (p0V L d 97))) (joinValue (p0V L d 104) (p0V L d
    105))) (joinValue (p0V L d 112) (p0V L d 113))) (joinValue (p0V L d 120) (p0V L d 121))) (add2V
    (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V
    (add2V (joinValue (p0V L d 2) (p0V L d 3)) (joinValue (p0V L d 10) (p0V L d 11))) (joinValue
    (p0V L d 18) (p0V L d 19))) (joinValue (p0V L d 26) (p0V L d 27))) (joinValue (p0V L d 34) (p0V
    L d 35))) (joinValue (p0V L d 42) (p0V L d 43))) (joinValue (p0V L d 50) (p0V L d 51)))
    (joinValue (p0V L d 58) (p0V L d 59))) (joinValue (p0V L d 66) (p0V L d 67))) (joinValue (p0V L
    d 74) (p0V L d 75))) (joinValue (p0V L d 82) (p0V L d 83))) (joinValue (p0V L d 90) (p0V L d
    91))) (joinValue (p0V L d 98) (p0V L d 99))) (joinValue (p0V L d 106) (p0V L d 107))) (joinValue
    (p0V L d 114) (p0V L d 115))) (joinValue (p0V L d 122) (p0V L d 123)))) (add2V (add2V (add2V
    (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V
    (joinValue (p0V L d 4) (p0V L d 5)) (joinValue (p0V L d 12) (p0V L d 13))) (joinValue (p0V L d
    20) (p0V L d 21))) (joinValue (p0V L d 28) (p0V L d 29))) (joinValue (p0V L d 36) (p0V L d 37)))
    (joinValue (p0V L d 44) (p0V L d 45))) (joinValue (p0V L d 52) (p0V L d 53))) (joinValue (p0V L
    d 60) (p0V L d 61))) (joinValue (p0V L d 68) (p0V L d 69))) (joinValue (p0V L d 76) (p0V L d
    77))) (joinValue (p0V L d 84) (p0V L d 85))) (joinValue (p0V L d 92) (p0V L d 93))) (joinValue
    (p0V L d 100) (p0V L d 101))) (joinValue (p0V L d 108) (p0V L d 109))) (joinValue (p0V L d 116)
    (p0V L d 117))) (joinValue (p0V L d 124) (p0V L d 125))) (add2V (add2V (add2V (add2V (add2V
    (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (joinValue (p0V L d 6)
    (p0V L d 7)) (joinValue (p0V L d 14) (p0V L d 15))) (joinValue (p0V L d 22) (p0V L d 23)))
    (joinValue (p0V L d 30) (p0V L d 31))) (joinValue (p0V L d 38) (p0V L d 39))) (joinValue (p0V L
    d 46) (p0V L d 47))) (joinValue (p0V L d 54) (p0V L d 55))) (joinValue (p0V L d 62) (p0V L d
    63))) (joinValue (p0V L d 70) (p0V L d 71))) (joinValue (p0V L d 78) (p0V L d 79))) (joinValue
    (p0V L d 86) (p0V L d 87))) (joinValue (p0V L d 94) (p0V L d 95))) (joinValue (p0V L d 102) (p0V
    L d 103))) (joinValue (p0V L d 110) (p0V L d 111))) (joinValue (p0V L d 118) (p0V L d 119)))
    (joinValue (p0V L d 126) (p0V L d 127)))))

/-- A loop tile's row sum as the `add.rn.f32x2` tree computes it, as a pair of partial sums. -/
def sum1PairV (L : Launch) (d : D) : Value :=
    (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V
    (add2V (add2V (add2V (add2V (add2V (joinValue (okVal (.bits 32 0) (mulE false d.l (alphaV L d)))
    (.bits 32 (BitVec.ofNat 64 0))) (joinValue (p1V L d 0) (p1V L d 1))) (joinValue (p1V L d 8) (p1V
    L d 9))) (joinValue (p1V L d 16) (p1V L d 17))) (joinValue (p1V L d 24) (p1V L d 25)))
    (joinValue (p1V L d 32) (p1V L d 33))) (joinValue (p1V L d 40) (p1V L d 41))) (joinValue (p1V L
    d 48) (p1V L d 49))) (joinValue (p1V L d 56) (p1V L d 57))) (joinValue (p1V L d 64) (p1V L d
    65))) (joinValue (p1V L d 72) (p1V L d 73))) (joinValue (p1V L d 80) (p1V L d 81))) (joinValue
    (p1V L d 88) (p1V L d 89))) (joinValue (p1V L d 96) (p1V L d 97))) (joinValue (p1V L d 104) (p1V
    L d 105))) (joinValue (p1V L d 112) (p1V L d 113))) (joinValue (p1V L d 120) (p1V L d 121)))
    (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V
    (add2V (add2V (joinValue (p1V L d 2) (p1V L d 3)) (joinValue (p1V L d 10) (p1V L d 11)))
    (joinValue (p1V L d 18) (p1V L d 19))) (joinValue (p1V L d 26) (p1V L d 27))) (joinValue (p1V L
    d 34) (p1V L d 35))) (joinValue (p1V L d 42) (p1V L d 43))) (joinValue (p1V L d 50) (p1V L d
    51))) (joinValue (p1V L d 58) (p1V L d 59))) (joinValue (p1V L d 66) (p1V L d 67))) (joinValue
    (p1V L d 74) (p1V L d 75))) (joinValue (p1V L d 82) (p1V L d 83))) (joinValue (p1V L d 90) (p1V
    L d 91))) (joinValue (p1V L d 98) (p1V L d 99))) (joinValue (p1V L d 106) (p1V L d 107)))
    (joinValue (p1V L d 114) (p1V L d 115))) (joinValue (p1V L d 122) (p1V L d 123)))) (add2V (add2V
    (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V
    (add2V (joinValue (p1V L d 4) (p1V L d 5)) (joinValue (p1V L d 12) (p1V L d 13))) (joinValue
    (p1V L d 20) (p1V L d 21))) (joinValue (p1V L d 28) (p1V L d 29))) (joinValue (p1V L d 36) (p1V
    L d 37))) (joinValue (p1V L d 44) (p1V L d 45))) (joinValue (p1V L d 52) (p1V L d 53)))
    (joinValue (p1V L d 60) (p1V L d 61))) (joinValue (p1V L d 68) (p1V L d 69))) (joinValue (p1V L
    d 76) (p1V L d 77))) (joinValue (p1V L d 84) (p1V L d 85))) (joinValue (p1V L d 92) (p1V L d
    93))) (joinValue (p1V L d 100) (p1V L d 101))) (joinValue (p1V L d 108) (p1V L d 109)))
    (joinValue (p1V L d 116) (p1V L d 117))) (joinValue (p1V L d 124) (p1V L d 125))) (add2V (add2V
    (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V (add2V
    (joinValue (p1V L d 6) (p1V L d 7)) (joinValue (p1V L d 14) (p1V L d 15))) (joinValue (p1V L d
    22) (p1V L d 23))) (joinValue (p1V L d 30) (p1V L d 31))) (joinValue (p1V L d 38) (p1V L d 39)))
    (joinValue (p1V L d 46) (p1V L d 47))) (joinValue (p1V L d 54) (p1V L d 55))) (joinValue (p1V L
    d 62) (p1V L d 63))) (joinValue (p1V L d 70) (p1V L d 71))) (joinValue (p1V L d 78) (p1V L d
    79))) (joinValue (p1V L d 86) (p1V L d 87))) (joinValue (p1V L d 94) (p1V L d 95))) (joinValue
    (p1V L d 102) (p1V L d 103))) (joinValue (p1V L d 110) (p1V L d 111))) (joinValue (p1V L d 118)
    (p1V L d 119))) (joinValue (p1V L d 126) (p1V L d 127)))))

/-- The first tile's row sum (`add.f32` of the two partial sums). -/
def lsum0V (L : Launch) (d : D) : Value :=
  okVal (.bits 32 0) (floatE (addI false)
    [(splitValue 64 (sum0PairV L d)).1, (splitValue 64 (sum0PairV L d)).2])

/-- The row sum after a loop tile. -/
def lsum1V (L : Launch) (d : D) : Value :=
  okVal (.bits 32 0) (floatE (addI false)
    [(splitValue 64 (sum1PairV L d)).1, (splitValue 64 (sum1PairV L d)).2])

/-- An outcome of `add.f32` (`0` where it faults) has four bytes. -/
theorem okVal_add_bytes (fz : Bool) (vs : List Value) :
    (okVal (.bits 32 0) (floatE (addI fz) vs)).bytes = 4 := by
  cases h : floatE (addI fz) vs with
  | ok v => exact floatE_add_four fz vs v h
  | error e => rfl

theorem lsum0V_bytes (L : Launch) (d : D) : (lsum0V L d).bytes = 4 := okVal_add_bytes _ _

theorem lsum1V_bytes (L : Launch) (d : D) : (lsum1V L d).bytes = 4 := okVal_add_bytes _ _

/-- The real reading of the reference maximum. -/
abbrev D.mR (d : D) : ℝ := rd32 d.m

/-- The real reading of the row sum. -/
abbrev D.lR (d : D) : ℝ := rd32 d.l

/-- The scaled distance of the reference maximum from a loop tile's maximum. -/
def gap (L : Launch) (d : D) : ℝ := sc L * (d.mR - mx d.mR d.s)

/-- The reference maximum after a loop tile. -/
def mN (L : Launch) (d : D) : ℝ := if gap L d ≥ -8 then d.mR else mx d.mR d.s

/-- The rescale factor of a loop tile. -/
def alpha (L : Launch) (d : D) : ℝ := if gap L d ≥ -8 then 1 else Real.rpow 2 (gap L d)

/-- The probability of column `j` of the first tile. -/
def p0 (L : Launch) (d : D) (j : Nat) : ℝ := Real.rpow 2 (d.s j * sc L + negM L d.mR)

/-- The probability of column `j` of a loop tile. -/
def p1 (L : Launch) (d : D) (j : Nat) : ℝ := Real.rpow 2 (d.s j * sc L + negM L (mN L d))

/-- The first tile's row sum. -/
def lsum0 (L : Launch) (d : D) : ℝ :=
  ((((((((((((((((((p0 L d 0) + (p0 L d 8)) + (p0 L d 16)) + (p0 L d 24)) + (p0 L d 32)) +
                            (p0 L d 40)) + (p0 L d 48)) + (p0 L d 56)) + (p0 L d 64)) + (p0 L d 72))
                  + (p0 L d 80)) + (p0 L d 88)) + (p0 L d 96)) + (p0 L d 104)) + (p0 L d 112)) +
        (p0 L d 120)) + ((((((((((((((((p0 L d 2) + (p0 L d 10)) + (p0 L d 18)) + (p0 L d 26)) +
                              (p0 L d 34)) + (p0 L d 42)) + (p0 L d 50)) + (p0 L d 58)) +
                      (p0 L d 66)) + (p0 L d 74)) + (p0 L d 82)) + (p0 L d 90)) + (p0 L d 98)) +
            (p0 L d 106)) + (p0 L d 114)) + (p0 L d 122))) + (((((((((((((
                              ((((p0 L d 4) + (p0 L d 12)) + (p0 L d 20)) + (p0 L d 28)) +
                              (p0 L d 36)) + (p0 L d 44)) + (p0 L d 52)) + (p0 L d 60)) +
                      (p0 L d 68)) + (p0 L d 76)) + (p0 L d 84)) + (p0 L d 92)) + (p0 L d 100)) +
            (p0 L d 108)) + (p0 L d 116)) + (p0 L d 124)) + ((((((((((((
                              ((((p0 L d 6) + (p0 L d 14)) + (p0 L d 22)) + (p0 L d 30)) +
                              (p0 L d 38)) + (p0 L d 46)) + (p0 L d 54)) + (p0 L d 62)) +
                      (p0 L d 70)) + (p0 L d 78)) + (p0 L d 86)) + (p0 L d 94)) + (p0 L d 102)) +
            (p0 L d 110)) + (p0 L d 118)) + (p0 L d 126)))) + ((((((((((((((
                              ((((p0 L d 1) + (p0 L d 9)) + (p0 L d 17)) + (p0 L d 25)) +
                              (p0 L d 33)) + (p0 L d 41)) + (p0 L d 49)) + (p0 L d 57)) +
                      (p0 L d 65)) + (p0 L d 73)) + (p0 L d 81)) + (p0 L d 89)) + (p0 L d 97)) +
            (p0 L d 105)) + (p0 L d 113)) + (p0 L d 121)) + ((((((((((((
                              ((((p0 L d 3) + (p0 L d 11)) + (p0 L d 19)) + (p0 L d 27)) +
                              (p0 L d 35)) + (p0 L d 43)) + (p0 L d 51)) + (p0 L d 59)) +
                      (p0 L d 67)) + (p0 L d 75)) + (p0 L d 83)) + (p0 L d 91)) + (p0 L d 99)) +
            (p0 L d 107)) + (p0 L d 115)) + (p0 L d 123))) + (((((((((((((
                              ((((p0 L d 5) + (p0 L d 13)) + (p0 L d 21)) + (p0 L d 29)) +
                              (p0 L d 37)) + (p0 L d 45)) + (p0 L d 53)) + (p0 L d 61)) +
                      (p0 L d 69)) + (p0 L d 77)) + (p0 L d 85)) + (p0 L d 93)) + (p0 L d 101)) +
            (p0 L d 109)) + (p0 L d 117)) + (p0 L d 125)) + ((((((((((((
                              ((((p0 L d 7) + (p0 L d 15)) + (p0 L d 23)) + (p0 L d 31)) +
                              (p0 L d 39)) + (p0 L d 47)) + (p0 L d 55)) + (p0 L d 63)) +
                      (p0 L d 71)) + (p0 L d 79)) + (p0 L d 87)) + (p0 L d 95)) + (p0 L d 103)) +
            (p0 L d 111)) + (p0 L d 119)) + (p0 L d 127))))

/-- The row sum after a loop tile. -/
def lsum1 (L : Launch) (d : D) : ℝ :=
  (((((((((((((((((((d.lR * alpha L d) + (p1 L d 0)) + (p1 L d 8)) + (p1 L d 16)) + (p1 L d 24)) +
                              (p1 L d 32)) + (p1 L d 40)) + (p1 L d 48)) + (p1 L d 56)) +
                      (p1 L d 64)) + (p1 L d 72)) + (p1 L d 80)) + (p1 L d 88)) + (p1 L d 96)) +
            (p1 L d 104)) + (p1 L d 112)) + (p1 L d 120)) + ((((((((((((
                              ((((p1 L d 2) + (p1 L d 10)) + (p1 L d 18)) + (p1 L d 26)) +
                              (p1 L d 34)) + (p1 L d 42)) + (p1 L d 50)) + (p1 L d 58)) +
                      (p1 L d 66)) + (p1 L d 74)) + (p1 L d 82)) + (p1 L d 90)) + (p1 L d 98)) +
            (p1 L d 106)) + (p1 L d 114)) + (p1 L d 122))) + (((((((((((((
                              ((((p1 L d 4) + (p1 L d 12)) + (p1 L d 20)) + (p1 L d 28)) +
                              (p1 L d 36)) + (p1 L d 44)) + (p1 L d 52)) + (p1 L d 60)) +
                      (p1 L d 68)) + (p1 L d 76)) + (p1 L d 84)) + (p1 L d 92)) + (p1 L d 100)) +
            (p1 L d 108)) + (p1 L d 116)) + (p1 L d 124)) + ((((((((((((
                              ((((p1 L d 6) + (p1 L d 14)) + (p1 L d 22)) + (p1 L d 30)) +
                              (p1 L d 38)) + (p1 L d 46)) + (p1 L d 54)) + (p1 L d 62)) +
                      (p1 L d 70)) + (p1 L d 78)) + (p1 L d 86)) + (p1 L d 94)) + (p1 L d 102)) +
            (p1 L d 110)) + (p1 L d 118)) + (p1 L d 126)))) + ((((((((((((((
                              ((((0 + (p1 L d 1)) + (p1 L d 9)) + (p1 L d 17)) + (p1 L d 25)) +
                              (p1 L d 33)) + (p1 L d 41)) + (p1 L d 49)) + (p1 L d 57)) +
                      (p1 L d 65)) + (p1 L d 73)) + (p1 L d 81)) + (p1 L d 89)) + (p1 L d 97)) +
            (p1 L d 105)) + (p1 L d 113)) + (p1 L d 121)) + ((((((((((((
                              ((((p1 L d 3) + (p1 L d 11)) + (p1 L d 19)) + (p1 L d 27)) +
                              (p1 L d 35)) + (p1 L d 43)) + (p1 L d 51)) + (p1 L d 59)) +
                      (p1 L d 67)) + (p1 L d 75)) + (p1 L d 83)) + (p1 L d 91)) + (p1 L d 99)) +
            (p1 L d 107)) + (p1 L d 115)) + (p1 L d 123))) + (((((((((((((
                              ((((p1 L d 5) + (p1 L d 13)) + (p1 L d 21)) + (p1 L d 29)) +
                              (p1 L d 37)) + (p1 L d 45)) + (p1 L d 53)) + (p1 L d 61)) +
                      (p1 L d 69)) + (p1 L d 77)) + (p1 L d 85)) + (p1 L d 93)) + (p1 L d 101)) +
            (p1 L d 109)) + (p1 L d 117)) + (p1 L d 125)) + ((((((((((((
                              ((((p1 L d 7) + (p1 L d 15)) + (p1 L d 23)) + (p1 L d 31)) +
                              (p1 L d 39)) + (p1 L d 47)) + (p1 L d 55)) + (p1 L d 63)) +
                      (p1 L d 71)) + (p1 L d 79)) + (p1 L d 87)) + (p1 L d 95)) + (p1 L d 103)) +
            (p1 L d 111)) + (p1 L d 119)) + (p1 L d 127))))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
