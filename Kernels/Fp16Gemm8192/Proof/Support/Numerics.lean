-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Spec
public import Lemmas.Assumption.Facts
public import Lemmas.Tcgen05.TcMmaValue
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! Exact real arithmetic of the production kernel's K=16 MMA steps.

Operand-element equations are explicit premises. Their derivation from actual TMA
and MMA byte observations belongs to the kernel's memory proof. These lemmas add no
execution, completion or visibility assumptions. Disabled input-D needs no old value.
-/
namespace PTX.Kernels.Fp16Gemm8192
open PTX
noncomputable section

/-- A consecutive segment of the mathematical output dot product. -/
def segmentDot (P : Params) (row col first count : Nat) : ℝ :=
  ∑ k ∈ Finset.range count, P.a row (first + k) * P.b col (first + k)

@[simp] theorem prefixDot_zero (P : Params) (row col : Nat) :
    prefixDot P row col 0 = 0 := by simp [prefixDot]

@[simp] theorem segmentDot_zero (P : Params) (row col first : Nat) :
    segmentDot P row col first 0 = 0 := by simp [segmentDot]

theorem segmentDot_succ (P : Params) (row col first n : Nat) :
    segmentDot P row col first (n + 1) = segmentDot P row col first n +
      P.a row (first + n) * P.b col (first + n) := by
  exact Finset.sum_range_succ _ _

@[simp] theorem segmentDot_from_zero (P : Params) (row col count : Nat) :
    segmentDot P row col 0 count = prefixDot P row col count := by
  simp only [segmentDot, prefixDot, Nat.zero_add]

theorem prefixDot_add (P : Params) (row col first count : Nat) :
    prefixDot P row col (first + count) =
      prefixDot P row col first + segmentDot P row col first count := by
  exact Finset.sum_range_add _ _ _

/-- Rebuilding the exact two-byte FP16 slice gives its real payload. -/
theorem idealMmaElement_of_bytes {bytes : List (Option Byte)} {row k : Nat} {x : ℝ}
    (hb : (bytes.drop (2 * (row * 16 + k))).take 2 =
      (Value.float .f16 x).toBytes.map some) :
    Assumption.idealMmaElement (.f16 .f16 .f32) .a bytes row k = .ok x := by
  have hb' : TcMma.elementBytes (.f16 .f16 .f32) bytes row k =
      (Value.float .f16 x).toBytes.map some := by
    rw [← hb]
    simp [TcMma.elementBytes, TcMma.Kind.k, TcMma.Kind.width, Nat.mul_comm]
  unfold Assumption.idealMmaElement
  dsimp only
  rw [hb']
  simp [rebuild, Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes,
    valFloat, List.range_succ]
  rfl

/-- The profile's recursive dot product is the intended consecutive real segment
when each observed operand element has the intended value. -/
theorem idealMmaDot_segment {P : Params} {d : TcMma.Descriptor}
    {a b : List (Option Byte)} {row col globalRow globalCol first n : Nat}
    (hkind : d.kind = .f16 .f16 .f32) (hnegA : d.negateA = false) (hnegB : d.negateB = false)
    (ha : ∀ k < n, Assumption.idealMmaElement (.f16 .f16 .f32) .a a row k =
      .ok (P.a globalRow (first + k)))
    (hb : ∀ k < n, Assumption.idealMmaElement (.f16 .f16 .f32) .b b col k =
      .ok (P.b globalCol (first + k))) :
    Assumption.idealMmaDot d a b row col n =
      .ok (segmentDot P globalRow globalCol first n) := by
  induction n with
  | zero =>
    simp [Assumption.idealMmaDot]
    rfl
  | succ n ih =>
    have hn : n < n + 1 := Nat.lt_succ_self n
    have hdot := ih (fun k hk => ha k (Nat.lt_succ_of_lt hk))
      (fun k hk => hb k (Nat.lt_succ_of_lt hk))
    rw [Assumption.idealMmaDot, hdot, hkind, ha n hn, hb n hn]
    simp [hnegA, hnegB, segmentDot_succ]
    rfl

/-- One valid FP16-input/FP32-output issue computes its K=16 segment plus the
supplied old-accumulator interpretation. -/
theorem execIdealMma_segment {P : Params} {d : TcMma.Descriptor}
    {a b : List (Option Byte)} {row col globalRow globalCol first : Nat}
    {accumulate : Bool} {old : Option Value} {previous : ℝ}
    (hkind : d.kind = .f16 .f16 .f32) (hv : TcMma.Valid d)
    (hr : row < d.m) (hc : col < d.n)
    (halen : a.length = d.m * 16 * 2) (hblen : b.length = d.n * 16 * 2)
    (hws : d.ws = false) (hnegA : d.negateA = false) (hnegB : d.negateB = false)
    (ha : ∀ k < 16, Assumption.idealMmaElement (.f16 .f16 .f32) .a a row k =
      .ok (P.a globalRow (first + k)))
    (hb : ∀ k < 16, Assumption.idealMmaElement (.f16 .f16 .f32) .b b col k =
      .ok (P.b globalCol (first + k)))
    (hprevious : Assumption.idealMmaAccumulator .f32 accumulate old = .ok previous) :
    Assumption.execIdealMma d accumulate a b old row col =
      .ok (.float .f32 (segmentDot P globalRow globalCol first 16 + previous)) := by
  have hdot := idealMmaDot_segment hkind hnegA hnegB ha hb
  have hsh : TcMma.operandRow d row col = row := by simp [TcMma.operandRow, hws]
  have hal : a.length = TcMma.Operand.bytes .a d := by
    simp [TcMma.Operand.bytes, TcMma.Operand.rows, TcMma.Operand.extent, hws, hkind,
      TcMma.Kind.k, TcMma.Kind.width, halen]
  have hbl : b.length = TcMma.Operand.bytes .b d := by
    simp [TcMma.Operand.bytes, TcMma.Operand.rows, TcMma.Operand.extent, hkind,
      TcMma.Kind.k, TcMma.Kind.width, hblen]
  simp [Assumption.execIdealMma, hkind, hv, hr, hc, hal, hbl, hsh, TcMma.Kind.k, hdot, hprevious]
  rfl

end
end PTX.Kernels.Fp16Gemm8192
