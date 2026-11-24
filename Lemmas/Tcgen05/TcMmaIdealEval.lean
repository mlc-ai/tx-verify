-- SPDX-License-Identifier: Apache-2.0
module

public import Assumption.IdealReal
public import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

/-! # The ideal `kind::f16` MMA succeeds on FP16 elements

Under an ideal-real assumption whose scope holds `kind::f16` with an `.f32` accumulator, an MMA
outside the `.ws` M < 128 shapes evaluates to a single-precision float at every row and column of
its shape when every contraction element of its A row and B column is an FP16 value and, when it
accumulates, the old value is a single-precision float (`eval_ok`). An element is an FP16 value
when its two bytes are the two bytes of one (`idealMmaElement_of_bytes`). Also: the row and column
of a result cell are in the shape (`resultCell_rowcol`), and the cells an MMA writes depend on its
descriptor, its CTAs, its accumulator address and its masks only (`writeCell_congr`). -/

namespace PTX.TcMma
open PTX

/-- A result cell's row and column are in the shape. -/
theorem resultCell_rowcol {s : OperandSpec} {base row col : Nat} {cell : Cell}
    (h : resultCell s base row col = some cell) : row < s.descriptor.m ∧ col < s.descriptor.n := by
  unfold resultCell at h
  dsimp only at h
  split at h
  next hg => exact ⟨hg.2.2.1, hg.2.2.2.1⟩
  next => cases h

/-- The cells an MMA writes depend on its descriptor, CTAs, accumulator address and masks
only. -/
theorem writeCell_congr {s s' : OperandSpec} (hd : s.descriptor = s'.descriptor)
    (hl : s.lowCta = s'.lowCta) (hh : s.highCta = s'.highCta) (base : Nat) (mask : List Nat)
    (row col : Nat) : writeCell s base mask row col = writeCell s' base mask row col := by
  unfold writeCell resultCell
  rw [hd, hl, hh]

/-- Two consecutive entries of a list are its two entries from the first. -/
theorem take_two {α : Type} {bs : List α} {n : Nat} {a b : α} (ha : bs[n]? = some a)
    (hb : bs[n + 1]? = some b) : (bs.drop n).take 2 = [a, b] := by
  apply List.ext_getElem?
  intro i
  rcases Nat.lt_or_ge i 2 with hi | hi
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [List.getElem?_drop, ha, hb]
  · simp [show ¬ i < 2 by omega]

/-- **An element whose two bytes are those of an FP16 value is that value.** -/
theorem idealMmaElement_of_bytes {o : FloatFmt} {bytes : List (Option Byte)} {row k : Nat}
    {x : ℝ}
    (hb : (bytes.drop (2 * (row * 16 + k))).take 2 = (Value.float .f16 x).toBytes.map some) :
    Assumption.idealMmaElement (.f16 .f16 o) .a bytes row k = .ok x := by
  have hb' : elementBytes (.f16 .f16 o) bytes row k = (Value.float .f16 x).toBytes.map some := by
    rw [← hb]
    simp [elementBytes, Kind.k, Kind.width, Nat.mul_comm]
  unfold Assumption.idealMmaElement
  dsimp only
  rw [hb']
  simp [rebuild, Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes, valFloat,
    List.range_succ]
  rfl

/-- The ideal dot product of FP16 elements is a real number. -/
theorem idealMmaDot_ok {d : Descriptor} {o : FloatFmt} (hk : d.kind = .f16 .f16 o)
    {a b : List (Option Byte)} {row col : Nat} :
    ∀ n, (∀ k, k < n → ∃ x, Assumption.idealMmaElement (.f16 .f16 o) .a a row k = .ok x) →
      (∀ k, k < n → ∃ y, Assumption.idealMmaElement (.f16 .f16 o) .b b col k = .ok y) →
      ∃ r, Assumption.idealMmaDot d a b row col n = .ok r
  | 0, _, _ => ⟨0, rfl⟩
  | n + 1, ha, hb => by
    obtain ⟨r, hr⟩ := idealMmaDot_ok hk n (fun j hj => ha j (by omega))
      (fun j hj => hb j (by omega))
    obtain ⟨x, hx⟩ := ha n (by omega)
    obtain ⟨y, hy⟩ := hb n (by omega)
    exact ⟨_, by simp only [Assumption.idealMmaDot, hk, hr, hx, hy]; rfl⟩

/-- **The ideal `kind::f16` MMA succeeds** on FP16 elements and an `.f32` old value (or none,
when it does not accumulate). -/
theorem eval_ok {name why : String} {sc : Assumption.IdealScope} {rest A : List Assumption}
    (hA : A = Assumption.idealReal name sc why :: rest) {d : Descriptor}
    (hk : d.kind = .f16 .f16 .f32) (hs : d.kind ∈ sc.mma) (hv : Valid d)
    (hws : d.ws = false) {a b : List (Option Byte)} (hla : a.length = Operand.bytes .a d)
    (hlb : b.length = Operand.bytes .b d) {row col : Nat} (hrow : row < d.m) (hcol : col < d.n)
    (ha : ∀ k, k < 16 → ∃ x, Assumption.idealMmaElement (.f16 .f16 .f32) .a a row k = .ok x)
    (hb : ∀ k, k < 16 → ∃ y, Assumption.idealMmaElement (.f16 .f16 .f32) .b b col k = .ok y)
    {acc : Bool} {old : Option Value} (hold : acc = true → ∃ r, old = some (.float .f32 r)) :
    ∃ r, eval A d acc a b old row col = .ok (.float .f32 r) := by
  subst hA
  obtain ⟨dot, hdot⟩ := idealMmaDot_ok (d := d) hk (a := a) (b := b) (row := row) (col := col)
    16 ha hb
  obtain ⟨prev, hprev⟩ : ∃ prev, Assumption.idealMmaAccumulator .f32 acc old = .ok prev := by
    cases acc
    · exact ⟨0, rfl⟩
    · obtain ⟨r, rfl⟩ := hold rfl
      exact ⟨r, rfl⟩
  have hr : (Assumption.idealReal name sc why).mmaRule d acc a b old row col =
      some (Assumption.execIdealMma d acc a b old row col) := by
    simp [Assumption.idealReal, hs]
  have hrow' : operandRow d row col = row := by simp [operandRow, hws]
  refine ⟨dot + prev, ?_⟩
  simp only [eval, hk, List.findSome?, hr, Option.getD_some]
  simp only [Assumption.execIdealMma, hk, hv, hrow, hcol, hla, hlb, and_self, hrow', Kind.k]
  simp [bind, Except.bind, pure, Except.pure, hdot, hprev]

end PTX.TcMma
