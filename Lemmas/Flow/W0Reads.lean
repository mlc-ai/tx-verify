-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutKinds
public import Lemmas.Flow.OutFloatItems
public import Lemmas.Flow.EmuStep

@[expose] public section

/-! # Outcomes of the softmax instructions on operands that read as extended reals

A proof tool: the ideal outcomes of `max.ftz.f32`, `add.f32x2` (no rounding modifier), `neg.ftz.f32`
and `fma.rn.ftz.f32` on operands whose `readEReal` is given, as `OutKinds` has them for the other
forms, and the reading of a value written for an extended real. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

theorem maxFE_reads {va vb : Value} {x y : EReal} (hx : readEReal .f32 va = some (.ok x))
    (hy : readEReal .f32 vb = some (.ok y)) : maxFE va vb = .ok (erealValue .f32 (max x y)) := by
  unfold maxFE
  simp only [idealMax, hx, hy, bindRead, pure, Except.pure]

theorem add2NE_reads {va vb : Value} {x0 x1 y0 y1 z0 z1 : EReal}
    (hx : pairRead va = some (.ok (x0, x1))) (hy : pairRead vb = some (.ok (y0, y1)))
    (hz0 : addEReal x0 y0 = some z0) (hz1 : addEReal x1 y1 = some z1) :
    add2NE va vb = .ok (.pair (erealValue .f32 z0) (erealValue .f32 z1)) := by
  unfold add2NE
  simp only [idealAdd2, hx, hy, bindRead, hz0, hz1, pure, Except.pure]

theorem negE_reads {fz : Bool} {va : Value} {x : EReal} (hx : readEReal .f32 va = some (.ok x)) :
    negE fz va = .ok (erealValue .f32 (-x)) := by
  unfold negE
  simp only [idealNeg, hx, bindRead, pure, Except.pure]

theorem fmaE_reads {fz : Bool} {va vb vc : Value} {x y z w : EReal}
    (hx : readEReal .f32 va = some (.ok x)) (hy : readEReal .f32 vb = some (.ok y))
    (hz : readEReal .f32 vc = some (.ok z)) (hw : (mulEReal x y).bind (addEReal · z) = some w) :
    floatE (fmaI .rn fz) [va, vb, vc] = .ok (erealValue .f32 w) := by
  simp only [floatE, idealVal, hx, hy, hz, bindRead, hw, Option.map_some, pure, Except.pure]

/-- A value written for an extended real that is no `+∞` reads as it. -/
theorem readEReal_erealValue {x : EReal} (h : x ≠ ⊤) :
    readEReal .f32 (erealValue .f32 x) = some (.ok x) := by
  induction x using EReal.rec with
  | bot => rw [erealValue_bot]; exact readEReal_negInf
  | coe r => rw [erealValue_coe]; exact readEReal_float r
  | top => exact absurd rfl h

end
end PTX.Flow
