-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.BrAll

@[expose] public section

/-! # The bridge on an empty row

A row with no visible key (`num_iters < 1`, or every key masked) leaves `l = 0` and `mx = -inf`. The
bridge then runs `lg2.approx.ftz.f32` on zero (pc 2562) and `fma.rn.f32 sc, mx, lg2l` (pc 2563);
the zero test of the row sum is the epilogue's, after the poll (`Epi.Prm.setpOk`,
`Br.prm_setpOk`).

* `Assumptions.lg2Exact` reads only finite positive operands (`lg2E`); a zero operand takes Core's
  rule, whose `lg2Table` has `(.posZero, .inf true)` and `(.negZero, .inf true)`
  (§9.7.3.20): `lg2E_zero` gives the bits of `-inf` (`FVal.toValue`), `infValue_read` reads them
  back as `⊥`.
* The `fma` is read by `idealArith` (the extended reals): `sc * (-inf) + (-inf)` with `sc > 0` is
  `-inf`, and `addEReal ⊥ ⊥ = some ⊥`, so there is no fault (`lse_empty`).

`nofault_of_row` combines this with `Br.lse_fin` (a positive finite row sum): the softmax region's
exit premise `Br.In.NoFault` follows from the values of `sc`, `mx` and `l`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Br
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Epi

noncomputable section
set_option maxRecDepth 100000

/-- The bits of an infinity of format `f32` read back as that infinity in the extended reals. -/
theorem infValue_read (neg : Bool) :
    readEReal .f32 ((FVal.inf neg).toValue .f32) = some (.ok (if neg then ⊥ else ⊤)) := by
  have hd := FloatFmt.decode_infPattern .f32 (by decide) neg
  have hw : (FloatFmt.f32.layout.infPattern neg) < 2 ^ 64 := by
    cases neg <;> decide
  have hc := classify_bits (fmt := .f32) hw hd
  simp only [FVal.toValue]
  show readEReal.ofDatum _ = _
  rw [hc]
  simp [readEReal.ofDatum, pure, Except.pure]

/-- `lg2.approx.ftz.f32` of a zero datum (either sign) is `-inf` (`lg2Table`). -/
theorem lane_lg2_zero (s : Bool) : lg2I.lane [.zero s] = some (.val (.inf true)) := by
  cases s <;>
  simp [FloatInstr.lane, lg2I, FloatInstr.rule, FloatInstr.approx, FloatInstr.approxTable?,
    lg2Table, ACls.of, FloatInstr.flushIn, Layout.flush] <;> rfl

/-- **`lg2` of zero**: a value that classifies as a zero datum and reads as `0` has the outcome
`-inf`: `Assumptions.lg2Exact` declines it and Core's table gives the infinity. -/
theorem lg2E_zero {l : Value} {s : Bool} (h : classify .f32 l = .ok (.zero s))
    (hr : readEReal .f32 l = some (.ok 0)) :
    lg2E l = .ok ((FVal.inf true).toValue .f32) := by
  unfold lg2E
  rw [hr]
  simp only [lt_self_iff_false, false_and, ite_false]
  unfold coreFloat
  simp [lg2I, floatLane, ty1, h, lane_lg2_zero, pure, Except.pure, bind, Except.bind]

end
end PTX.Kernels.InklingRelDecode.Proof.Br
