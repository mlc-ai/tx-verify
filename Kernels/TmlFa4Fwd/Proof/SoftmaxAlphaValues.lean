-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxReference
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWeights
public import Lemmas.Flow.OutRun

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Numeric

noncomputable section

/-- Candidate exponent difference when the previous running maximum is finite. -/
def referenceDelta (scale : ℝ) (old candidate : Option ℝ) : Option ℝ :=
  old.map (fun x => scale * (x - candidate.getD 0))

def keepReference (scale : ℝ) (old candidate : Option ℝ) : Bool :=
  (referenceDelta scale old candidate).any (fun x => decide (-8 ≤ x))

def chosenReference (scale : ℝ) (old candidate : Option ℝ) : Option ℝ :=
  if keepReference scale old candidate then old else candidate

def correctionAlpha (scale : ℝ) (old candidate : Option ℝ) : ℝ :=
  if keepReference scale old candidate then 1
  else (referenceDelta scale old candidate).elim 0 (fun x => (2 : ℝ) ^ x)

private theorem scaleReferenceDefault (scale : ℝ) (m : Option ℝ) :
    (m.map (scale * ·)).getD 0 = scale * m.getD 0 := by
  cases m <;> simp

/-- With the chosen reference, the hardware's alpha value is precisely the accumulator factor
used in the mathematical recurrence. The all-masked prefix is carried by an absent maximum. -/
theorem correctionAlpha_eq (scale : ℝ) (old candidate : Option ℝ) :
    correctionAlpha scale old candidate =
      maskedRescale (old.map (scale * ·)) ((chosenReference scale old candidate).map (scale * ·)) :=
  by
  cases old with
  | none => simp [correctionAlpha, keepReference, referenceDelta, maskedRescale]
  | some x =>
    by_cases hk : keepReference scale (some x) candidate
    · simp [correctionAlpha, chosenReference, hk, maskedRescale]
    · simp [correctionAlpha, chosenReference, hk, maskedRescale, referenceDelta,
        scaleReferenceDefault, mul_sub]

private theorem referenceDifference_real (old candidate : Option ℝ) :
    addEReal (scoreReal old) (-((candidate.getD 0 : ℝ) : EReal)) =
      some (scoreReal (old.map (fun x => x - candidate.getD 0))) := by
  cases old with
  | none => simp [addEReal, scoreReal, EReal.bot_add]
  | some x => simp [addEReal, scoreReal, sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_add]

private theorem referenceScale_real (scale : ℝ) (hs : 0 < scale) (x : Option ℝ) :
    mulEReal (scale : EReal) (scoreReal x) = some (scoreReal (x.map (scale * ·))) := by
  cases x with
  | none =>
    have hn : (scale : EReal) ≠ 0 := ne_of_gt (EReal.coe_pos.mpr hs)
    rw [mulEReal, scoreReal]
    simp [hn, mul_comm, EReal.bot_mul_coe_of_pos hs, scoreReal]
  | some x => simp [mulEReal, scoreReal, ← EReal.coe_mul]

theorem referenceSubOutcome (old candidate : Option ℝ) :
    subE false (scoreValue old) (finiteRefValue candidate) =
      .ok (scoreValue (old.map (fun x => x - candidate.getD 0))) := by
  unfold subE idealSub
  rw [readScoreValue, readFiniteRef]
  simp [bindRead, referenceDifference_real, scoreReal_value, pure, Except.pure]

theorem referenceMulOutcomeOfWord (old candidate : Option ℝ) {scale : ℝ} {word : Value}
    (hs : 0 < scale) (hWord : readEReal .f32 word = some (.ok (scale : EReal))) :
    mulE false word (scoreValue (old.map (fun x => x - candidate.getD 0))) =
      .ok (scoreValue (referenceDelta scale old candidate)) := by
  unfold mulE idealMul
  rw [hWord, readScoreValue]
  simp [bindRead, referenceScale_real scale hs, scoreReal_value, referenceDelta, Function.comp_def,
    pure, Except.pure]

theorem referenceExponentOutcome (scale : ℝ) (old candidate : Option ℝ) :
    ex2E true (scoreValue (referenceDelta scale old candidate)) =
      .ok (.float .f32 ((referenceDelta scale old candidate).elim 0 (fun x => (2 : ℝ) ^ x))) := by
  cases h : referenceDelta scale old candidate with
  | none => exact hardwareExponentNegInf
  | some x => exact ex2E_fin (fz := true) (x := x) rfl

private theorem thresholdRead :
    readEReal .f32 (.bits 32 (BitVec.ofNat 64 0xC1000000)) =
      some (.ok ((-8 : ℝ) : EReal)) := by
  have hNum : f32Value 0xC1000000 = some (-8) := by
    norm_num [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
      Layout.magnitude, Layout.bias, Layout.width, FVal.num]
  have hRead := valFloat_b32 (by decide : 0xC1000000 < 2 ^ 64) hNum
  change readEReal .f32 (b32 0xC1000000) = _
  simpa using readEReal_of_valFloat hRead

theorem referenceThresholdOutcome (scale : ℝ) (old candidate : Option ℝ) :
    setpE (.ord .ge) false (scoreValue (referenceDelta scale old candidate))
      (.bits 32 (BitVec.ofNat 64 0xC1000000)) = .ok (keepReference scale old candidate) := by
  unfold setpE idealSetp
  simp only [fcmpBase, readScoreValue, thresholdRead, bindRead, pure, Except.pure]
  unfold keepReference
  cases referenceDelta scale old candidate with
  | none => simp [scoreReal, erealCompare]
  | some x => simp [scoreReal, erealCompare, -EReal.coe_neg]

end
end PTX.Kernels.TmlFa4Fwd.Softmax
