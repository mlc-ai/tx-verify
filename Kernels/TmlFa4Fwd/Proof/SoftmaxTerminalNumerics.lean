-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstLoopEntry
public import Kernels.TmlFa4Fwd.Proof.SoftmaxAlphaValues

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax

open PTX PTX.Proof PTX.Flow PTX.Numeric

noncomputable section

private theorem absentScoreOfAbsentMaximum {scores : Nat → Option ℝ} {cols : List Nat}
    (h : scoreMax scores cols = none) {col : Nat} (hc : col ∈ cols) : scores col = none := by
  induction cols with
  | nil => simp at hc
  | cons x rest ih =>
    have h' : maxScore (scores x) (scoreMax scores rest) = none := h
    have hBoth : scores x = none ∧ scoreMax scores rest = none := by
      cases hx : scores x <;> cases hr : scoreMax scores rest <;> simp_all [maxScore]
    rcases List.mem_cons.mp hc with he | hm
    · exact he.symm ▸ hBoth.1
    · exact ih hBoth.2 hm

/-- The specification's first reference and mass initialize the row-sum recurrence. -/
theorem openingSoftmaxSumPrefix (p : Params) (batch head row blocks : Nat) :
    let maximum := scoreMax (fun c => maskedLogit p batch head row (visitKey blocks 0 c))
      (List.range 128)
    let ref := maximum.map (abiFloat p.scaleLog2Bits * ·)
    let sum := (2 : ℝ) ^ (-ref.getD 0) * maskedBlockSum (p.keyCount batch row) blocks 0
      (weight p batch head row)
    SoftmaxSumPrefix p batch head row blocks 1 (fun _ => ref) (fun _ => sum) := by
  dsimp only
  let maximum := scoreMax (fun c => maskedLogit p batch head row (visitKey blocks 0 c))
    (List.range 128)
  refine SoftmaxSumPrefix.first _ _ ?_ rfl
  intro hn
  change maximum.map (abiFloat p.scaleLog2Bits * ·) = none at hn
  have hm : maximum = none := by
    cases hc : maximum with
    | none => rfl
    | some x => simp [hc] at hn
  by_contra! hkey
  have hZero := absentScoreOfAbsentMaximum hm (col := 0) (by decide)
  simp [maskedLogit, hkey] at hZero

/-- The actual first visit initializes both registers of the denominator recurrence. -/
theorem firstRoundSumRegisters {p : Params} {l : Launch} {X : Execution} {warp : Fin 8}
    {g j batch head row blocks biasCap pastTile : Nat}
    (hRound : FirstRoundProgress p l X warp g j batch head row blocks biasCap pastTile) :
    let maximum := scoreMax (fun c => maskedLogit p batch head row (visitKey blocks 0 c))
      (List.range 128)
    let ref := maximum.map (abiFloat p.scaleLog2Bits * ·)
    let sum := (2 : ℝ) ^ (-ref.getD 0) * maskedBlockSum (p.keyCount batch row) blocks 0
      (weight p batch head row)
    ∃ t pos, t.regs 7257 = some (fl sum) ∧ t.regs 7256 = some (scoreValue maximum) ∧
      SoftmaxSumPrefix p batch head row blocks 1 (fun _ => ref) (fun _ => sum) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) none := by
  dsimp only
  obtain ⟨t, _, _, leader, failed, _, _, _, _, ht, hRun⟩ := hRound
  let maximum := scoreMax (fun c => maskedLogit p batch head row (visitKey blocks 0 c))
    (List.range 128)
  have href : (maximum.map (abiFloat p.scaleLog2Bits * ·)).getD 0 =
      firstReference p batch head row blocks := by
    change (maximum.map (abiFloat p.scaleLog2Bits * ·)).getD 0 =
      abiFloat p.scaleLog2Bits * maximum.getD 0
    cases maximum <;> simp
  have fields : Holds t.regs
      [(7257, fl ((2 : ℝ) ^ (-firstReference p batch head row blocks) *
        maskedBlockSum (p.keyCount batch row) blocks 0 (weight p batch head row))),
      (1225, b32 (pastTile + 256)), (1226, b32 blocks), (1228, b32 biasCap),
      (1229, b32 (blocks - 1)), (7256, scoreValue maximum)] := ht.2.2.2.2
  obtain ⟨hSum, _, _, _, _, hMax, _⟩ := fields
  rw [← href] at hSum
  refine ⟨t, (if laneOf l g = leader then j + 12 else j + 11) + failed + 1,
    hSum, hMax, ?_, hRun⟩
  exact openingSoftmaxSumPrefix p batch head row blocks

/-- Record the next denominator from the repeated-visit sum state. The candidate from the
max reduction bounds column zero, so an absent chosen reference implies a fully masked visit. -/
theorem appendRepeatedSum {p : Params} {b h row blocks visited : Nat}
    {refs : Nat → Option ℝ} {sums : Nat → ℝ} {t : TState}
    (hPrefix : SoftmaxSumPrefix p b h row blocks visited refs sums) (hVisited : 0 < visited)
    (old candidate : Option ℝ)
    (hMax : scoreReal (maskedLogit p b h row (visitKey blocks visited 0)) ≤ scoreReal candidate)
    (sum : ℝ)
    (hSum : let scale := abiFloat p.scaleLog2Bits
      let next := (chosenReference scale old candidate).map (scale * ·)
      sum = sums (visited - 1) * maskedRescale (refs (visited - 1)) next +
        (2 : ℝ) ^ (-next.getD 0) * maskedBlockSum (p.keyCount b row) blocks visited
          (weight p b h row))
    (hReg : t.regs 7257 = some (fl sum)) :
    let scale := abiFloat p.scaleLog2Bits
    let next := (chosenReference scale old candidate).map (scale * ·)
    SoftmaxSumPrefix p b h row blocks (visited + 1)
      (Function.update refs visited next) (Function.update sums visited sum) ∧
    t.regs 7257 = some (fl (Function.update sums visited sum visited)) := by
  dsimp only
  refine ⟨hPrefix.extend hVisited _ sum ?_ hSum, by simpa only [Function.update_self] using hReg⟩
  intro hAbsent
  have hCandidate : candidate = none := by
    by_cases hKeep : keepReference (abiFloat p.scaleLog2Bits) old candidate = true
    · cases old with
      | none => simp [keepReference, referenceDelta] at hKeep
      | some x => simp [chosenReference, hKeep] at hAbsent
    · simpa [chosenReference, hKeep] using hAbsent
  by_contra! hKey
  simp [maskedLogit, hKey, hCandidate, scoreReal] at hMax

/-- In a one-visit execution, the real first-visit state supplies the complete denominator
recurrence and carries its FP32 sum and maximum into the terminal drain. -/
theorem oneVisitTerminalSumWithReference {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j batch head row biasCap pastTile : Nat}
    (hb : batch < p.batch) (hRow : row < p.qLength batch)
    (hBias : 0 < biasCap) (hCap : biasCap < 2^31) (hPast : pastTile + 256 < 2^31)
    (hRound : FirstRoundProgress p l X warp g j batch head row 1 biasCap pastTile) :
    ∃ (t : TState) (pos : Nat) (maximum sum : ℝ),
      SoftmaxSumRun p batch head row 1 (fun _ => some (abiFloat p.scaleLog2Bits * maximum))
        (fun _ => sum) ∧
      firstReference p batch head row 1 = abiFloat p.scaleLog2Bits * maximum ∧
      t.pc = 7605 ∧ t.regs 7257 = some (fl sum) ∧ t.regs 7256 = some (fl maximum) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) none := by
  let mx := scoreMax (fun c => maskedLogit p batch head row (visitKey 1 0 c)) (List.range 128)
  obtain ⟨_, _, _, _, hInitial, _⟩ := firstRoundSumRegisters hRound
  have hFinite := SoftmaxSumRun.final_ref hInitial (by decide) (hp.keyCount_pos hb hRow)
  change (mx.map (abiFloat p.scaleLog2Bits * ·)).isSome = true at hFinite
  obtain ⟨maximum, hMax⟩ : ∃ x, mx = some x := by
    cases hm : mx with
    | some x => exact ⟨x, rfl⟩
    | none => simp [hm] at hFinite
  have hRef : firstReference p batch head row 1 = abiFloat p.scaleLog2Bits * maximum := by
    change abiFloat p.scaleLog2Bits * mx.getD 0 = _
    rw [hMax]
    rfl
  let sum := (2 : ℝ) ^ (-(abiFloat p.scaleLog2Bits * maximum)) *
    maskedBlockSum (p.keyCount batch row) 1 0 (weight p batch head row)
  change SoftmaxSumRun p batch head row 1
    (fun _ => mx.map (abiFloat p.scaleLog2Bits * ·))
    (fun _ => (2 : ℝ) ^ (-(mx.map (abiFloat p.scaleLog2Bits * ·)).getD 0) *
      maskedBlockSum (p.keyCount batch row) 1 0 (weight p batch head row)) at hInitial
  have hVisits : SoftmaxSumRun p batch head row 1
      (fun _ => some (abiFloat p.scaleLog2Bits * maximum)) (fun _ => sum) := by
    simpa only [hMax, Option.map_some, Option.getD_some, sum] using hInitial
  obtain ⟨t, leader, failed, hRun, ht⟩ :=
    firstRoundLoopTrace hp warp (by decide) (by decide) hBias hCap hPast hRound
  have hSplit : firstPlainSplit 1 biasCap = 0 := by unfold firstPlainSplit; omega
  have hBiased : firstBiasedRepeats 1 biasCap = 0 := by unfold firstBiasedRepeats; omega
  have hAt : At t 7605 ((1491, b32 0) :: firstLoopChoiceFacts 1 0 pastTile mx sum) := by
    simpa only [hSplit, hBiased, ite_true, hRef, mx, sum] using ht
  have hRegs := hAt.2.2.2.2
  refine ⟨t, (if laneOf l g = leader then j + 12 else j + 11) + failed + 1, maximum, sum,
    hVisits, hRef, hAt.1, ?_, ?_, hRun⟩
  · exact holds_lookup hRegs (by rfl)
  · have hValue : t.regs 7256 = some (scoreValue mx) := holds_lookup hRegs (by rfl)
    simpa [hMax, scoreValue, fl] using hValue

end
end PTX.Kernels.TmlFa4Fwd.Softmax
