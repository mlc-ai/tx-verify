-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkResult
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreSource
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTmemCells

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Assumption PTX.TcMma PTX.Proof PTX.Flow
open scoped BigOperators

noncomputable section

/-- The producer's column selected by one word of a softmax score load. -/
def firstScoreColumn (q : Fin 4) (word : Fin 32) : Fin 128 :=
  ⟨32*q.val+word.val, by have := q.isLt; have := word.isLt; omega⟩

/-- The exact QK dot product returned in one score word of the first block. -/
def firstScoreDot (p : Params) (l : Launch) (g batch head firstQ firstK : Nat)
    (q : Fin 4) (word : Fin 32) : ℝ :=
  ∑ d ∈ Finset.range 128, Mma.qkQuery p (firstQ+(tmemRow l g).val) head d *
    Mma.qkKey p batch head (firstK+(firstScoreColumn q word).val) d

private theorem firstScoreCell {l : Launch} {g h : Nat} (hCta : SameCta l h g)
    (stage : Fin 2) (q : Fin 4) (word : Fin 32) :
    tcDataCell l g .s32x32b (scoreAddress l g stage q) word.val =
      ⟨h/l.block, (tmemRow l g).val, scoreColumn stage + (firstScoreColumn q word).val⟩ := by
  have hCol : scoreColumn stage+32*q.val < 512 := by
    have hStage := scoreColumn_range stage
    have hQ := q.isLt
    omega
  rw [scoreAddress, tcDataCell_warp32 l g word.val hCol, hCta.2.2]
  simp only [tmemRow, firstScoreColumn, Nat.add_assoc]

private theorem scoreReadColumn (l : Launch) (g : Nat) (stage : Fin 2)
    (q : Fin 4) (word : Fin 32) :
    (tcDataCell l g .s32x32b (scoreAddress l g stage q) word.val).column =
      scoreColumn stage+(firstScoreColumn q word).val := by
  have hCol : scoreColumn stage+32*q.val < 512 := by
    have hStage := scoreColumn_range stage
    have hQ := q.isLt
    omega
  rw [scoreAddress, tcDataCell_warp32 l g word.val hCol]
  simp only [firstScoreColumn, Nat.add_assoc]

private theorem mmaWriteColumnRange {X : Execution} {other : EvId} {s : OperandSpec}
    {base : Nat} {acc : Bool} {mask : List Nat} {cell : Cell}
    (hIssue : X.MmaIssue other base s acc mask)
    (hBase : base < 2^16) (hM : s.descriptor.m = 128) (hN : s.descriptor.n = 128)
    (hGroup : s.descriptor.group = .one) (hW : X.MmaCell other cell) :
    base ≤ cell.column ∧ cell.column < base+128 := by
  obtain ⟨_, _, _, _, row, col, ⟨_, hMma⟩, hWrite⟩ := hW
  obtain ⟨_, he⟩ := hIssue
  rw [he] at hMma
  cases hMma
  have hCell := writeCell_resultCell hWrite
  unfold resultCell at hCell
  dsimp only at hCell
  split at hCell
  · rename_i hValid
    have hCol : col < 128 := hN ▸ hValid.2.2.2.1
    simp only [hM, hGroup, CtaGroup.size, Nat.mul_one, ↓reduceIte, Option.some.injEq] at hCell
    subst cell
    simp only [Nat.mod_eq_of_lt hBase]
    omega
  · cases hCell

variable {l : Launch} {X : Execution}

/-- A QK issue in the other phase's physical stage cannot overwrite this score word. -/
theorem scoreOtherStageDisjoint {other : EvId} (g : Nat) (stage writtenStage : Fin 2) (q : Fin 4)
    (word : Fin 32) {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hDesc : s.descriptor = qkDescriptor)
    (hIssue : X.MmaIssue other (scoreColumn writtenStage) s acc mask)
    (hDifferent : writtenStage ≠ stage) :
    ¬ X.MmaCell other (tcDataCell l g .s32x32b (scoreAddress l g stage q) word.val) := by
  intro hW
  have hWritten := scoreColumn_range writtenStage
  have hCol := mmaWriteColumnRange hIssue (by omega) (by rw [hDesc]; rfl)
    (by rw [hDesc]; rfl) (by rw [hDesc]; rfl) hW
  rw [scoreReadColumn] at hCol
  have hK := (firstScoreColumn q word).isLt
  have hn : writtenStage.val ≠ stage.val := fun e => hDifferent (Fin.ext e)
  unfold scoreColumn at hCol
  omega

/-- The PV accumulator always occupies the upper half of Tensor Memory, outside both score tiles. -/
theorem scorePvDisjoint {other : EvId} (g : Nat) (stage writtenStage : Fin 2) (q : Fin 4)
    (word : Fin 32) {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hDesc : s.descriptor = pvDescriptor)
    (hIssue : X.MmaIssue other (outputColumn writtenStage) s acc mask) :
    ¬ X.MmaCell other (tcDataCell l g .s32x32b (scoreAddress l g stage q) word.val) := by
  intro hW
  have hWritten := outputColumn_range writtenStage
  have hCol := mmaWriteColumnRange hIssue (by omega) (by rw [hDesc]; rfl)
    (by rw [hDesc]; rfl) (by rw [hDesc]; rfl) hW
  rw [scoreReadColumn] at hCol
  have hK := (firstScoreColumn q word).isLt
  have hApart := score_output_apart stage writtenStage
  omega

/-- The consumer row is the lane's position within its 128-thread softmax stage. -/
theorem scoreRow_eq_tid (l : Launch) (g : Nat) :
    (tmemRow l g).val = g % l.block % 128 := by
  simp only [tmemRow, laneBase, laneOf]
  omega

/-- Matching score/probability rows in the same CTA and physical stage identify the same lane. -/
theorem scoreSameLane {l : Launch} {g h : Nat} (hCta : SameCta l g h)
    (hStage : g % l.block / 128 = h % l.block / 128)
    (hRow : tmemRow l g = tmemRow l h) : g = h := by
  have hR := congrArg Fin.val hRow
  rw [scoreRow_eq_tid, scoreRow_eq_tid] at hR
  have hTid : g % l.block = h % l.block := by omega
  have hg := Nat.div_add_mod g l.block
  have hh := Nat.div_add_mod h l.block
  rw [hCta.2.2, hTid] at hg
  exact hg.symm.trans hh

/-- A valid probability store can share a score cell only for the same CTA, row and
physical stage. The stages reuse the upper 64 columns of their own score tiles. -/
theorem scoreProbabilityDisjoint {g h write : Nat} (stage writtenStage : Fin 2)
    (q writtenQuarter : Fin 4) (word : Fin 32) {vals : List Value}
    (hStore : X.TSt (h, write) (probabilityAddress l h writtenStage writtenQuarter) vals .s32x32b)
    (hLength : vals.length = 16)
    (hApart : g/l.block ≠ h/l.block ∨ tmemRow l g ≠ tmemRow l h ∨ stage ≠ writtenStage) :
    ¬ StoreCell l X (h, write)
      (tcDataCell l g .s32x32b (scoreAddress l g stage q) word.val) := by
  intro hBad
  obtain ⟨_, _, _, k, ⟨_, he'⟩, hk, hCell⟩ := hBad
  obtain ⟨_, he⟩ := hStore
  rw [he] at he'
  cases he'
  have hWQ := writtenQuarter.isLt
  have hR := probabilityColumn_range writtenStage
  have hB := scoreColumn_range writtenStage
  have hW : probabilityColumn writtenStage+16*writtenQuarter.val < 512 := by omega
  have hQ := q.isLt
  have hB' := scoreColumn_range stage
  have hG : scoreColumn stage+32*q.val < 512 := by omega
  rw [scoreAddress, probabilityAddress, tcDataCell_warp32 l g word.val hG,
    tcDataCell_warp32 l h k hW] at hCell
  have hCta := congrArg Cell.cta hCell
  have hRow : tmemRow l g = tmemRow l h := Fin.ext (congrArg Cell.lane hCell)
  have hCol := congrArg Cell.column hCell
  have hWord := word.isLt
  have hSame : stage = writtenStage := by
    have hKnown := (scoreColumn_distinct
      (s := stage) (t := writtenStage) (i := firstScoreColumn q word)
      (j := ⟨64+16*writtenQuarter.val+k, by omega⟩))
    exact (hKnown (by
      simp only [firstScoreColumn, probabilityColumn] at hCol ⊢
      change scoreColumn stage+32*q.val+word.val =
        scoreColumn writtenStage+64+16*writtenQuarter.val+k at hCol
      omega)).1
  exact hApart.elim (fun hn => hn hCta) (fun a => a.elim (fun hn => hn hRow) (fun hn => hn hSame))

/-- The preceding fragment writes the exact accumulator cell used by this score word.
The remaining conditions cover cross-block writes and allocation liveness. -/
theorem firstScoreAccumulatorSource {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {producer consumer start use : Nat} (hCta : SameCta l producer consumer)
    (hIssues : ∀ step : Fin 8, X.get (producer, start+step.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) step use))
    (q : Fin 4) (word : Fin 32) (step : Fin 8) (hStep : step.val ≠ 0)
    (hOutside : ∀ other,
      let cell := tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val
      (X.MmaCell other cell ∨ StoreCell l X other cell) →
      (∀ k : Fin 8, other ≠ (producer, start+k.val)) →
      WriteBefore l X other (producer, start+(step.val-1)) ∨
        ReadBefore l X .acc (producer, start+step.val) other)
    (hLive : SourceLive l X (producer, start+(step.val-1)) (producer, start+step.val)
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val)) :
    ReadSource l X .acc (producer, start+(step.val-1)) (producer, start+step.val)
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val) := by
  let cell := tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val
  let block := firstQkBlock stage
  let prev : Fin 8 := ⟨step.val-1, by have := step.isLt; omega⟩
  let operand := Mma.qkOperands l producer block prev use
  let row := tmemRow l consumer
  let col := firstScoreColumn q word
  have hWrite : X.MmaCell (producer, start+prev.val) cell := by
    refine ⟨scoreColumn (Mma.qkStage block), operand, _, _, row.val, col.val,
      ⟨_, hIssues prev⟩, ?_⟩
    have h := writeCell_no_mask_128 (s := operand) rfl rfl row.isLt row.isLt
      (qkResultCell (s := operand) rfl (Mma.qkStage block) row col)
    have hProducer : operand.lowCta = producer/l.block := rfl
    simpa only [block, firstQkBlock_stage, cell, row, col, hProducer,
      firstScoreCell hCta stage q word] using h
  exact firstQkAccumulatorSource hX hCta.1 stage step hStep hIssues cell hWrite hOutside hLive

/-- The eight observed QK fragments produce the exact mathematical score for one consumer cell. -/
theorem firstQkScoreResult {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {producer consumer start use batch head firstQ firstK : Nat}
    (hCta : SameCta l producer consumer)
    (hIssues : ∀ step : Fin 8, X.get (producer, start+step.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) step use))
    (hOperands : ∀ step : Fin 8, ∃ ops, X.async.mmaOperands (producer, start+step.val) = some ops)
    (q : Fin 4) (word : Fin 32)
    (hIn : Mma.QkCellInputs p l X producer (firstQkBlock stage) use batch head firstQ firstK
      (tmemRow l consumer) (firstScoreColumn q word) (fun step => (producer, start+step.val)))
    (hPrior : ∀ step : Fin 8, step.val ≠ 0 →
      ReadSource l X .acc (producer, start+(step.val-1)) (producer, start+step.val)
        (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val)) :
    Result l Assumptions.all X (producer, start+7)
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val)
      (.float .f32 (firstScoreDot p l consumer batch head firstQ firstK q word)) := by
  let block := firstQkBlock stage
  let issues := fun s : Fin 8 => (producer, start+s.val)
  have hIssue (step : Fin 8) : X.MmaIssue (issues step)
      (scoreColumn (Mma.qkStage block)) (Mma.qkOperands l producer block step use)
      (decide (0 < step.val)) (List.replicate 4 0) := by
    refine ⟨Mma.qkPc block+step.val, ?_⟩
    simpa only [Mma.qkIssueEvent, Nat.pos_iff_ne_zero] using hIssues step
  have hCell := firstScoreCell hCta stage q word
  have hPrev (step : Fin 8) (hStep : step.val ≠ 0) :
      ReadSource l X .acc (issues ⟨step.val-1, by have := step.isLt; omega⟩) (issues step)
        ⟨producer/l.block, (tmemRow l consumer).val,
          scoreColumn (Mma.qkStage block) + (firstScoreColumn q word).val⟩ := by
    simpa only [block, firstQkBlock_stage, ← hCell] using hPrior step hStep
  have hResult := Mma.qkCellResult hX block (tmemRow l consumer) (firstScoreColumn q word)
    issues hIn hIssue hOperands hPrev
  simpa only [block, firstQkBlock_stage, issues, firstScoreDot, ← hCell,
    show (7 : Fin 8).val = 7 from rfl] using hResult

/-- The executed pack has the two finite FP32 dot products as its FMA operands. -/
theorem firstPackedScoreValues {stage : Fin 2} {g j : Nat} {t : TState} {vals : Fin 4 → List Value}
    (hScores : FirstScores l X stage g j t vals) (score : Fin 4 → Fin 32 → ℝ)
    (hVals : ∀ (q : Fin 4) (word : Fin 32), (vals q)[word.val]? = some (.float .f32 (score q word)))
    (q : Fin 4) (k : Fin 16) :
    let lo : Fin 32 := ⟨2*k.val, by have := k.isLt; omega⟩
    let hi : Fin 32 := ⟨2*k.val+1, by have := k.isLt; omega⟩
    readERealPair l g t (.reg (firstScorePairReg q k.val)) =
      some (.ok ((score q lo : EReal), (score q hi : EReal))) := by
  dsimp only
  let lo : Fin 32 := ⟨2*k.val, by have := k.isLt; omega⟩
  let hi : Fin 32 := ⟨2*k.val+1, by have := k.isLt; omega⟩
  have hLow := hVals q lo
  have hHigh := hVals q hi
  have hReg := hScores.2 q k.val k.isLt
  change (vals q)[2*k.val]? = some (.float .f32 (score q lo)) at hLow
  change (vals q)[2*k.val+1]? = some (.float .f32 (score q hi)) at hHigh
  simp only [List.getD_eq_getElem?_getD, hLow, hHigh, Option.getD_some] at hReg
  exact readERealPair_reg hReg rfl rfl

end
end PTX.Kernels.TmlFa4Fwd.Softmax
