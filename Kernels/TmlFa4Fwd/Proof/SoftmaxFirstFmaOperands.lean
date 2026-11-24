-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasWordValues
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreValues
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasFmaEntry
import Kernels.TmlFa4Fwd.Proof.ResultGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

/-- Within each loaded Bias vector, the decoded destination registers decrease with column. -/
def firstBiasColumnRegister (col : Nat) : Nat :=
  793 + 8 * (col / 8) - col % 8

/-- At a decoded first-round Bias source register, recover the corresponding logical element. -/
def firstBiasRegisterValue (bias : Nat → Option ℝ) (r : Nat) : Option ℝ :=
  bias (8 * ((r - 786) / 8) + (7 - (r - 786) % 8))

/-- A QK pair register holds its consecutive logical score columns from low to high. -/
def firstQkRegisterValue (dot : Nat → ℝ) (r : Nat) : ℝ × ℝ :=
  (dot (2 * (r - 7303)), dot (2 * (r - 7303) + 1))

private theorem firstBiasRegisterInverse {col : Nat}
    (bias : Nat → Option ℝ) :
    firstBiasRegisterValue bias (firstBiasColumnRegister col) = bias col := by
  unfold firstBiasRegisterValue firstBiasColumnRegister
  apply congrArg bias
  have hSub : 793 + 8 * (col / 8) - col % 8 - 786 =
      8 * (col / 8) + (7 - col % 8) := by omega
  rw [hSub]
  omega

/-- The actual vector unpack supplies the original value in every logical Bias column. -/
theorem firstBiasRegistersOfWords {t : TState} (bias : Nat → Option ℝ)
    (hUnpacked : ∀ i : Fin 16, BiasUnpacked false i t (fun k =>
      biasLoadWord (bias (8 * i.val + 2 * k)) (bias (8 * i.val + 2 * k + 1)))) :
    ∀ col < 128, t.regs (firstBiasColumnRegister col) = some (biasValue (bias col)) := by
  intro col hCol
  let vector : Fin 16 := ⟨col / 8, by omega⟩
  let word := col % 8 / 2
  obtain ⟨hLo, hHi⟩ := hUnpacked vector word (by dsimp [word]; omega)
  rw [splitBiasLoadWord] at hLo hHi
  by_cases hEven : col % 2 = 0
  · have hCol' : 8 * vector.val + 2 * word = col := by dsimp [vector, word]; omega
    have hReg : (biasUnpackRegs false vector word).1 = firstBiasColumnRegister col := by
      simp only [biasUnpackRegs, biasUnpackTop, Bool.false_eq_true, ite_false,
        firstBiasColumnRegister, vector, word]
      omega
    simpa only [hReg, hCol'] using hLo
  · have hCol' : 8 * vector.val + 2 * word + 1 = col := by dsimp [vector, word]; omega
    have hReg : (biasUnpackRegs false vector word).2 = firstBiasColumnRegister col := by
      simp only [biasUnpackRegs, biasUnpackTop, Bool.false_eq_true, ite_false,
        firstBiasColumnRegister, vector, word]
      omega
    simpa only [hReg, hCol'] using hHi

/-- All actual first score packs match the two logical QK values read for their columns. -/
theorem firstQkRegistersOfWords {l : Launch} {X : Execution} {stage : Fin 2}
    {g j : Nat} {t : TState} {vals : Fin 4 → List Value}
    (hScores : FirstScores l X stage g j t vals) (dot : Nat → ℝ)
    (hVals : ∀ (q : Fin 4) (word : Fin 32),
      (vals q)[word.val]? = some (.float .f32 (dot (32 * q.val + word.val)))) :
    ∀ pair < 64, readERealPair l g t (.reg (7303 + pair)) =
      some (.ok ((dot (2 * pair) : EReal), (dot (2 * pair + 1) : EReal))) := by
  intro pair hPair
  let q : Fin 4 := ⟨pair / 16, by omega⟩
  let k : Fin 16 := ⟨pair % 16, by omega⟩
  have hRead := firstPackedScoreValues hScores (fun q word => dot (32 * q.val + word.val))
    hVals q k
  have hReg : firstScorePairReg q k.val = 7303 + pair := by
    dsimp [firstScorePairReg, q, k]
    omega
  have hLo : 32 * q.val + 2 * k.val = 2 * pair := by dsimp [q, k]; omega
  have hHi : 32 * q.val + (2 * k.val + 1) = 2 * pair + 1 := by rw [← Nat.add_assoc, hLo]
  simpa only [hReg, hLo, hHi] using hRead

private def firstBiasItemInOrder (item : BiasAffineItem) : Bool :=
  let pair := item.qk - 7303
  (7303 ≤ item.qk) && (pair < 64) &&
    (item.biasLow == firstBiasColumnRegister (2 * pair)) &&
    (item.biasHigh == firstBiasColumnRegister (2 * pair + 1))

private theorem firstBiasItemsInOrder : (biasBodyItems false).all firstBiasItemInOrder = true := by
  kernel_rfl

/-- The actual Bias unpacks and QK packs supply every source of the first FMA sequence
with its logical value. -/
theorem firstFmaOperandsOfWords {l : Launch} {X : Execution} {stage : Fin 2}
    {g j : Nat} {t : TState} {vals : Fin 4 → List Value}
    (hScores : FirstScores l X stage g j t vals) (bias : Nat → Option ℝ) (dot : Nat → ℝ)
    (hVals : ∀ (q : Fin 4) (word : Fin 32),
      (vals q)[word.val]? = some (.float .f32 (dot (32 * q.val + word.val))))
    (hUnpacked : ∀ i : Fin 16, BiasUnpacked false i t (fun k =>
      biasLoadWord (bias (8 * i.val + 2 * k)) (bias (8 * i.val + 2 * k + 1)))) :
    let biases := firstBiasRegisterValue bias
    let qk := firstQkRegisterValue dot
    t.regs 793 = some (biasValue (biases 793)) ∧
    t.regs 792 = some (biasValue (biases 792)) ∧
    readERealPair l g t (.reg 7303) = some (.ok (((qk 7303).1 : ℝ), ((qk 7303).2 : ℝ))) ∧
    ∀ i ∈ biasBodyItems false,
      t.regs i.biasLow = some (biasValue (biases i.biasLow)) ∧
      t.regs i.biasHigh = some (biasValue (biases i.biasHigh)) ∧
      readERealPair l g t (.reg i.qk) = some (.ok (((qk i.qk).1 : ℝ), ((qk i.qk).2 : ℝ))) := by
  dsimp only
  have hBias := firstBiasRegistersOfWords bias hUnpacked
  have hDot := firstQkRegistersOfWords hScores dot hVals
  refine ⟨hBias 0 (by decide), hBias 1 (by decide), hDot 0 (by decide), ?_⟩
  intro item hItem
  have hOrder := List.all_eq_true.mp firstBiasItemsInOrder item hItem
  simp only [firstBiasItemInOrder, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hOrder
  obtain ⟨⟨⟨hBase, hCount⟩, hLo⟩, hHi⟩ := hOrder
  let pair := item.qk - 7303
  have hL : 2 * pair < 128 := by omega
  have hH : 2 * pair + 1 < 128 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hLo, firstBiasRegisterInverse]
    exact hBias _ hL
  · rw [hHi, firstBiasRegisterInverse]
    exact hBias _ hH
  · have hReg : 7303 + pair = item.qk := Nat.add_sub_of_le hBase
    simpa only [hReg, firstQkRegisterValue, pair] using hDot pair hCount

private theorem firstBiasItemQkOrder :
    (biasBodyItems false).map (·.qk) = (List.range 63).map (fun i => 7304 + i) := by
  kernel_rfl

private theorem firstBiasItemForPair {pair : Nat} (hPos : 0 < pair) (hPair : pair < 64) :
    ∃ i, (biasBodyItems false)[pair - 1]? = some i ∧ i.qk = 7303 + pair := by
  have hIdx : pair - 1 < 63 := by omega
  have hGet := congrArg (fun ns : List Nat => ns[pair - 1]?) firstBiasItemQkOrder
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_range hIdx] at hGet
  cases hi : (biasBodyItems false)[pair - 1]? with
  | none => simp [hi] at hGet
  | some i =>
    have hReg : i.qk = 7304 + (pair - 1) := by simpa only [hi, Option.map_some, Option.some.injEq]
      using hGet
    exact ⟨i, rfl, by omega⟩

/-- The first Bias affine results use the same column order as the loads on both sides. -/
theorem firstBiasLogitOfColumns (scale : ℝ) (bias : Nat → Option ℝ) (dot : Nat → ℝ)
    {col : Nat} (hCol : col < 128) :
    firstBiasLogit scale (firstBiasRegisterValue bias) (firstQkRegisterValue dot) col =
      affineScore scale (dot col) (bias col) := by
  let pair := col / 2
  by_cases hZero : pair = 0
  · have hFirst : col = 0 ∨ col = 1 := by dsimp [pair] at hZero; omega
    rcases hFirst with rfl | rfl <;> rfl
  have hp : pair < 64 := by dsimp [pair]; omega
  obtain ⟨i, hi, hReg⟩ := firstBiasItemForPair (Nat.pos_of_ne_zero hZero) hp
  have hOrder := List.all_eq_true.mp firstBiasItemsInOrder i (List.mem_of_getElem? hi)
  simp only [firstBiasItemInOrder, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hOrder
  obtain ⟨⟨⟨_, _⟩, hLo⟩, hHi⟩ := hOrder
  rw [hReg, Nat.add_sub_cancel_left] at hLo hHi
  have hPair : firstBiasPairValue scale (firstBiasRegisterValue bias) (firstQkRegisterValue dot)
      pair = (affineScore scale (dot (2 * pair)) (bias (2 * pair)),
        affineScore scale (dot (2 * pair + 1)) (bias (2 * pair + 1))) := by
    simp only [firstBiasPairValue, hZero, ite_false, hi, hLo, hHi, firstBiasRegisterInverse, hReg,
      firstQkRegisterValue, Nat.add_sub_cancel_left]
  unfold firstBiasLogit
  change (if col % 2 = 0 then _ else _) = _
  simp only [← show pair = col / 2 from rfl, hPair]
  by_cases hEven : col % 2 = 0
  · have hIndex : 2 * pair = col := by dsimp [pair]; omega
    simp only [hEven, ite_true, hIndex]
  · have hIndex : 2 * pair + 1 = col := by dsimp [pair]; omega
    simp only [hEven, ite_false, hIndex]

/-- The actual score loads and Bias unpacks at the fence determine the first numerical
round once their logical source columns are known. -/
theorem firstRoundFromFenceOperands {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j batch head base blocks biasCap pastTile scoreStart : Nat}
    {t : TState} {scores : Fin 4 → List Value} (bias : Nat → Option ℝ)
    (hb : batch < p.batch) (hh : head < p.heads)
    (hRow : 128 * base + (g % l.block) % 128 < p.qLength batch)
    (hBlocks : 128 * (blocks - 1) ≤ p.kLength batch)
    (ht : At t 3581 (biasFenceFacts l g warp false))
    (hGeometry : Holds t.regs
      [(1229, b32 (blocks - 1)), (1224, b32 (p.kLength batch)),
        (2868, b32 (128 * base)), (1223, maskSigned (-(p.qLength batch : Int)))])
    (hScores : FirstScores l X (stageOf warp) g scoreStart t scores)
    (hDots : ∀ (q : Fin 4) (word : Fin 32),
      (scores q)[word.val]? = some (.float .f32
        (firstScoreDot p l g batch head (p.qOffset batch + 128 * base) (128 * (blocks - 1))
          q word)))
    (hUnpacked : ∀ i : Fin 16, BiasUnpacked false i t (fun k =>
      biasLoadWord (bias (8 * i.val + 2 * k)) (bias (8 * i.val + 2 * k + 1))))
    (hBias : ∀ col < 128,
      let row := 128 * base + (g % l.block) % 128
      let key := visitKey blocks 0 col
      let bc := p.biasColumn batch row key
      key < p.keyCount batch row → 0 ≤ bc ∧ bc < 1280 ∧
        bias col = p.bias (p.qOffset batch + row) head bc.toNat)
    (hLoop : Holds t.regs (firstLoopGeometry blocks biasCap pastTile))
    (hBar : t.regs 5127 = some (b32 (3 + warp.val)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let pos := if laneOf l g = 0 then j + 3 else j + 2
    X.get (g, j) = some ⟨3581, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, j + 1) = some ⟨3583, .bar (11 + (stageOf warp).val) (some 128) .sync⟩ ∧
      (laneOf l g = 0 → X.get (g, j + 2) = some
        ⟨3590, .arrive (signalLoc l g (stageOf warp) 0) 0 1 true .cta⟩) ∧
      FirstRoundProgress p l X warp g pos batch head (128 * base + (g % l.block) % 128)
        blocks biasCap pastTile := by
  let row := 128 * base + (g % l.block) % 128
  let dot := fun c => ∑ d ∈ Finset.range 128,
    Mma.qkQuery p (p.qOffset batch + row) head d *
      Mma.qkKey p batch head (visitKey blocks 0 c) d
  have hWords (q : Fin 4) (word : Fin 32) :
      (scores q)[word.val]? = some (.float .f32 (dot (32 * q.val + word.val))) := by
    simpa only [firstScoreDot, firstScoreColumn, scoreRow_eq_tid, visitKey, Nat.sub_zero,
      dot, row, Nat.add_assoc] using hDots q word
  obtain ⟨hLo, hHi, hDot, hInputs⟩ := firstFmaOperandsOfWords hScores bias dot hWords hUnpacked
  refine firstRoundFromBiasFence hp warp (firstBiasRegisterValue bias) (firstQkRegisterValue dot)
    hb (by omega) hBlocks ht hGeometry hLo hHi hDot hInputs ?_ hLoop hBar hRun
  intro col hc
  dsimp only
  intro hKey
  obtain ⟨hLow, hHigh, hVal⟩ := hBias col hc hKey
  rw [firstBiasLogitOfColumns _ _ _ hc, hVal]
  have hQ : p.qOffset batch + row < p.totalQ := hp.packedRow_lt hb hRow
  have hK : visitKey blocks 0 col < p.kLength batch :=
    hKey.trans_le (Nat.min_le_left ..)
  have hDotLive : dot col = queryKeyDot p batch head row (visitKey blocks 0 col) := by
    simp only [dot, queryKeyDot, Mma.qkQuery, Mma.qkKey, ite_eq_left hQ, ite_eq_left hK]
  rw [hDotLive, biasedLogit_eq hp hb hRow hh hLow hHigh]
  exact ite_eq_left hKey

end
end PTX.Kernels.TmlFa4Fwd.Softmax
