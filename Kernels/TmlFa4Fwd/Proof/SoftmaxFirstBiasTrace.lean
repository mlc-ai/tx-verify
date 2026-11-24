-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

/-- The first pair precedes the 63 regularly laid out bias affine items. -/
def firstBiasPairValue (scale : ℝ) (bias : Nat → Option ℝ) (qk : Nat → ℝ × ℝ)
    (pair : Nat) : Option ℝ × Option ℝ :=
  if pair = 0 then
    (affineScore scale (qk 7303).1 (bias 793), affineScore scale (qk 7303).2 (bias 792))
  else match (biasBodyItems false)[pair-1]? with
    | none => (none, none)
    | some i => (affineScore scale (qk i.qk).1 (bias i.biasLow),
        affineScore scale (qk i.qk).2 (bias i.biasHigh))

def firstBiasLogit (scale : ℝ) (bias : Nat → Option ℝ) (qk : Nat → ℝ × ℝ)
    (col : Nat) : Option ℝ :=
  let value := firstBiasPairValue scale bias qk (col / 2)
  if col % 2 = 0 then value.1 else value.2

private theorem firstBiasColumns (scale : ℝ) (bias : Nat → Option ℝ) (qk : Nat → ℝ × ℝ)
    (group pair : Nat) :
    (firstBiasLogit scale bias qk (32 * group + 2 * pair),
     firstBiasLogit scale bias qk (32 * group + 2 * pair + 1)) =
      firstBiasPairValue scale bias qk (16 * group + pair) := by
  have hL : (32 * group + 2 * pair) / 2 = 16 * group + pair := by omega
  have hH : (32 * group + 2 * pair + 1) / 2 = 16 * group + pair := by omega
  have hE : (32 * group + 2 * pair) % 2 = 0 := by omega
  have hO : (32 * group + 2 * pair + 1) % 2 = 1 := by omega
  simp only [firstBiasLogit, hL, hH, hE, hO, ite_true, Nat.one_ne_zero, ite_false]

private theorem firstBiasBodyRegs :
    (biasBodyItems false).map (·.result) = (List.range 63).map (fun i => 7899 + 2*i) := by
  kernel_rfl

private theorem firstBiasItem {i : Nat} (hi : i < 63) :
    ∃ it, (biasBodyItems false)[i]? = some it ∧ it.result = 7899 + 2*i := by
  have h : ((biasBodyItems false).map (·.result))[i]? = some (7899 + 2*i) := by
    rw [firstBiasBodyRegs, List.getElem?_map, List.getElem?_range hi]
    rfl
  rw [List.getElem?_map] at h
  cases hI : (biasBodyItems false)[i]? with
  | none => simp [hI] at h
  | some it => exact ⟨it, rfl, by simpa [hI] using h⟩

private theorem firstBiasBodyReads :
    (biasBodyItems false).all (fun it =>
      it.reads.all (fun r => !(r ∈ [3088, 3089, 7895, 7896, 7897]))) = true := by
  decide +kernel

private theorem firstBiasInitKept :
    7897 ∉ (biasBodyItems false).flatMap BiasAffineItem.writes := by decide +kernel

section
variable {l : Launch} {g : Nat}

/-- The complete first bias FMA pass consumes the actual ABI scale word and writes the
pairs consumed by the causal mask, in the decoded key order. -/
theorem firstBiasScoreRun {t : TState} {bits : Nat} {scale : ℚ} (hs : 0 < scale)
    (hBits : bits < 2^32) (hDecode : f32Value bits = some scale) (bias : Nat → Option ℝ)
    (qk : Nat → ℝ × ℝ) (ht : At t 3593 []) (hLo : t.regs 793 = some (biasValue (bias 793)))
    (hHi : t.regs 792 = some (biasValue (bias 792))) (hScale : t.regs 7135 = some (b32 bits))
    (hDot : readERealPair l g t (.reg 7303) = some (.ok (((qk 7303).1 : ℝ), ((qk 7303).2 : ℝ))))
    (hInputs : ∀ i ∈ biasBodyItems false,
      t.regs i.biasLow = some (biasValue (bias i.biasLow)) ∧
      t.regs i.biasHigh = some (biasValue (bias i.biasHigh)) ∧
      readERealPair l g t (.reg i.qk) = some (.ok (((qk i.qk).1 : ℝ), ((qk i.qk).2 : ℝ)))) :
    ∃ u, At u 3850 [] ∧ run kernel Assumptions.all l g 257 t = some u ∧
      firstMaskInputs u (firstBiasLogit (scale : ℝ) bias qk) ∧
      ∀ r ∉ [3088, 3089, 7895, 7896, 7897] ++
        (biasBodyItems false).flatMap BiasAffineItem.writes, u.regs r = t.regs r := by
  obtain ⟨v, hv, hvRun, hPackedScale, hvFrame⟩ :=
    firstBiasPairBitsRun hs hBits hDecode ht hLo hHi hScale hDot
  have hvInputs (i : BiasAffineItem) (hi : i ∈ biasBodyItems false) :
      v.regs i.biasLow = some (biasValue (bias i.biasLow)) ∧
      v.regs i.biasHigh = some (biasValue (bias i.biasHigh)) ∧
      readERealPair l g v (.reg i.qk) = some (.ok (((qk i.qk).1 : ℝ), ((qk i.qk).2 : ℝ))) := by
    have hKeep (r : Nat) (hm : r ∈ i.reads) : v.regs r = t.regs r := by
      have h := List.all_eq_true.mp (List.all_eq_true.mp firstBiasBodyReads i hi) r hm
      exact hvFrame r (by simpa using h)
    obtain ⟨ha, hb, hc⟩ := hInputs i hi
    refine ⟨(hKeep _ (by simp [BiasAffineItem.reads])).trans ha,
      (hKeep _ (by simp [BiasAffineItem.reads])).trans hb, ?_⟩
    simpa only [readERealPair, readValue, readReg, hKeep i.qk (by simp [BiasAffineItem.reads])]
      using hc
  have hsReal : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hs
  obtain ⟨u, hu, huRun, huFrame, huOut⟩ :=
    biasBodyRun false hsReal bias qk (hv.mono trivial) hPackedScale hvInputs
  refine ⟨u,hu,run_comp hvRun huRun,?_,fun r hN => ?_⟩
  · intro group pair hp
    have hg := group.isLt
    let idx := 16 * group.val + pair
    have hIdx : idx < 64 := by dsimp [idx]; omega
    let value := firstBiasPairValue (scale : ℝ) bias qk idx
    have hPair : u.regs (7897 + 2*idx) =
        some (.pair (scoreValue value.1) (scoreValue value.2)) := by
      by_cases hz : idx = 0
      · rw [hz]
        simpa [value, hz, firstBiasPairValue] using
          (huFrame 7897 firstBiasInitKept).trans hv.2.2.2.2.1
      · obtain ⟨it, hI, hReg⟩ := firstBiasItem (i := idx-1) (by omega)
        have hOut := huOut it (List.mem_of_getElem? hI)
        have hDst : it.result = 7897 + 2*idx := by omega
        rw [hDst] at hOut
        simpa only [value, firstBiasPairValue, ite_eq_right hz, hI] using hOut
    have hColumns := firstBiasColumns (scale : ℝ) bias qk group pair
    have hReg : (firstMaskPairRegs group pair).packed = 7897 + 2*idx := by
      unfold firstMaskPairRegs
      change 7897 + 32 * group.val + 2 * pair = _
      dsimp [idx]
      omega
    have hlo : firstBiasLogit (scale : ℝ) bias qk (32 * group.val + 2 * pair) = value.1 :=
      congrArg Prod.fst hColumns
    have hhi : firstBiasLogit (scale : ℝ) bias qk (32 * group.val + 2 * pair + 1) = value.2 :=
      congrArg Prod.snd hColumns
    rw [hReg, hlo, hhi]
    exact hPair
  · exact (huFrame _ (fun hm => hN (List.mem_append_right _ hm))).trans
      (hvFrame _ (fun hm => hN (List.mem_append_left _ hm)))

/-- The complete first bias FMA pass consumes the actual ABI scale word and writes the
pairs consumed by the causal mask, in the decoded key order. -/
theorem firstBiasScoreTrace {t : TState} {es : List Event} {bits : Nat} {scale : ℚ} (hs : 0 < scale)
    (hBits : bits < 2^32) (hDecode : f32Value bits = some scale) (bias : Nat → Option ℝ)
    (qk : Nat → ℝ × ℝ) (ht : At t 3593 []) (hLo : t.regs 793 = some (biasValue (bias 793)))
    (hHi : t.regs 792 = some (biasValue (bias 792))) (hScale : t.regs 7135 = some (b32 bits))
    (hDot : readERealPair l g t (.reg 7303) = some (.ok (((qk 7303).1 : ℝ), ((qk 7303).2 : ℝ))))
    (hInputs : ∀ i ∈ biasBodyItems false,
      t.regs i.biasLow = some (biasValue (bias i.biasLow)) ∧
      t.regs i.biasHigh = some (biasValue (bias i.biasHigh)) ∧
      readERealPair l g t (.reg i.qk) = some (.ok (((qk i.qk).1 : ℝ), ((qk i.qk).2 : ℝ))))
    (hr : Run kernel Assumptions.all l g t es none) :
    ∃ u, At u 3850 [] ∧ Run kernel Assumptions.all l g u es none ∧
      firstMaskInputs u (firstBiasLogit (scale : ℝ) bias qk) ∧
      ∀ r ∉ [3088, 3089, 7895, 7896, 7897] ++
        (biasBodyItems false).flatMap BiasAffineItem.writes, u.regs r = t.regs r := by
  obtain ⟨u,hu,hRun,hScores,hFrame⟩ :=
    firstBiasScoreRun hs hBits hDecode bias qk ht hLo hHi hScale hDot hInputs
  exact ⟨u,hu,hr.after_local (run_rtg hRun),hScores,hFrame⟩
end

private theorem firstBiasCarryAudit :
    ∀ r ∈ [1229, 1224, 2868, 1223, 1225, 1226, 1228, 1062, 2535, 7132, 5127],
      r ∉ [3088, 3089, 7895, 7896, 7897] ++
        (biasBodyItems false).flatMap BiasAffineItem.writes := by decide +kernel

/-- The first numerical round begins with the actual loaded BF16 biases and QK pairs.
Each live affine score is related to the mathematical logit supplied by the score stage. -/
theorem firstRoundFromBiasReady {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j batch head base blocks biasCap pastTile : Nat}
    {t : TState} (bias : Nat → Option ℝ) (qk : Nat → ℝ × ℝ)
    (hb : batch < p.batch)
    (hRow : 128 * base + (g % l.block) % 128 < p.qLength batch + 256)
    (hBlocks : 128 * (blocks - 1) ≤ p.kLength batch)
    (ht : At t 3593
      [(1229, b32 (blocks-1)), (1224, b32 (p.kLength batch)),
        (2868, b32 (128 * base)), (1223, maskSigned (-(p.qLength batch : Int)))])
    (hLo : t.regs 793 = some (biasValue (bias 793)))
    (hHi : t.regs 792 = some (biasValue (bias 792)))
    (hScale : t.regs 7135 = some (b32 p.invScaleBits))
    (hDot : readERealPair l g t (.reg 7303) =
      some (.ok (((qk 7303).1 : ℝ), ((qk 7303).2 : ℝ))))
    (hInputs : ∀ i ∈ biasBodyItems false,
      t.regs i.biasLow = some (biasValue (bias i.biasLow)) ∧
      t.regs i.biasHigh = some (biasValue (bias i.biasHigh)) ∧
      readERealPair l g t (.reg i.qk) = some (.ok (((qk i.qk).1 : ℝ), ((qk i.qk).2 : ℝ))))
    (hLive : ∀ col < 128,
      let row := 128 * base + (g % l.block) % 128
      visitKey blocks 0 col < p.keyCount batch row →
      firstBiasLogit (abiFloat p.invScaleBits) bias qk col =
        some (score p batch head row (visitKey blocks 0 col) / abiFloat p.scaleLog2Bits))
    (hLoop : Holds t.regs (firstLoopGeometry blocks biasCap pastTile))
    (hTail : Holds t.regs (tailFrame l warp))
    (hBaseScale : t.regs 7132 = some (b32 p.scaleLog2Bits))
    (hBar : t.regs 5127 = some (b32 (3 + warp.val)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    FirstRoundProgress p l X warp g j batch head (128 * base + (g % l.block) % 128)
      blocks biasCap pastTile := by
  obtain ⟨_, inv, _, hInv, _, hPos⟩ := hp.scales
  have hWord : p.invScaleBits < 2^32 := (hp.values (14, p.invScaleBits)
    (by simp [Params.scalarWords])).1
  have hAbi : abiFloat p.invScaleBits = (inv : ℝ) := by simp [abiFloat, hInv]
  obtain ⟨u, hu, huRun, huScores, huFrame⟩ :=
    firstBiasScoreTrace hPos hWord hInv bias qk (ht.mono trivial) hLo hHi hScale hDot hInputs hr
  have hKeep (r : Nat)
      (hm : r ∈ [1229, 1224, 2868, 1223, 1225, 1226, 1228, 1062, 2535, 7132, 5127]) :
      u.regs r = t.regs r := huFrame r (firstBiasCarryAudit r hm)
  have huAt := hu.mono (G := [(1229, b32 (blocks-1)), (1224, b32 (p.kLength batch)),
        (2868, b32 (128 * base)), (1223, maskSigned (-(p.qLength batch : Int)))])
    ⟨(hKeep _ (by decide)).trans ht.2.2.2.2.1, (hKeep _ (by decide)).trans ht.2.2.2.2.2.1,
      (hKeep _ (by decide)).trans ht.2.2.2.2.2.2.1, (hKeep _ (by decide)).trans
        ht.2.2.2.2.2.2.2.1, trivial⟩
  have huLoop : Holds u.regs (firstLoopGeometry blocks biasCap pastTile) :=
    ⟨(hKeep _ (by decide)).trans hLoop.1, (hKeep _ (by decide)).trans hLoop.2.1,
      (hKeep _ (by decide)).trans hLoop.2.2.1, (hKeep _ (by decide)).trans hLoop.2.2.2.1,
      trivial⟩
  have huTail : Holds u.regs (tailFrame l warp) :=
    ⟨(hKeep _ (by decide)).trans hTail.1, (hKeep _ (by decide)).trans hTail.2.1, trivial⟩
  exact firstRoundFromBiasTail hp warp (firstBiasLogit (inv : ℝ) bias qk) hb hRow hBlocks
    huAt huScores (by simpa only [hAbi] using hLive) huLoop huTail
    ((hKeep _ (by decide)).trans hBaseScale) ((hKeep _ (by decide)).trans hBar) huRun

end
end PTX.Kernels.TmlFa4Fwd.Softmax
