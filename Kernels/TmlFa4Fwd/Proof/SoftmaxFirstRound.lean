-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstAddress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstAffineInput
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstSum

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The first-round shift is expressed in the scaled units of the mathematical logits. -/
def firstReference (p : Params) (batch head row blocks : Nat) : ℝ :=
  abiFloat p.scaleLog2Bits *
    (scoreMax (fun c => maskedLogit p batch head row (visitKey blocks 0 c)) (List.range 128)).getD 0

/-- The saved row limits are consumed after the first denominator is initialized. -/
def firstLoopGeometry (blocks biasCap pastTile : Nat) : List (Nat × Value) :=
  [(1225, b32 (pastTile+256)), (1226, b32 blocks), (1228, b32 biasCap),
    (1229, b32 (blocks-1))]

def firstLoopCarryValue (blocks biasCap pastTile : Nat) (mx : Option ℝ) : Nat → Value
  | 1225 => b32 (pastTile+256)
  | 1226 => b32 blocks
  | 1228 => b32 biasCap
  | 1229 => b32 (blocks-1)
  | _ => scoreValue mx

private theorem maskKeepsArgs {r : Nat}
    (h : r ∈ [1062, 1225, 1226, 1228, 1229, 2535, 3217, 3223, 3224, 3225, 3226,
      5127, 7132]) :
    r ∉ firstMaskSetupWrites ∧
      ∀ group : Fin 4, ¬ firstMaskGroupWrites group r := by
  have hAudit : ∀ r ∈ [1062, 1225, 1226, 1228, 1229, 2535, 3217, 3223, 3224, 3225, 3226,
      5127, 7132],
      r ∉ firstMaskSetupWrites := by decide +kernel
  refine ⟨hAudit r h, fun group => ?_⟩
  have hg := group.isLt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  unfold firstMaskGroupWrites maskScratch maskPred
  omega

private theorem shiftKeepsArgs {r : Nat}
    (h : r ∈ [1062, 1225, 1226, 1228, 1229, 2535, 3217, 3223, 3224, 3225, 3226]) :
    r ∉ (rWrites (firstMaxItems.map MaxItem.item) ++
      [622, 3685, 1230, 3686, 8024, 8025, 8026]) := by
  have hAudit : ∀ r ∈ [1062, 1225, 1226, 1228, 1229, 2535, 3217, 3223, 3224, 3225, 3226],
      r ∉ (rWrites (firstMaxItems.map MaxItem.item) ++
        [622, 3685, 1230, 3686, 8024, 8025, 8026]) :=
    by decide +kernel
  exact hAudit r h

/-- The observable first-round events and the state of the initialized denominator. -/
def FirstRoundProgress (p : Params) (l : Launch) (X : Execution) (warp : Fin 8)
    (g j batch head row blocks biasCap pastTile : Nat) : Prop :=
  let reference := firstReference p batch head row blocks
  let mx := scoreMax (fun c => maskedLogit p batch head row (visitKey blocks 0 c)) (List.range 128)
  let weights := fun (q : Fin 4) i =>
    shiftedWeight p batch head row (visitKey blocks 0 (32 * q.val + i)) reference
  let ack := waitLoc l g (stageOf warp) 3
  let mass := (2 : ℝ) ^ (-reference) * maskedBlockSum (p.keyCount batch row) blocks 0
    (weight p batch head row)
  ∃ u barInst electInst leader failed,
    let post := if laneOf l g = leader then j + 12 else j + 11
    X.get (g, j) = some ⟨4397, .bar (3 + warp.val) (some 64) .arrive⟩ ∧
    (∀ i : Fin 10, X.get (g, j + 1 + i.val) =
      (firstPublicationEvents l g (stageOf warp) weights barInst electInst leader)[i.val]?) ∧
    (laneOf l g = leader → X.get (g, j + 11) = some
      ⟨4867, .arrive (signalLoc l g (stageOf warp) 2) 0 1 true .cta⟩) ∧
    (X.tr g).drop post = List.replicate failed ⟨4874, .wait ack 0 false true .cta⟩ ++
      ⟨4874, .wait ack 0 true true .cta⟩ :: (X.tr g).drop (post + failed + 1) ∧
    At u 5006 ((7257, fl mass) :: factsFrom firstTransitionRegs
      (firstLoopCarryValue blocks biasCap pastTile mx)) ∧
    Run kernel Assumptions.all l g u ((X.tr g).drop (post + failed + 1)) none

/-- Starting with the decoded bias output pairs and fetched geometry, the first round
masks padding and future keys, publishes the maximum handoff and the four groups of BF16
probabilities, then stores the initial FP32 denominator after the correction acknowledgement. -/
theorem firstRoundFromScores {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j batch head tid base blocks biasCap pastTile : Nat}
    {t : TState}
    (raw : Nat → Option ℝ) (hb : batch < p.batch) (htid : tid < 2^32)
    (hRow : 128 * base + tid % 128 < p.qLength batch + 256)
    (hBlocks : 128 * (blocks - 1) ≤ p.kLength batch)
    (ht : At t 3863
      [(1229, b32 (blocks-1)), (1224, b32 (p.kLength batch)),
        (3219, b32 tid), (2868, b32 (128 * base)), (1223, maskSigned (-(p.qLength batch : Int)))])
    (hs : firstMaskInputs t raw)
    (hLive : ∀ col < 128, visitKey blocks 0 col < p.keyCount batch (128 * base + tid % 128) →
      raw col = some (score p batch head (128 * base + tid % 128) (visitKey blocks 0 col) /
        abiFloat p.scaleLog2Bits))
    (hLoop : Holds t.regs (firstLoopGeometry blocks biasCap pastTile))
    (hTail : Holds t.regs (tailFrame l warp))
    (hScaleWord : t.regs 7132 = some (b32 p.scaleLog2Bits))
    (hBar : t.regs 5127 = some (b32 (3 + warp.val)))
    (hP : ∀ q : Fin 4, t.regs (probabilityReg .first q) =
      some (b32 (probabilityAddress l g (stageOf warp) q)))
    (hPBase : t.regs 3217 = some (b32 (l.sharedBase + 8 * (stageOf warp).val)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    FirstRoundProgress p l X warp g j batch head (128 * base + tid % 128)
      blocks biasCap pastTile := by
  let row := 128 * base + tid % 128
  let logits := fun c => maskedLogit p batch head row (visitKey blocks 0 c)
  have hLogits (c : Nat) (hc : c < 128) :
      firstMaskedValue p batch row blocks raw c = logits c := by
    by_cases hk : visitKey blocks 0 c < p.keyCount batch row
    · simp only [firstMaskedValue, logits, maskedLogit, ite_eq_left hk]
      exact hLive c hc hk
    · simp only [firstMaskedValue, logits, maskedLogit, ite_eq_right hk]
  have hBounds := hp.lengths batch hb
  obtain ⟨s, hsAt, hsRun, hScores, hsFrame⟩ :=
    firstCausalMaskTrace p batch tid base blocks raw htid hBounds.2.1 hBounds.2.2
      hRow hBlocks ht hs hr
  have hMaskKeep (r : Nat)
      (hm : r ∈ [1062, 1225, 1226, 1228, 1229, 2535, 3217, 3223, 3224, 3225, 3226, 5127, 7132]) :
      s.regs r = t.regs r :=
    hsFrame r (maskKeepsArgs hm).1 (maskKeepsArgs hm).2
  have hsLogits : ∀ group : Fin 4, firstMaskOutputs s group logits := by
    intro group pair hPair
    have hGroup := group.isLt
    obtain ⟨hLo, hHi⟩ := hScores group pair hPair
    rw [hLogits _ (by omega)] at hLo
    rw [hLogits _ (by omega)] at hHi
    exact ⟨hLo, hHi⟩
  obtain ⟨v, hv, hStats, hvRun, hScale, hOff, hRead, hSource, hMax, hvFrame⟩ :=
    firstShiftInputTrace hp warp logits hsAt hsLogits
      ((hMaskKeep _ (by decide)).trans hScaleWord) ((hMaskKeep _ (by decide)).trans hBar) hsRun
  have hKeep (r : Nat)
      (hm : r ∈ [1062, 1225, 1226, 1228, 1229, 2535, 3217, 3223, 3224, 3225, 3226]) :
      v.regs r = t.regs r := by
    refine (hvFrame r (shiftKeepsArgs hm)).trans (hMaskKeep r ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    tauto
  have hvTail : At v 4403 (tailFrame l warp) :=
    hv.mono ⟨(hKeep _ (by decide)).trans hTail.1, (hKeep _ (by decide)).trans hTail.2.1,
      trivial⟩
  have hvP (q : Fin 4) : v.regs (probabilityReg .first q) =
      some (b32 (probabilityAddress l g (stageOf warp) q)) :=
    (hKeep _ (by fin_cases q <;> decide)).trans (hP q)
  let reference := firstReference p batch head row blocks
  have hOff' : Assumption.readERealPair l g v (.reg (shiftLayout 0).addReg) =
      some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))) := by
    simpa only [show (shiftLayout 0).addReg = 8024 from rfl, reference, firstReference, logits]
      using hOff
  let keep := firstLoopCarryValue blocks biasCap pastTile (scoreMax logits (List.range 128))
  have hTransition : Holds v.regs (factsFrom firstTransitionRegs keep) := by
    apply holds_of_pointwise
    intro r h
    simp only [firstTransitionRegs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact (hKeep _ (by decide)).trans hLoop.1
    · exact (hKeep _ (by decide)).trans hLoop.2.1
    · exact (hKeep _ (by decide)).trans hLoop.2.2.1
    · exact (hKeep _ (by decide)).trans hLoop.2.2.2.1
    · exact hMax
  obtain ⟨u, barInst, electInst, leader, failed, hPub, hElect, hAck, hU, hRun⟩ :=
    firstRoundNumericSum hp warp reference (firstShiftValues v) (firstShiftLogits logits)
      keep hTransition hvTail
      hRead hSource (fun _ _ => ⟨rfl, rfl⟩) hScale hOff' hvP
      ((hKeep _ (by decide)).trans hPBase) hvRun
  exact ⟨u, barInst, electInst, leader, failed, hStats, hPub, hElect, hAck, hU, hRun⟩


/-- From the end of the first bias FMA pass, the decoded program computes both the
P addresses and the mask geometry before performing the first numerical round. -/
theorem firstRoundFromBiasTail {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j batch head base blocks biasCap pastTile : Nat} {t : TState}
    (raw : Nat → Option ℝ) (hb : batch < p.batch)
    (hRow : 128 * base + (g % l.block) % 128 < p.qLength batch + 256)
    (hBlocks : 128 * (blocks - 1) ≤ p.kLength batch)
    (ht : At t 3850
      [(1229, b32 (blocks-1)), (1224, b32 (p.kLength batch)),
        (2868, b32 (128 * base)), (1223, maskSigned (-(p.qLength batch : Int)))])
    (hs : firstMaskInputs t raw)
    (hLive : ∀ col < 128,
      visitKey blocks 0 col < p.keyCount batch (128 * base + (g % l.block) % 128) →
      raw col = some (score p batch head (128 * base + (g % l.block) % 128)
        (visitKey blocks 0 col) / abiFloat p.scaleLog2Bits))
    (hLoop : Holds t.regs (firstLoopGeometry blocks biasCap pastTile))
    (hTail : Holds t.regs (tailFrame l warp))
    (hScaleWord : t.regs 7132 = some (b32 p.scaleLog2Bits))
    (hBar : t.regs 5127 = some (b32 (3 + warp.val)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    FirstRoundProgress p l X warp g j batch head (128 * base + (g % l.block) % 128)
      blocks biasCap pastTile := by
  obtain ⟨u, hu, hAddr, huRun, hKeep⟩ := firstPAddressTrace hp warp (ht.mono hTail) hr
  have hTid : g % l.block < 2^32 := by
    have h := Nat.mod_lt g (show 0 < l.block by rw [hp.block]; decide)
    rw [hp.block] at h ⊢
    omega
  have hSrc : firstMaskInputs u raw := by
    intro group pair hj
    have hGroup := group.isLt
    refine (hKeep _ ?_).trans (hs group pair hj)
    unfold firstMaskPairRegs firstAddressWrites
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map, List.mem_range,
      not_or]
    omega
  have hTidReg : u.regs 3219 = some (b32 (g % l.block)) :=
    holds_mem hu.2.2.2.2 (by simp [firstAddressFacts])
  have hBaseReg : u.regs 3217 = some (b32 (l.sharedBase + 8 * (stageOf warp).val)) :=
    holds_mem hu.2.2.2.2 (by simp [firstAddressFacts])
  have huAt : At u 3863
      [(1229, b32 (blocks-1)), (1224, b32 (p.kLength batch)),
        (3219, b32 (g % l.block)), (2868, b32 (128 * base)),
        (1223, maskSigned (-(p.qLength batch : Int)))] := by
    exact hu.mono ⟨(hKeep _ (by decide)).trans ht.2.2.2.2.1,
      (hKeep _ (by decide)).trans ht.2.2.2.2.2.1, hTidReg,
      (hKeep _ (by decide)).trans ht.2.2.2.2.2.2.1,
      (hKeep _ (by decide)).trans ht.2.2.2.2.2.2.2.1, trivial⟩
  have huTail : Holds u.regs (tailFrame l warp) :=
    ⟨(hKeep _ (by decide)).trans hTail.1, (hKeep _ (by decide)).trans hTail.2.1, trivial⟩
  have huLoop : Holds u.regs (firstLoopGeometry blocks biasCap pastTile) :=
    ⟨(hKeep _ (by decide)).trans hLoop.1, (hKeep _ (by decide)).trans hLoop.2.1,
      (hKeep _ (by decide)).trans hLoop.2.2.1, (hKeep _ (by decide)).trans hLoop.2.2.2.1,
      trivial⟩
  exact firstRoundFromScores hp warp raw hb hTid hRow hBlocks huAt hSrc hLive huLoop huTail
    ((hKeep _ (by decide)).trans hScaleWord) ((hKeep _ (by decide)).trans hBar) hAddr hBaseReg huRun

end
end PTX.Kernels.TmlFa4Fwd.Softmax
