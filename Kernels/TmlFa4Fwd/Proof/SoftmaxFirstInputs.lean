-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreTrace
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasVector

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

private noncomputable def firstScoreFact (words : Fin 4 → List Value) (q : Fin 4) (k : Fin 16) :
    Nat × Value :=
  (firstScorePairReg q k.val,
    joinValue ((words q).getD (2*k.val) (b32 0)) ((words q).getD (2*k.val+1) (b32 0)))

private noncomputable def firstScoreFacts (words : Fin 4 → List Value) : List (Nat × Value) :=
  (List.finRange 4).flatMap (fun q => (List.finRange 16).map (firstScoreFact words q))

private theorem memFirstScoreFacts (words : Fin 4 → List Value) (q : Fin 4) (k : Fin 16) :
    firstScoreFact words q k ∈ firstScoreFacts words :=
  List.mem_flatMap.mpr ⟨q, List.mem_finRange q, List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩⟩

private theorem firstScoreFactsHold {l : Launch} {X : Execution} {stage : Fin 2}
    {g j : Nat} {t : TState} {words : Fin 4 → List Value}
    (hScores : FirstScores l X stage g j t words) : Holds t.regs (firstScoreFacts words) := by
  have hAll : ∀ x ∈ firstScoreFacts words, t.regs x.1 = some x.2 := by
    intro x hx
    obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
    exact hScores.2 q k.val k.isLt
  generalize firstScoreFacts words = F at hAll ⊢
  induction F with
  | nil => trivial
  | cons x xs ih => exact ⟨hAll x (by simp), ih (fun y hy => hAll y (by simp [hy]))⟩

private theorem firstBiasKeepsScore (i : Fin 16) (r : Nat) (hr : 7303 ≤ r) :
    biasVectorKeeps false i r := by
  have hRead : ∀ d ∈ biasReadRegs false i, d ≤ 3074 := by
    fin_cases i <;> decide
  have hUnpack : (biasUnpackRegs false i 0).1 ≤ 913 := by
    fin_cases i <;> decide
  exact ⟨fun h => by have := hRead r h; omega, .inr (by omega)⟩

/-- The first QK and Bias waits lead to the actual score and bias operands at the proxy fence.
Their source obligations are stated at the exact observed event addresses. -/
theorem firstQkBiasInputsTrace {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (stage : Fin 2) {g j : Nat} {t : TState} {F : List (Nat × Value)}
    (ht : At t 3425 F)
    (hQkWait : (2769, b32 (waitLoc l g stage 1).addr) ∈ F)
    (hBiasWait : (2771, b32 (waitLoc l g stage 2).addr) ∈ F)
    (hPhase : (2770, b32 0) ∈ F)
    (hAddr0 : (2788, b32 (scoreAddress l g stage 0)) ∈ F)
    (hAddr2 : (2789, b32 (scoreAddress l g stage 2)) ∈ F)
    (hQkFrame : ∀ x ∈ F, x.1 ≠ 9751 ∧ firstScoreKeeps x.1)
    (hBiasFrame : ∀ x ∈ F, x.1 ≠ 9752 ∧ ∀ i, biasVectorKeeps false i x.1)
    (hBytes : ∀ pos (q : Fin 4) vals, X.get (g, pos) = some
      ⟨scorePc .first q, .tc (.ld (scoreAddress l g stage q) vals .s32x32b)⟩ →
      ∀ k < 32, (vals.getD k (b32 0)).bytes = 4)
    (base : Fin 16 → Nat) (bias : Fin 16 → Nat → Value)
    (hShape : ∀ i k, k < 4 → BiasWordShape (bias i k))
    (hBases : ∀ i, ((biasReadSite false i).base, b32 (base i)) ∈ F)
    (hAddr : ∀ i, base i + (biasReadSite false i).offset < 2^32)
    (hAlign : ∀ i, (base i + (biasReadSite false i).offset) % 16 = 0)
    (hValue : ∀ wait, X.get (g, wait) =
      some ⟨3498, .wait (waitLoc l g stage 2) 0 true true .cta⟩ →
      ∀ i k, k < 4 → ∀ bs, X.get (g, wait + 1 + 4 * i.val + k) = some
        ⟨biasReadPc false i, .rd (biasReadAcc l g (base i) false i k) bs⟩ →
          rebuild 3 bs = .ok (bias i k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ (qkFails biasFails : Nat) (u : TState) (scores : Fin 4 → List Value),
      let qkStart := j+qkFails+1
      let biasWait := qkStart+4
      let biasStart := biasWait+biasFails+1
      (X.tr g).drop j =
        List.replicate qkFails ⟨3425, .wait (waitLoc l g stage 1) 0 false true .cta⟩ ++
          ⟨3425, .wait (waitLoc l g stage 1) 0 true true .cta⟩ :: (X.tr g).drop qkStart ∧
      (X.tr g).drop biasWait =
        List.replicate biasFails ⟨3498, .wait (waitLoc l g stage 2) 0 false true .cta⟩ ++
          ⟨3498, .wait (waitLoc l g stage 2) 0 true true .cta⟩ :: (X.tr g).drop biasStart ∧
      At u 3581 F ∧ FirstScores l X stage g qkStart u scores ∧
      (∀ i, BiasWordReads l X false i g (biasStart+4*i.val) (base i) (bias i) ∧
        BiasUnpacked false i u (bias i)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (biasStart+64)) none := by
  obtain ⟨qkFails, v, scores, hQkEvts, hvAt, hScores, hv⟩ :=
    firstQkScoreTileTrace hp stage ht hQkWait hPhase hAddr0 hAddr2 hQkFrame hBytes hr
  have hFacts : At v 3498 (F ++ firstScoreFacts scores) :=
    hvAt.mono ((holds_append _ _ _).mpr ⟨hvAt.2.2.2.2, firstScoreFactsHold hScores⟩)
  have hKeep : ∀ x ∈ F ++ firstScoreFacts scores,
      x.1 ≠ 9752 ∧ ∀ i, biasVectorKeeps false i x.1 := by
    intro x hx
    rcases List.mem_append.mp hx with hF | hWritten
    · exact hBiasFrame x hF
    obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp hWritten
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
    change firstScorePairReg q k.val ≠ 9752 ∧ ∀ i, biasVectorKeeps false i (firstScorePairReg q k)
    have hQ := q.isLt
    have hK := k.isLt
    exact ⟨by unfold firstScorePairReg; omega,
      fun i => firstBiasKeepsScore i _ (by unfold firstScorePairReg; omega)⟩
  obtain ⟨biasFails, u, hBiasEvts, huAt, hBias, hu⟩ :=
    firstBiasTileTrace hp stage hFacts (List.mem_append_left _ hBiasWait)
      (List.mem_append_left _ hPhase) hKeep base bias hShape
      (fun i => List.mem_append_left _ (hBases i)) hAddr hAlign hValue hv
  have hU := (holds_append _ _ _).mp huAt.2.2.2.2
  refine ⟨qkFails, biasFails, u, scores, hQkEvts, hBiasEvts, huAt.mono hU.1,
    ⟨hScores.1, ?_⟩, hBias, hu⟩
  intro q k hk
  exact holds_mem hU.2 (memFirstScoreFacts scores q ⟨k, hk⟩)

end PTX.Kernels.TmlFa4Fwd.Softmax
