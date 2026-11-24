-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleVisit
public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupRoute
import Lemmas.Step.SetMaxNReg

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The part of the register frame used and preserved by one rescale visit. -/
structure RescaleVisitFrame (l : Launch) (g : Nat) (stage : Fin 2)
    (F : List (Nat × Value)) : Prop where
  rendezvous : (statsBarrierReg stage, b32 (statsBarrierId l g stage)) ∈ F
  statistics : (1627, b32 (l.sharedBase + 4 * rowOf l g)) ∈ F
  accumulator : ∀ rv ∈ rescaleStageAddresses l g stage, rv ∈ F
  credit : (outputCreditReg stage, b32 (creditLoc l g stage).addr) ∈ F
  reuse : (rescaleReuseReg stage, b32 (rescaleReuseLoc l g stage).addr) ∈ F
  control : ∀ rv ∈ F, rv.1 ≠ statsReg stage .alpha ∧ rv.1 ≠ rescalePredReg stage ∧
    rv.1 ≠ rescaleVoteReg stage ∧ rv.1 ≠ maskZeroReg stage
  data : ∀ chunk : Fin 8, ∀ r ∈ F.map Prod.fst, r ∉ rescaleDataRegs stage chunk ∧
    rescaleLocalKeeps stage chunk r
  release : ∀ pair ∈ F, pair.1 ≠ rescaleCountReg stage ∧
    pair.1 ≠ rescaleSignalDst stage ∧ pair.1 ≠ rescaleSignalDst stage + 1

/-- Values supplied by the statistics publication and the accumulated output before this visit. -/
structure RescaleVisitInputs (l : Launch) (X : Execution) (g pos : Nat) (stage : Fin 2)
    (alpha : ℝ) (old : Fin 8 → Nat → ℝ) (coefficient : Value := fl alpha) : Prop where
  alphaRead : ∀ bs, X.get (g, pos + 1) = some ⟨statsPc stage .alpha,
    .rd { loc := statsLoc l g stage .alpha, size := 4 } bs⟩ → bs = coefficient.toBytes.map some
  accumulatorRead : ∀ word : BitVec 32, word ≠ 0 → X.get (g, pos + 2) =
    some ⟨statsPc stage .alpha + 2, .vote (2 ^ 32 - 1) (decide (alpha < 1)) word⟩ →
    ∀ (chunk : Fin 8) vals, X.get (g, pos + 3 + 3 * chunk.val) =
    some ⟨rescaleLoadPc stage chunk,
      .tc (.ld (outputAddress l g stage (16 * chunk.val)) vals .s32x32b)⟩ →
    vals = List.ofFn (fun i : Fin 16 => fl (old chunk i.val))

end
end PTX.Kernels.TmlFa4Fwd.Correction
