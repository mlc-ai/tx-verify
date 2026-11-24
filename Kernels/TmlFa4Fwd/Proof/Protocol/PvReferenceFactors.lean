-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxAlphaValues
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleBallotValue
public import Kernels.TmlFa4Fwd.Proof.Protocol.PvUnscaledCarry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX

/-- The fallback exponent is used only below the reference-retention threshold. -/
theorem correctionAlpha_le_one (scale : ℝ) (old candidate : Option ℝ) :
    correctionAlpha scale old candidate ≤ 1 := by
  unfold correctionAlpha
  split
  · exact le_rfl
  · rename_i hSkip
    cases hDelta : referenceDelta scale old candidate with
    | none => simp
    | some delta =>
      have hSmall : delta < -8 := by
        simp [keepReference,hDelta] at hSkip
        exact hSkip
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)

end PTX.Kernels.TmlFa4Fwd.Softmax

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.TcMma Thread Thread.Scores Thread.Mma
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

/-- A direct prior-PV source forces the corresponding arithmetic factor to be one. -/
theorem PvVisit.directFactorOfRescaleVisit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {g index use prior d correction pos : Nat} {block : Fin 4} {row col : Fin 128}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    {alpha : ℝ} {old : Fin 8 → Nat → ℝ} {vote : BitVec 32} {coefficient : Value}
    (visit : PvVisit l X g block use row col index) (hCarry : visit.keep = true)
    (hCta : correction/l.block = g/l.block)
    (hRow : laneBase l correction+laneOf l correction = row.val) :
    let stage := (pvSite block).stage
    let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
    PvInstruction X (g,prior) (firstPvBlock true stage) 7 d op accum mask →
    LatestValueReadyUse l X g prior (use-2) →
    ReadSource l X .acc (g,prior) (g,visit.issues 0) cell →
    TmlFa4Fwd.Correction.RescaleVisit l X correction pos stage alpha old vote coefficient →
    (correctionBefore X (correction,pos)).barrier
      (TmlFa4Fwd.Correction.statsBarrierId l correction stage) = use/2 →
    alpha ≤ 1 → alpha = 1 := by
  dsimp only
  intro hPrior hUse hRead hVisit hOrdinal hBound
  have hZero := visit.previousCarrySkipsRescale hp hX hCuQ hCarry hCta hRow
    hPrior hUse hRead hVisit hOrdinal
  exact hVisit.factorOfZeroBallot hX hZero hBound

end PTX.Kernels.TmlFa4Fwd.Protocol
