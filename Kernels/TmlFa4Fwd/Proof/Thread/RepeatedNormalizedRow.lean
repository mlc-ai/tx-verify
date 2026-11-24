-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedNormalization
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFinalStageZero

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.TcMma Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Protocol (PvVisit)

noncomputable section

/-- The mathematical visits for one live row, paired to its actual terminal
statistics publication and final completed PV result. -/
structure RepeatedRowHistory (p : Params) (l : Launch) (X : Execution)
    (g batch : Nat) (stage : Fin 2) where
  reference : Nat → Option ℝ
  sum : Nat → ℝ
  numerator : Nat → Nat → ℝ
  recurrence :
    let coords := assignedCoordinates p batch (g/l.block)
    let qrow := stageRow coords.1 stage+rowOf l g
    let blocks := trips p batch coords.1
    SoftmaxRun p batch coords.2 qrow blocks reference sum numerator
  statistics :
    let blocks := trips p batch (assignedCoordinates p batch (g/l.block)).1
    ∀ pos, CorrectionWaits X (g,pos) .terminal stage → pos+1 < (X.tr g).length →
      ∃ pub maximum, TerminalPublishedWords l X g stage pub (fl (sum (blocks-1))) (fl maximum) ∧
        TerminalGeneration l X g stage (pub-2) pos
  accumulator :
    let blocks := trips p batch (assignedCoordinates p batch (g/l.block)).1
    let row : Fin 128 := ⟨rowOf l g,Nat.mod_lt _ (by decide)⟩
    ∀ (col : Fin 128) (source : EvId), source.1/l.block = g/l.block →
      X.async.mmaDone source = true →
      PvVisit l X source.1 (firstPvBlock false stage) (2*blocks-1) row col source.2 →
      TcMma.Result l Assumptions.all X source ⟨g/l.block,row.val,outputColumn stage+col.val⟩
        (.float .f32 (numerator (blocks-1) col.val))

/-- An exited, active correction lane runs both finalizers through the real
trace. The arithmetic histories identify the emitted FP32 attention row. -/
theorem normalizedRowOfCompletedHistory {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads)
    (hWarpLo : 8 ≤ warpIndex l g) (hWarpHi : warpIndex l g < 12)
    (stage : Fin 2) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRow : stageRow (assignedCoordinates p batch (g/l.block)).1 stage+rowOf l g <
      p.qLength batch)
    (hHistory : ∀ stage' : Fin 2,
      stageRow (assignedCoordinates p batch (g/l.block)).1 stage'+rowOf l g < p.qLength batch →
      Nonempty (RepeatedRowHistory p l X g batch stage')) :
    ∃ start, SingleVisitNormalizedRow p l X g batch stage start := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  obtain ⟨pos,t,ht,hT⟩ := observedFinalStageZeroEntry hp hX hDone (hFootprint X hX)
    hg hWarpLo hWarpHi hl hb hLo hHi
  rw [hSelf] at hT
  have hRow0 : stageRow (assignedCoordinates p batch (g/l.block)).1 0+rowOf l g <
      p.qLength batch := by
    unfold stageRow at *
    omega
  have hFrame0 (sum maximum : ℝ) :
      FinalStageFrame l g 0 sum maximum (correctionFinalStageFacts p l g batch lane 0 0 0) := by
    simpa only [hSelf] using correctionFinalStageFrame p l g batch lane 0 0 sum maximum 0
  obtain ⟨first⟩ := hHistory 0 hRow0
  obtain ⟨max0,start0,v,_,hOut0,hExact0,hV,hRest0⟩ :=
    normalizedStageOfTerminalRow hp hX hDone hFootprint 0 hb hLo hHi hRow0 ht hFrame0 hT
      first.reference first.sum first.numerator first.recurrence
      (first.statistics pos) first.accumulator
  fin_cases stage
  · exact ⟨start0,_,_,hOut0,hExact0⟩
  · obtain ⟨second⟩ := hHistory 1 hRow
    let sum0 := first.sum (trips p batch (assignedCoordinates p batch (g/l.block)).1-1)
    have hSecond : At v (statsBarrierPc 1 false)
        (correctionFinalStageFacts p l g batch lane sum0 max0 1) :=
      hV.mono ⟨hV.2.2.2.2.2.1,hV.2.2.2.2.2.2.2⟩
    have hFrame1 (sum maximum : ℝ) :
        FinalStageFrame l g 1 sum maximum
          (correctionFinalStageFacts p l g batch lane sum0 max0 1) := by
      simpa only [hSelf] using correctionFinalStageFrame p l g batch lane sum0 max0 sum maximum 1
    obtain ⟨_,start,_,_,hOut,hExact,_,_⟩ :=
      normalizedStageOfTerminalRow hp hX hDone hFootprint 1 hb hLo hHi hRow
        hSecond hFrame1 hRest0 second.reference second.sum second.numerator second.recurrence
        (second.statistics (start0+163)) second.accumulator
    exact ⟨start,_,_,hOut,hExact⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
