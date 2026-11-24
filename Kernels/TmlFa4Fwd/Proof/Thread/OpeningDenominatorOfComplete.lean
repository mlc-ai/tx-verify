-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorHead
public import Kernels.TmlFa4Fwd.Proof.Thread.ReachedSoftmaxHistory
import Kernels.TmlFa4Fwd.Proof.Termination
import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Numeric Epilogue Prologue Thread.Scores Thread.Correction

/-- A completed lane keeps its trace in a maximal extension. Its initial probability
packet and denominator are therefore available with the first loop checkpoint on the original
execution. -/
theorem openingDenominatorHeadWithRegistersOfComplete
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads)
    (stage : Fin 2) (hRole : Prologue.warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRow : 128*(2*(Epilogue.assignedCoordinates p batch (g/l.block)).1+stage.val)+
      (g%l.block)%128 < p.qLength batch) :
    let coords := Epilogue.assignedCoordinates p batch (g/l.block)
    let row := 128*(2*coords.1+stage.val)+(g%l.block)%128
    let blocks := Mma.trips p batch coords.1
    let cap := blocks-stageGeometryBlocks p batch coords.1 stage+10
    let past := p.kLength batch-p.qLength batch+256*coords.1
    let mx := scoreMax (fun c => maskedLogit p batch coords.2 row (visitKey blocks 0 c))
      (List.range 128)
    let ref := firstReference p batch coords.2 row blocks
    let mass := (2 : ℝ)^(-ref)*maskedBlockSum (p.keyCount batch row) blocks 0
      (weight p batch coords.2 row)
    let split := firstPlainSplit blocks cap
    let biased := firstBiasedRepeats blocks cap
    Protocol.RecordedSoftmaxRowPrefix p l X g batch coords.2 row stage blocks 1
      (fun _ => mx.map (abiFloat p.scaleLog2Bits * ·)) (fun _ => mass) ∧
    ∃ j u,
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take j) u ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) none ∧
      Thread.Scores.probabilityOrdinal l X (g/l.block) stage 0 (g,j) = 1 ∧
      (if biased = 0 then
        if split = 0 then
          At u 7605 ((1491,b32 split)::firstLoopChoiceFacts blocks split past mx mass)
        else At u 6661 (firstPlainFacts p blocks split past mx mass)
       else At u 5032 (firstBiasedFacts blocks split past mx mass)) ∧
      Holds u.regs (openingDenominatorRegisters p l g) := by
  obtain ⟨last,⟨pc,kind⟩,hExit,hKind⟩ := Thread.exitedOfComplete hX hDone hg
  change kind = .exit at hKind
  subst kind
  obtain ⟨Y,hPrefix,hMax⟩ := maximalExtension hp hX
  have hExitY := Execution.le_get hPrefix hExit
  have hLength := (X.exit_last hX hg hExit).symm.trans (Y.exit_last hMax.1 hg hExitY)
  obtain ⟨suffix,hAppend⟩ := hPrefix.1 g
  have hSuffix : suffix = [] := by
    have hEq := congrArg List.length hAppend
    simp only [List.length_append] at hEq
    exact List.length_eq_zero_iff.mp (by omega)
  have hTrace : X.tr g = Y.tr g := by simpa only [hSuffix,List.append_nil] using hAppend
  have hInitial := recordedOpeningSoftmaxRow hp hX hDone hFrame hg stage hRole hb hLo hHi hRow
  have hHead := (openingDenominatorHeadWithRegistersOfMaximalExit hp hMax (hFrame Y hMax.1)
    hg stage hRole hb hLo hHi hExitY hRow).2
  refine ⟨?_,?_⟩
  · let coords := assignedCoordinates p batch (g/l.block)
    let blocks := Mma.trips p batch coords.1
    let row := 128*(2*coords.1+stage.val)+g%l.block%128
    let mx := scoreMax (fun c => maskedLogit p batch coords.2 row (visitKey blocks 0 c))
      (List.range 128)
    have hRef : (mx.map (abiFloat p.scaleLog2Bits * ·)).getD 0 =
        firstReference p batch coords.2 row blocks := by
      change (mx.map (abiFloat p.scaleLog2Bits * ·)).getD 0 = abiFloat p.scaleLog2Bits*mx.getD 0
      cases mx <;> simp
    simpa only [hRef,coords,blocks,row,mx] using hInitial
  · obtain ⟨j,u,hReach,hRun,hRank,hAt,hRegs⟩ := hHead
    refine ⟨j,u,?_,?_,?_,hAt,hRegs⟩
    · rwa [hTrace]
    · rwa [hTrace]
    · unfold probabilityOrdinal at hRank ⊢
      rwa [hTrace]

end PTX.Kernels.TmlFa4Fwd.Softmax
