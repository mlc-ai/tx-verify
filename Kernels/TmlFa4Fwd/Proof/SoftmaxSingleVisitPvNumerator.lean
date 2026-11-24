-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitProbabilityValues
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitPvAccumulator
public import Kernels.TmlFa4Fwd.Proof.MmaPvNumerics
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondOutputAcquire
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialValueValues
import Kernels.TmlFa4Fwd.Proof.Thread.InitialValuePhase
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvCarry
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.Thread.MmaProbabilityColumn
import Kernels.TmlFa4Fwd.Proof.MmaPvInputLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.TcMma Thread Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma

private theorem pvOperands_of_fields {l : Launch} {g : Nat} {block : Fin 4} {step : Fin 8}
    {op : OperandSpec}
    (hDesc : op.descriptor = pvDescriptor)
    (hB : op.b = sharedDescriptor (kvStart l 1 + pvFragment step) 16384)
    (hA : op.a = op.b) (hLo : op.lowCta = g/l.block) (hHi : op.highCta = g/l.block)
    (hCol : op.aTmem = some (probabilityColumn (pvSite block).stage+8*step.val))
    (hCollector : op.collector = {}) :
    op = pvOperands l g block step 1 := by
  cases op with
  | mk desc a b low high tmem collector =>
    dsimp only at hDesc hB hA hLo hHi hCol hCollector
    subst desc a b low high tmem collector
    rfl

/-- The actual last PV fragment observed by correction has the exact shifted
numerator of the selected row, for a tile with one key-block visit. -/
theorem singleVisitPvNumeratorOfObservedOutput {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {g batch : Nat} (hg : g < l.threads) (hWarp : warpIndex l g < 8) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hRow : 128 * (2 * (assignedCoordinates p batch (g/l.block)).1 +
      (stageOf ⟨warpIndex l g,hWarp⟩).val) + (g%l.block)%128 < p.qLength batch)
    (col : Fin 128) {wait : EvId} (hWait : Thread.Correction.SecondOutputAcquire l X wait)
    (hCta : g/l.block = wait.1/l.block) :
    let coords := assignedCoordinates p batch (g/l.block)
    let stage := stageOf ⟨warpIndex l g,hWarp⟩
    let row := 128 * (2*coords.1+stage.val) + (g%l.block)%128
    let reference := firstReference p batch coords.2 row 1
    ∃ issue d op acc mask loc,
      PvInstruction X issue (firstPvBlock false stage) 7 d op acc mask ∧
      issue.1/l.block = g/l.block ∧
      op.byteLoc .b (qkByteIndex col.val 0 0) = some loc ∧ TcMma.Result l Assumptions.all X issue
      ⟨g/l.block,(tmemRow l g).val,outputColumn stage+col.val⟩
      (.float .f32 ((2 : ℝ) ^ (-reference) *
        maskedBlockSum (p.keyCount batch row) 1 0
          (weightedValue p batch coords.2 row col.val))) := by
  let stage := stageOf (⟨warpIndex l g,hWarp⟩ : Fin 8)
  let block := firstPvBlock false stage
  let coords := assignedCoordinates p batch (g/l.block)
  let row := 128 * (2*coords.1+stage.val) + (g%l.block)%128
  let reference := firstReference p batch coords.2 row 1
  have hStage : (pvSite block).stage = stage := by
    dsimp only [block]
    generalize h : stage = s
    fin_cases s <;> rfl
  obtain ⟨output,commit,scope,hCommit,hOutputCta,hReads⟩ :=
    secondOutputAcquireReads hp hX hWait
  have hOut : output.1/l.block = g/l.block := hOutputCta.2.2.trans hCta.symm
  obtain ⟨steady,hGroups⟩ := initialValueIssuesBeforeSecondOutputCommitExact hp hX hCommit
  have hTail : steady = false := by
    cases steady
    · rfl
    · exfalso
      obtain ⟨i,d,op,acc,mask,hFrag,_,_,hBefore⟩ := hGroups stage 0
      have hIssueCta : i.1/l.block = g/l.block := (congrArg (·/l.block) hBefore.1).trans hOut
      have he : X.get i =
          some ⟨pvPc (firstPvBlock true stage) 0,.tc (.mma d op acc mask)⟩ := hFrag
      have audit : ∀ s : Fin 2, 2295 ≤ pvPc (firstPvBlock true s) 0 ∧
          pvPc (firstPvBlock true s) 0 < 2534 := by decide
      have hBounds := audit stage
      obtain ⟨i,j⟩ := i
      exact singleVisitNoSteadyEvent hp hX hDone hFrame hb (hIssueCta.symm ▸ hLo)
        (hIssueCta.symm ▸ hHi) (hIssueCta.symm ▸ hTrip) he hBounds
  subst steady
  have hGroup := hGroups stage
  choose issues dst specs accum masks hFragment hMma hB hOrder using hGroup
  have hPv (f : Fin 8) : PvInstruction X (issues f) block f
      (dst f) (specs f) (accum f) (masks f) :=
    PvInstruction.of_decoded (hFragment f)
  have hIssueCta (f : Fin 8) : (issues f).1/l.block = g/l.block :=
    (congrArg (·/l.block) (hOrder f).1).trans hOut
  have hSpec (f : Fin 8) : specs f = pvOperands l g block f 1 := by
    have h := hPv f
    obtain ⟨_,_,hDesc,hLow,hHigh⟩ := h.valueOperand hp hX
    obtain ⟨hA,hCollector,_⟩ := h.fixedOperandFields hX
    have hCol := h.tailProbabilityAddress hp hX stage
    rw [← hStage] at hCol
    exact pvOperands_of_fields hDesc (hB f) hA (hLow.trans (hIssueCta f))
      (hHigh.trans (hIssueCta f)) hCol hCollector
  have hIssue (f : Fin 8) : X.MmaIssue (issues f) (outputColumn (pvSite block).stage)
      (pvOperands l g block f 1) (false || decide (0 < f.val)) (List.replicate 4 0) := by
    have h := hPv f
    have hDst := h.tailOutputDestination hp hX stage
    have hMask := (h.fixedOperandFields hX).2.2
    have hAcc : accum f = decide (0 < f.val) := by
      by_cases hf : 0 < f.val
      · simpa only [hf,decide_true] using (h.accumulatorUse hp hX).mpr (.inl hf)
      · rw [decide_eq_false hf]
        apply Bool.eq_false_iff.mpr
        intro hTrue
        rcases (h.accumulatorUse hp hX).mp hTrue with hPos | hSteady
        · exact hf hPos
        · obtain ⟨j,e,he,hBounds⟩ := hSteady.steadyEvent
          have hC := hIssueCta f
          exact singleVisitNoSteadyEvent hp hX hDone hFrame hb (hC.symm ▸ hLo)
            (hC.symm ▸ hHi) (hC.symm ▸ hTrip) he hBounds
    simpa only [hDst,hStage,hSpec f,hAcc,hMask,Bool.false_or] using hMma f
  have hVal (f : Fin 8) (k byte : Nat) (hk : k < 16) (hb' : byte < 2) :
      ∃ loc, (pvOperands l g block f 1).byteLoc .b (qkByteIndex col.val k byte) = some loc ∧
      OperandByteSource l X (issues f) true (qkByteIndex col.val k byte) loc
        (if pvKeyRow f k < p.kLength batch then
          (Value.float .bf16 (pvValue p batch coords.2 (pvKeyRow f k) col.val)).byteAt byte
        else AsyncCopy.zeroByte) := by
    have hC := hIssueCta f
    obtain ⟨loc,hLoc,hValue⟩ := Protocol.singleVisitInitialValueOperandByte hp hX hDone
      hFrame hb (hC.symm ▸ hLo) (hC.symm ▸ hHi) (hC.symm ▸ hTrip) hCommit (hOrder f).1
      stage f col.isLt hk hb' (hFragment f) (hB f) (hMma f)
    exact ⟨loc,by simpa only [hSpec f] using hLoc,by simpa only [hC,coords] using hValue⟩
  have hObserved (f : Fin 8) : ∃ ops, X.async.mmaOperands (issues f) = some ops := by
    obtain ⟨loc,hLoc,_⟩ := hVal f 0 0 (by decide) (by decide)
    obtain ⟨_,_,v,_,ops,hOps,_⟩ := hReads (isB := true) (hIssue f)
      (hOrder f).1 (hOrder f).2.1 hLoc
    exact ⟨ops,hOps⟩
  let weights := fun k => shiftedWeight p batch coords.2 row (visitKey 1 0 k) reference
  have hSource : PvCellInputs p l X g block 1 batch coords.2 (visitKey 1 0 0)
      (tmemRow l g) col issues weights := by
    constructor
    · intro f k byte hk hb' ops hOps
      have hByte := singleVisitProbabilityOperandByte hp hX hDone hFrame hg hWarp hb hLo hHi
        hTrip hRow (hPv f) (hIssueCta f).symm hk hb' hOps
      simpa only [weights,visitKey,Nat.sub_self,Nat.mul_zero,Nat.zero_add] using hByte
    · intro f k byte hk hb'
      obtain ⟨loc,hLoc,hByte⟩ := hVal f k byte hk hb'
      refine ⟨loc,hLoc,?_⟩
      have hKey : visitKey 1 0 0 + 16*f.val+k = pvKeyRow f k := by simp [visitKey,pvKeyRow]
      rw [hKey]
      by_cases hInside : pvKeyRow f k < p.kLength batch
      · simpa only [ite_eq_left hInside] using hByte
      · simpa only [ite_eq_right hInside] using hByte
  have hPrev (f : Fin 8) (hf : f.val ≠ 0) :
      ReadSource l X .acc (issues ⟨f.val-1,by have := f.isLt; omega⟩) (issues f)
        ⟨g/l.block,(tmemRow l g).val,outputColumn (pvSite block).stage+col.val⟩ := by
    let before : Fin 8 := ⟨f.val-1,by have := f.isLt; omega⟩
    rw [hStage]
    exact singleVisitPvAccumulatorSource hp hX hDone hFrame hb hLo hHi hTrip stage (tmemRow l g)
      col (hPv before) (hPv f) (hIssueCta before) (hIssueCta f) (by dsimp [before]; omega)
  have hFinish := pvCellWeightedBlock (p := p) (g := g) (use := 1) (batch := batch)
    (head := coords.2) (qrow := row) (blocks := 1) (visit := 0) hX block (tmemRow l g)
    col issues reference false 0 hSource hIssue hObserved hPrev (fun _ => rfl) (by intro h; cases h)
  obtain ⟨loc,hLoc,_⟩ := hVal 7 0 0 (by decide) (by decide)
  exact ⟨issues 7,dst 7,specs 7,accum 7,masks 7,loc,hPv 7,hIssueCta 7,
    hSpec 7 ▸ hLoc,by simpa only [hStage,zero_add] using hFinish⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
