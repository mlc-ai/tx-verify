-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.PvAccumulatorSources
public import Kernels.TmlFa4Fwd.Proof.MmaPvResult
public import Kernels.TmlFa4Fwd.Proof.Protocol.ValueLaunchOperandElements
import Kernels.TmlFa4Fwd.Proof.MmaPvInputLayout
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvOperandFields
import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorCompletion
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.TcMma Thread
open scoped BigOperators
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

/-- The issued fragments and accumulator reads of one PV visit writing an output cell. -/
structure PvVisit (l : Launch) (X : Execution) (g : Nat) (block : Fin 4) (use : Nat)
    (row col : Fin 128) (last : Nat) where
  issues : Fin 8 → Nat
  keep : Bool
  terminal : issues 7 = last
  fragment : ∀ step : Fin 8, PvInstruction X (g,issues step) block step
    (outputColumn (pvSite block).stage) (pvOperands l g block step use)
    (keep || decide (0 < step.val)) (List.replicate 4 0)
  ready : ∀ step : Fin 8, Mma.LatestValueReadyUse l X g (issues step) use
  previous : ∀ (step : Fin 8) (h : 0 < step.val),
    ReadSource l X .acc (g,issues ⟨step.val-1,by omega⟩) (g,issues step)
      ⟨g/l.block,row.val,outputColumn (pvSite block).stage+col.val⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem pvFragmentChain (hCuQ : Epilogue.DrainCuQProtected p X) {g use : Nat}
    {block : Fin 4} (row col : Fin 128) (n : Nat) (hn : n < 8) {index d : Nat} {op : OperandSpec}
    {accum : Bool} {mask : List Nat}
    (hLast : PvInstruction X (g,index) block ⟨n,hn⟩ d op accum mask)
    (hUse : Mma.LatestValueReadyUse l X g index use) :
    ∃ (issues : Fin 8 → Nat) (keep : Bool), issues ⟨n,hn⟩ = index ∧
      (∀ step : Fin 8, step.val ≤ n → PvInstruction X (g,issues step) block step
        (outputColumn (pvSite block).stage) (pvOperands l g block step use)
        (keep || decide (0 < step.val)) (List.replicate 4 0)) ∧
      (∀ step : Fin 8, step.val ≤ n → Mma.LatestValueReadyUse l X g (issues step) use) ∧
      (∀ (step : Fin 8) (h : 0 < step.val), step.val ≤ n →
        ReadSource l X .acc (g,issues ⟨step.val-1,by omega⟩) (g,issues step)
          ⟨g/l.block,row.val,outputColumn (pvSite block).stage+col.val⟩) := by
  induction n using Nat.strong_induction_on generalizing index d op accum mask with
  | h n ih =>
    have hOp := hLast.operandsOfLatestValueReadyUse hp hX hUse
    have hD := hLast.outputDestination hp hX
    have hMask := (hLast.fixedOperandFields hX).2.2
    by_cases hPos : 0 < n
    · obtain ⟨prev,_,d',op',accum',mask',hPrev,hSource,hPrevUse⟩ :=
        previousPvAccumulatorSourceAtUse hp hX hCuQ hLast hPos row col
      obtain ⟨smaller,keep,hTerminal,hFrag,hReady,hReads⟩ :=
        ih (n-1) (by omega) (by omega) hPrev (hPrevUse use hUse)
      let issues (step : Fin 8) := if step.val < n then smaller step else index
      refine ⟨issues,keep,by simp [issues],?_,?_,?_⟩
      · intro step hStep
        by_cases hLt : step.val < n
        · simpa only [issues, ite_eq_left hLt] using hFrag step (by omega)
        · obtain rfl : step = (⟨n,hn⟩ : Fin 8) := Fin.ext (by change step.val = n; omega)
          have hAcc : accum = true := (hLast.accumulatorUse hp hX).mpr (.inl hPos)
          simpa [issues,hD,hOp,hMask,hAcc,hPos] using hLast
      · intro step hStep
        by_cases hLt : step.val < n
        · simpa only [issues, ite_eq_left hLt] using hReady step (by omega)
        · simpa only [issues, ite_eq_right hLt] using hUse
      · intro step hStep hLe
        have hPrevLt : step.val-1 < n := by omega
        by_cases hLt : step.val < n
        · simpa only [issues, ite_eq_left hPrevLt, ite_eq_left hLt] using
            hReads step hStep (by omega)
        · obtain rfl : step = (⟨n,hn⟩ : Fin 8) := Fin.ext (by change step.val = n; omega)
          simpa only [issues, ite_eq_left hPrevLt, ite_eq_right (Nat.lt_irrefl _),
            hTerminal] using hSource
    · have hZero : n = 0 := by omega
      refine ⟨fun _ => index,accum,rfl,?_,fun _ _ => hUse,?_⟩
      · intro step hStep
        obtain rfl : step = (⟨n,hn⟩ : Fin 8) := Fin.ext (by change step.val = n; omega)
        simp only [hD,hOp,hMask] at hLast
        simpa [hPos] using hLast
      · intro step hStep hLe
        omega

/-- A real last PV fragment fixes all eight events and seven accumulator sources in its visit. -/
theorem PvVisit.ofLast (hCuQ : Epilogue.DrainCuQProtected p X) {g index use d : Nat} {block : Fin 4}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hLast : PvInstruction X (g,index) block 7 d op accum mask)
    (hUse : Mma.LatestValueReadyUse l X g index use) (row col : Fin 128) :
    Nonempty (PvVisit l X g block use row col index) := by
  obtain ⟨issues,keep,hTerminal,hFrag,hReady,hReads⟩ :=
    pvFragmentChain hp hX hCuQ row col 7 (by decide) hLast hUse
  exact ⟨⟨issues,keep,hTerminal,fun step => hFrag step (by omega),
    fun step => hReady step (by omega),fun step h => hReads step h (by omega)⟩⟩

/-- Completion of the last PV fragment requires completion of all eight fragments. -/
theorem PvVisit.fragmentDone (hCuQ : Epilogue.DrainCuQProtected p X) {g use index : Nat}
    {block : Fin 4} {row col : Fin 128} (visit : PvVisit l X g block use row col index)
    (hDone : X.async.mmaDone (g,index) = true) (step : Fin 8) :
    X.async.mmaDone (g,visit.issues step) = true := by
  let dst := outputColumn (pvSite block).stage
  let args := pvOperands l g block
  let cell : Cell := ⟨g/l.block,row.val,dst+col.val⟩
  have hGuard := guardedOfTmaSafe hX (Safety.noTmaUnsafe hp hX hCuQ)
  have hIssue (f : Fin 8) : X.MmaIssue (g,visit.issues f) dst (args f use)
      (visit.keep || decide (0 < f.val)) (List.replicate 4 0) :=
    ⟨_,(visit.fragment f).decoded⟩
  have hAll (n : Nat) (hn : n ≤ 7) : X.async.mmaDone (g,visit.issues ⟨7-n,by omega⟩) = true := by
    induction n with
    | zero =>
      exact visit.terminal.symm ▸ hDone
    | succ n ih =>
      let before : Fin 8 := ⟨7-n,by omega⟩
      let prior : Fin 8 := ⟨before.val-1,by have := before.isLt; omega⟩
      have hPos : 0 < before.val := by dsimp only [before]; omega
      have hPrior : prior = ⟨7-(n+1),by omega⟩ := by
        apply Fin.ext
        change 7-n-1 = 7-(n+1)
        omega
      have hRead : X.MmaReadCell (g,visit.issues before) cell := by
        refine ⟨dst,args before use,List.replicate 4 0,row,col,?_,pvResultCell rfl _ row col⟩
        simpa [hPos] using hIssue before
      have hWrite : X.MmaCell (g,visit.issues prior) cell := by
        refine ⟨dst,args prior use,_,List.replicate 4 0,row,col,hIssue prior,?_⟩
        exact writeCell_no_mask_128 rfl rfl row.isLt row.isLt (pvResultCell rfl _ row col)
      have hEarlier := (mmaAccumulatorMmaSourceDone hp hX hGuard (visit.previous before hPos)
        hRead hWrite (ih (by omega))).2.2
      exact hPrior ▸ hEarlier
  have hStep : (⟨7-(7-step.val),by omega⟩ : Fin 8) = step := by
    apply Fin.ext
    change 7-(7-step.val) = step.val
    have := step.isLt
    omega
  exact hStep ▸ hAll (7-step.val) (by omega)

/-- Completion of the last PV fragment provides the records for all eight operands. -/
theorem PvVisit.operandRecords (hCuQ : Epilogue.DrainCuQProtected p X) {g use index : Nat}
    {block : Fin 4} {row col : Fin 128} (visit : PvVisit l X g block use row col index)
    (hDone : X.async.mmaDone (g,index) = true) (step : Fin 8) :
    ∃ ops, X.async.mmaOperands (g,visit.issues step) = some ops := by
  obtain ⟨ops,hOps,_⟩ := mmaCompletedOperandRecord hX (show X.MmaIssue (g,visit.issues step)
    _ _ _ _ from ⟨_,(visit.fragment step).decoded⟩) (visit.fragmentDone hp hX hCuQ hDone step)
  exact ⟨ops,hOps⟩

/-- With the observed P values and first carry, the issued bank gives the entire
128-key contraction. Every observed V element comes from its launch page. -/
theorem PvVisit.resultOfProbabilities (hFrame : OutputFootprint p X)
    (hCuQ : Epilogue.DrainCuQProtected p X) {g batch use index : Nat} {block : Fin 4}
    {row col : Fin 128} (visit : PvVisit l X g block use row col index) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (weights : Nat → ℝ) (carry : ℝ)
    (hDone : X.async.mmaDone (g,index) = true)
    (hP : ∀ (step : Fin 8) {ops}, X.async.mmaOperands (g,visit.issues step) = some ops →
      ∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row.val k =
        .ok (weights (16*step.val+k))) (hZero : visit.keep = false → carry = 0) :
    let co := Epilogue.assignedCoordinates p batch (g/l.block)
    let firstKey := 128*(trips p batch co.1-1-use/2)
    let cell : Cell := ⟨g/l.block,row.val,outputColumn (pvSite block).stage+col.val⟩
    (visit.keep = true → ∃ source, ReadSource l X .acc source (g,visit.issues 0) cell ∧
      (TcMma.Result l Assumptions.all X source cell (.float .f32 carry) ∨
        StoreValue l X source cell (.float .f32 carry))) →
    TcMma.Result l Assumptions.all X (g,index) cell
      (.float .f32 (carry + ∑ k ∈ Finset.range 128,
        weights k * pvValue p batch co.2 (firstKey+k) col.val)) := by
  dsimp only
  intro hCarry
  let co := Epilogue.assignedCoordinates p batch (g/l.block)
  let firstKey := 128*(trips p batch co.1-1-use/2)
  let dst := outputColumn (pvSite block).stage
  let cell : Cell := ⟨g/l.block,row.val,dst+col.val⟩
  let value (k : Nat) := pvValue p batch co.2 (firstKey+k) col.val
  have hFragments : CellFragments l X (fun step => (g,visit.issues step))
      (fun step => pvOperands l g block step use) dst row.val col.val cell
      visit.keep weights value := by
    refine ⟨fun step => ⟨_,(visit.fragment step).decoded⟩,?_,?_,?_⟩
    · intro step
      exact writeCell_no_mask_128 rfl rfl row.isLt row.isLt (pvResultCell rfl _ row col)
    · intro step
      obtain ⟨ops,hOps⟩ := visit.operandRecords hp hX hCuQ hDone step
      have hIssue : X.MmaIssue (g,visit.issues step) dst (pvOperands l g block step use)
          (visit.keep || decide (0 < step.val)) (List.replicate 4 0) :=
        ⟨_,(visit.fragment step).decoded⟩
      have hV (k : Nat) (hk : k < 16) :
          Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col.val k =
            .ok (value (16*step.val+k)) := by
        obtain ⟨actual,hUse,hVal⟩ := LoaderReady.valueOperandElementOfLaunch hp hX hFrame
          (visit.fragment step) hb hLo hHi col.isLt hk hOps
        rw [hUse.unique (visit.ready step)] at hVal
        let key := firstKey+pvKeyRow step k
        have hMasked : (if key < p.kLength batch then pvValue p batch co.2 key col.val
            else 0) = pvValue p batch co.2 key col.val := by
          by_cases hLive : key < p.kLength batch
          · rw [ite_eq_left hLive]
          · rw [ite_eq_right hLive,pvValue,ite_eq_right hLive]
        exact hVal.trans (congrArg Except.ok hMasked)
      obtain ⟨hValid,hLenA,hLenB⟩ := hX.mma_observation_shape hIssue hOps
      exact ⟨ops,hOps,fun old prev hPrev =>
        evalBf16Cell rfl hValid rfl rfl rfl hLenA hLenB row.isLt col.isLt (hP step hOps) hV hPrev⟩
    · intro step hk
      exact visit.previous step (Nat.pos_of_ne_zero hk)
  simpa only [visit.terminal] using fullFragmentResult hFragments carry hZero hCarry

end PTX.Kernels.TmlFa4Fwd.Protocol
