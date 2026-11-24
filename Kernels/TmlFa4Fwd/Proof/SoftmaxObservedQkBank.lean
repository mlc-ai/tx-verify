-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemScoreLoadProvenance
public import Kernels.TmlFa4Fwd.Proof.MmaQkResult
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaObservedCacheBank
import Kernels.TmlFa4Fwd.Proof.Safety.TmemQkAccumulatorSource
public import Kernels.TmlFa4Fwd.Proof.Safety.QueryFiniteOperands
import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorCompletion
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreValues
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma PTX.Proof Thread Thread.Scores Protocol.Scores Safety
open PTX.Kernels.TmlFa4Fwd.Mma (qkStage qkOperands qkCellResult qkFragment kvStart QkCellInputs
  sharedDescriptor)

/-- The QK fragment bank whose final result an actual score-load cell observes. -/
structure ScoreQkBank (l : Launch) (X : Execution) (load : EvId) (cell : Cell) (stage : Fin 2) where
  seen : ScoreLoadScore l X load stage
  block : Fin 4
  start : Nat
  wait : Nat
  slot : Fin 3
  parity : Nat
  stageMatches : qkStage block = stage
  position : start+9 = seen.commit.2
  ready : Mma.ReadyPoll l X seen.commit.1 wait slot parity true .cta
  fragments : ∀ step : Fin 8, ∃ d operands accum mask,
    QkInstruction X (seen.commit.1,start+step.val) block step d operands accum mask ∧
    TraceBefore X (seen.commit.1,wait) (seen.commit.1,start+step.val)
  read : ReadSource l X .ld (seen.commit.1,start+7) load cell

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The physical score source and the cache acquire of its eight-fragment bank
are selected by the same recorded score commit. -/
theorem observedScoreQkBank (hCuQ : Epilogue.DrainCuQProtected p X) {load : EvId} {cell : Cell}
    {stage : Fin 2} (hLoad : ScoreLoadCell l X load cell stage)
    : Nonempty (ScoreQkBank l X load cell stage) := by
  obtain ⟨seen,source,_,_,_,_,_,_,_,hActor,hAdjacent,_,hRead⟩ :=
    scoreLoadSelectsQk hp hX hCuQ hLoad
  obtain ⟨block,start,wait,slot,parity,hStage,hPosition,hReady,hBank⟩ :=
    seen.score.observedCacheBankAdjacent hp hX
  have hIndex : source.2 = start+7 := by omega
  rw [show source = (seen.commit.1,start+7) from Prod.ext hActor hIndex] at hRead
  exact ⟨⟨seen,block,start,wait,slot,parity,Fin.ext hStage,hPosition,hReady,hBank,hRead⟩⟩

/-- The recorded key address determines every remaining field of the QK operand pair. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.QkInstruction.operandsOfKey {issue : EvId}
    {block : Fin 4} {step : Fin 8} {d use : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hQk : QkInstruction X issue block step d op acc mask)
    (hKey : op.b = sharedDescriptor (kvStart l use+qkFragment step) 16) :
    op = qkOperands l issue.1 block step use := by
  obtain ⟨hd,ha,hLo,hHi,ht⟩ := hQk.queryOperand hp hX
  have hCollector := hQk.issueCollector hX
  obtain ⟨desc,a,b,lo,hi,tmem,collector⟩ := op
  dsimp only at hd ha hLo hHi ht hKey hCollector ⊢
  subst desc a lo hi tmem b collector
  rfl

/-- Once the observed operand bytes are linked to Q and K, every completed score word
is their dot product. Each accumulator uses its preceding fragment in the same bank. -/
theorem ScoreQkBank.wordOfInputs (hCuQ : Epilogue.DrainCuQProtected p X) {g pos : Nat}
    {stage : Fin 2} {round : Round} (quarter : Fin 4) (word : Fin 32) {values : List Value}
    (he : X.get (g,pos) = some
      ⟨scorePc round quarter,.tc (.ld (scoreAddress l g stage quarter) values .s32x32b)⟩)
    (bank : ScoreQkBank l X (g,pos)
      (tcDataCell l g .s32x32b (scoreAddress l g stage quarter) word.val) stage)
    {use batch head firstQ firstK : Nat}
    (hKeys : ∀ (step : Fin 8) {d operands accum mask},
      QkInstruction X (bank.seen.commit.1,bank.start+step.val) bank.block step
        d operands accum mask →
      operands.b = sharedDescriptor (kvStart l use+qkFragment step) 16)
    (hInput : QkCellInputs p l X bank.seen.commit.1 bank.block use batch head firstQ firstK
      (tmemRow l g) (firstScoreColumn quarter word)
      (fun step => (bank.seen.commit.1,bank.start+step.val))) :
    values[word.val]? = some (.float .f32
      (firstScoreDot p l g batch head firstQ firstK quarter word)) := by
  let producer := bank.seen.commit.1
  let row := tmemRow l g
  let col := firstScoreColumn quarter word
  let issues (step : Fin 8) := (producer,bank.start+step.val)
  let addr := scoreAddress l g stage quarter
  let cell := tcDataCell l g .s32x32b addr word.val
  have hCta : producer/l.block = g/l.block := (scoreCommitActor hp hX bank.seen.score).1
  have hCell : cell = ⟨producer/l.block,row.val,scoreColumn (qkStage bank.block)+col.val⟩ := by
    have hFit := scoreColumn_range stage
    have hQ := quarter.isLt
    change tcDataCell l g .s32x32b (2^16*laneBase l g +
      (scoreColumn stage+32*quarter.val)) word.val = _
    rw [tcDataCell_warp32 l g word.val (by omega),hCta,bank.stageMatches]
    simp only [row,col,firstScoreColumn,tmemRow,Nat.add_assoc]
  have hBank (step : Fin 8) :
      QkInstruction X (issues step) bank.block step (scoreColumn (qkStage bank.block))
        (qkOperands l producer bank.block step use) (decide (step.val ≠ 0))
        (List.replicate 4 0) := by
    obtain ⟨d,operands,accum,mask,hIssue,_⟩ := bank.fragments step
    have hDst := hIssue.scoreDestination hp hX
    obtain ⟨hAcc,hMask⟩ := hIssue.issueFlags hX
    rw [← hDst,← hIssue.operandsOfKey hp hX (hKeys step hIssue),← hAcc,← hMask]
    exact hIssue
  have hIssue (step : Fin 8) : X.MmaIssue (issues step) (scoreColumn (qkStage bank.block))
      (qkOperands l producer bank.block step use) (decide (0 < step.val))
      (List.replicate 4 0) := by
    refine ⟨Mma.qkPc bank.block+step.val,?_⟩
    simpa only [Nat.pos_iff_ne_zero] using (hBank step).decoded
  have hRecorded (step : Fin 8) : ∃ ops, X.async.mmaOperands (issues step) = some ops := by
    have hSame : SameCta l (issues step).1 g :=
      ⟨event_thread_lt hX (hBank step).decoded,event_thread_lt hX he,hCta⟩
    have hEarlier : (issues step).2 < bank.seen.commit.2 := by
      have := step.isLt
      have := bank.position
      dsimp only [issues]
      omega
    have hDone := bank.seen.doneBeforeEarlierMma hp hX (hIssue step) hSame hEarlier
    obtain ⟨ops,hOps,_,_,_⟩ := mmaCompletedOperandRecord hX (hIssue step) (hDone.done hX.tcCommit)
    exact ⟨ops,hOps⟩
  have hPrior (step : Fin 8) (hs : step.val ≠ 0) :
      ReadSource l X .acc (issues ⟨step.val-1,by have := step.isLt; omega⟩) (issues step)
        ⟨producer/l.block,row.val,scoreColumn (qkStage bank.block)+col.val⟩ := by
    have hResult := qkResultCell
      (s := qkOperands l producer bank.block step use) rfl (qkStage bank.block) row col
    have hRead := qkAccumulatorReadsPriorFragment hp hX hCuQ (hBank step)
      (Nat.pos_iff_ne_zero.mpr hs) hResult
    have hId : (issues step).2-1 = bank.start+(step.val-1) := by dsimp [issues]; omega
    rwa [hId] at hRead
  have hOutput := qkCellResult hX bank.block row col issues hInput hIssue hRecorded hPrior
  have hResult : Result l Assumptions.all X (producer,bank.start+7) cell
      (.float .f32 (firstScoreDot p l g batch head firstQ firstK quarter word)) := by
    rw [hCell]
    exact hOutput
  obtain ⟨_,_,_,hLen,_⟩ := scoreLoadAddress hp hX round quarter he
  have hLoad : X.TLd (g,pos) addr values .s32x32b := ⟨_,he⟩
  have hLoadCell : LoadCell l X (g,pos) word.val cell :=
    ⟨addr,values,.s32x32b,hLoad,hLen.symm ▸ word.isLt,rfl⟩
  obtain ⟨v,hv,hContains⟩ :=
    hX.tcRead.1 _ _ _ _ _ _ _ _ hLoad hLoadCell bank.read (.inl hResult)
  rcases hContains with ⟨_,rfl⟩ | ⟨hBad,_⟩
  · exact hv
  · cases hBad

/-- The selected Q subboxes supply the Q bytes at every score word in this bank.
The supplied K bytes use the same actual MMA issues. -/
theorem ScoreQkBank.wordOfSelectedQueryInPrefix (hCuQ : Epilogue.DrainCuQProtected p X)
    (hFrame : OutputFootprint p X) {g pos : Nat} {stage : Fin 2} {round : Round} (quarter : Fin 4)
    (word : Fin 32) {values : List Value}
    (he : X.get (g,pos) = some
      ⟨scorePc round quarter,.tc (.ld (scoreAddress l g stage quarter) values .s32x32b)⟩)
    (bank : ScoreQkBank l X (g,pos)
      (tcDataCell l g .s32x32b (scoreAddress l g stage quarter) word.val) stage)
    {use batch firstK : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ bank.seen.commit.1/l.block)
    (hHi : bank.seen.commit.1/l.block < tilePrefix p (batch+1)*p.heads)
    (hKeys : ∀ (step : Fin 8) {d operands accum mask},
      QkInstruction X (bank.seen.commit.1,bank.start+step.val) bank.block step
        d operands accum mask →
      operands.b = sharedDescriptor (kvStart l use+qkFragment step) 16)
    (hKeyBytes : let coords := Epilogue.assignedCoordinates p batch (bank.seen.commit.1/l.block)
      ∀ (step : Fin 8) (k byte : Nat), k < 16 → byte < 2 → ∃ loc,
        let col := (firstScoreColumn quarter word).val
        let index := Mma.qkByteIndex col k byte
        (qkOperands l bank.seen.commit.1 bank.block step use).byteLoc .b index = some loc ∧
        Mma.OperandByteSource l X (bank.seen.commit.1,bank.start+step.val) true index loc
          (if firstK+col < p.kLength batch then
            (Value.float .bf16 (Mma.qkKey p batch coords.2 (firstK+col)
              (16*step.val+k))).byteAt byte
          else AsyncCopy.zeroByte)) :
    let coords := Epilogue.assignedCoordinates p batch (bank.seen.commit.1/l.block)
    let firstQ := p.qOffset batch+256*coords.1+128*stage.val
    values[word.val]? = some (.float .f32
      (firstScoreDot p l g batch coords.2 firstQ firstK quarter word)) := by
  let coords := Epilogue.assignedCoordinates p batch (bank.seen.commit.1/l.block)
  let qBase := p.qOffset batch+256*coords.1
  have hInput : QkCellInputs p l X bank.seen.commit.1 bank.block use batch coords.2
      (qBase+128*(qkStage bank.block).val) firstK (tmemRow l g) (firstScoreColumn quarter word)
      (fun step => (bank.seen.commit.1,bank.start+step.val)) := by
    refine ⟨?_,hKeyBytes⟩
    intro step k byte hk hByte
    obtain ⟨d,operands,accum,mask,hIssue,_⟩ := bank.fragments step
    have hCanonical := hIssue.operandsOfKey hp hX (hKeys step hIssue)
    rw [hCanonical] at hIssue
    exact actualQkQueryByteOfSelectedAcquireInPrefix hp hX hFrame
      hIssue hb hLo hHi (tmemRow l g).isLt hk hByte
  have hValue := bank.wordOfInputs hp hX hCuQ quarter word he hKeys hInput
  change values[word.val]? = some (.float .f32
    (firstScoreDot p l g batch coords.2 (qBase+128*stage.val) firstK quarter word))
  rw [bank.stageMatches] at hValue
  exact hValue

end PTX.Kernels.TmlFa4Fwd.Softmax
