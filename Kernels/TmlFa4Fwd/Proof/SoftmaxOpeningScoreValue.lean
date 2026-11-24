-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.InitialCacheOperandValues
public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedQkBank
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningScoreLoadGeneration
public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedScores
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Safety.TmemQkAccumulatorSource
import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorCompletion

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.TcMma Thread Thread.Scores Protocol.Scores Safety
open PTX.Kernels.TmlFa4Fwd.Mma
open scoped BigOperators

/-- Each opening load returns the canonical selected QK dot, including the first K
tile's zero fill. Its operands and read source are selected by the actual score commit. -/
theorem ScoreQkBank.wordOfOpeningInputs {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hCuQ : Epilogue.DrainCuQProtected p X)
    {g pos batch : Nat} {stage : Fin 2} (q : Fin 4) (word : Fin 32) {vals : List Value}
    (he : X.get (g,pos) = some
      ⟨scorePc .first q,.tc (.ld (scoreAddress l g stage q) vals .s32x32b)⟩)
    (bank : ScoreQkBank l X (g,pos)
      (tcDataCell l g .s32x32b (scoreAddress l g stage q) word.val) stage)
    (hGen : probabilityOrdinal l X (g/l.block) stage 0 (g,pos) = 0)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    let coords := Epilogue.assignedCoordinates p batch (g/l.block)
    let firstQ := p.qOffset batch+256*coords.1+128*stage.val
    let firstK := 128*(trips p batch coords.1-1)
    vals[word.val]? = some (.float .f32
      (firstScoreDot p l g batch coords.2 firstQ firstK q word)) := by
  let producer := bank.seen.commit.1
  let issues (step : Fin 8) := (producer,bank.start+step.val)
  have hCta : producer/l.block = g/l.block := (scoreCommitActor hp hX bank.seen.score).1
  have hBlock : bank.block = initialQkBlock stage := by
    obtain ⟨_,_,_,_,hLast,_⟩ := bank.fragments 7
    have hCommit := bank.seen.score
    have hZero := bank.seen.generation.trans hGen
    rw [← hCta] at hCommit hZero
    exact hCommit.lastFragmentOpeningBlock hp hX hZero hLast (by
      have h := bank.position
      change bank.start+7+2 = bank.seen.commit.2
      omega)
  have hBrief (step : Fin 8) {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
      (hi : QkInstruction X (issues step) bank.block step d op acc mask) :
      op.b = sharedDescriptor (kvStart l 0+qkFragment step) 16 :=
    (hBlock ▸ hi).initialKeyOperand hp hX stage
  let coords := Epilogue.assignedCoordinates p batch (g/l.block)
  let firstQ := p.qOffset batch+256*coords.1+128*stage.val
  let firstK := 128*(trips p batch coords.1-1)
  have hInput : QkCellInputs p l X producer bank.block 0 batch coords.2 firstQ firstK
      (tmemRow l g) (firstScoreColumn q word) issues := by
    constructor
    · intro step k byte hk hByte
      obtain ⟨d,op,acc,mask,hi,_⟩ := bank.fragments step
      have hOp := hi.operandsOfKey hp hX (hBrief step hi)
      have hIssue : QkInstruction X (issues step) bank.block step d
          (qkOperands l producer bank.block step 0) acc mask := hOp ▸ hi
      have hSource := actualQkQueryByteOfSelectedAcquireInPrefix hp hX hFrame hIssue hb
        (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (tmemRow l g).isLt hk hByte
      simpa only [issues,coords,firstQ,hCta,bank.stageMatches] using hSource
    · intro step k byte hk hByte
      obtain ⟨d,op,acc,mask,hi,_⟩ := bank.fragments step
      have hOp := hi.operandsOfKey hp hX (hBrief step hi)
      have hIssue : QkInstruction X (issues step) bank.block step d
          (qkOperands l producer bank.block step 0) acc mask := hOp ▸ hi
      have hInitial : QkInstruction X (issues step) (initialQkBlock stage) step d
          (qkOperands l producer (initialQkBlock stage) step 0) acc mask := hBlock ▸ hIssue
      have hSource := Protocol.LoaderReady.initialKeyOperandByteInPrefix hp hX hFrame hb
        (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) hInitial.initialQueryFragment step
        (firstScoreColumn q word).isLt hk hByte hInitial.mmaIssue
      simpa only [issues,coords,firstK,hCta,hBlock] using hSource
  exact bank.wordOfInputs hp hX hCuQ q word he
    (fun step {_ _ _ _} hIssue => hBrief step hIssue) hInput

end PTX.Kernels.TmlFa4Fwd.Softmax
