-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxProbabilityGate
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityScore
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFragmentHistory
public import Core.Tc.TcMmaOrder
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Thread.TmemDelayedLoadCompletion
import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReuseTrace
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.TmemOrdinaryLoadOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQkDestination
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.Thread.QkIssueFlags
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Lemmas.Order.OrderBaseCausality
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTmemCells
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.TcMma PTX.AsyncCopy Softmax Prologue
open PTX.Kernels.TmlFa4Fwd.Mma

/-- An observed softmax score load and the Tensor Memory cell of one actual register. -/
@[no_expose] def ScoreLoadCell (l : Launch) (X : Execution) (load : EvId)
    (cell : Cell) (stage : Fin 2) : Prop :=
  ∃ (round : Softmax.Round) (quarter : Fin 4) (address : Nat) (words : List Value)
    (shape : TcShape) (j : Nat),
    X.get load = some ⟨scorePc round quarter,.tc (.ld address words shape)⟩ ∧
    j < words.length ∧ cell = tcDataCell l load.1 shape address j ∧
    warpIndex l load.1 / 4 = stage.val

/-- The matched stage is the actual score warp's group. -/
theorem ScoreLoadCell.ofDecoded {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {load : EvId} {cell : Cell} (round : Softmax.Round) (quarter : Fin 4)
    {address : Nat} {words : List Value} {shape : TcShape} {j : Nat}
    (he : X.get load = some ⟨scorePc round quarter,.tc (.ld address words shape)⟩)
    (hj : j < words.length) (hc : cell = tcDataCell l load.1 shape address j) :
    ∃ stage, ScoreLoadCell l X load cell stage := by
  obtain ⟨w,hWarp,_,_,_⟩ := scoreLoadAddress hp hX round quarter he
  exact ⟨stageOf w,round,quarter,address,words,shape,j,he,hj,hc,by rw [← hWarp]; rfl⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} {load : EvId} {cell : Cell}
    {stage : Fin 2} (h : ScoreLoadCell l X load cell stage) (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include h hp hX

/-- The actual score read is in the issuer CTA's score row. -/
theorem ScoreLoadCell.geometry :
    ∃ col : Fin 128, cell = ⟨load.1/l.block,tmemRow l load.1,scoreColumn stage+col.val⟩ := by
  obtain ⟨round,quarter,address,words,shape,j,he,hJ,hCell,hStage⟩ := h
  obtain ⟨w,hWarp,rfl,hLength,rfl⟩ := scoreLoadAddress hp hX round quarter he
  have hS : stageOf w = stage := by
    apply Fin.ext
    change w.val/4 = stage.val
    rwa [hWarp]
  rw [hS] at hCell
  rw [hLength] at hJ
  let col : Fin 128 := ⟨32*quarter.val+j,by have := quarter.isLt; omega⟩
  refine ⟨col,?_⟩
  rw [hCell,scoreAddress,tcDataCell_warp32 _ _ _ (by
    have := scoreColumn_range stage
    have := quarter.isLt
    omega)]
  simp only [col,tmemRow,Nat.add_assoc]

/-- The lane's successful score wait is indexed by its previous probability credits. -/
theorem ScoreLoadCell.acquire :
    let n := probabilityOrdinal l X (load.1/l.block) stage 0 load
    let object := scoreReadyObject l (load.1/l.block) stage
    let wait := (load.1,MbarRing.Poll.nth X object load.1 n)
    n < okPolls object (X.tr load.1) ∧
      warpIndex l load.1 < 8 ∧ warpIndex l load.1/4 = stage.val ∧
      ScoreAcquire X wait object ∧ Resumes kernel X wait load := by
  obtain ⟨g,i⟩ := load
  obtain ⟨round,quarter,address,words,shape,j,he,hJ,hCell,hStage⟩ := h
  change warpIndex l g / 4 = stage.val at hStage
  have hWarp : warpIndex l g < 8 := by have := stage.isLt; omega
  obtain ⟨k,⟨site,kind⟩,q,acq,scope,hGet,hKind,hOrd,hResume⟩ :=
    softmaxScoreLoadScorePoll hp hX stage hWarp hStage round quarter he
  change kind = _ at hKind
  subst kind
  obtain ⟨rfl,rfl⟩ := successfulScoreWaitIsAcquire hp hX stage hWarp hGet
  have hNth := MbarRing.Poll.nth_eq hGet
  rw [hOrd] at hNth
  have hHas : probabilityOrdinal l X (g/l.block) stage 0 (g,i) <
      okPolls (scoreReadyObject l (g/l.block) stage) (X.tr g) := by
    apply MbarRing.Poll.nth_present.mp
    rw [hNth]
    exact ⟨_,hGet⟩
  dsimp only
  rw [hNth]
  exact ⟨hHas,hWarp,hStage,⟨_,_,hGet,rfl⟩,hResume⟩

/-- The observed commit identifies its last QK fragment and bounds every earlier
MMA issue on that elected lane by the final fragment's trace position. -/
theorem ScoreLoadCell.qkCandidateAdjacent {commit : EvId} {spec : TcCommit.Spec} {rank : Fin 16}
    (hScore : ScoreCommit l X commit (load.1/l.block) stage spec rank) :
    ∃ source block d op acc mask,
      qkStage block = stage ∧ QkInstruction X source block 7 d op acc mask ∧
      X.MmaCell source cell ∧ SameCta l source.1 load.1 ∧ source.1 = commit.1 ∧
      source.2+2 = commit.2 ∧
      ∀ {writer wd wo wa wm}, X.MmaIssue writer wd wo wa wm →
        writer.1 = commit.1 → writer.2 < commit.2 → writer.2 ≤ source.2 := by
  obtain ⟨col,rfl⟩ := h.geometry hp hX
  obtain ⟨_,_,_,_,_,_,hRead,_,_,_⟩ := h
  obtain ⟨block,hStage,he⟩ := scoreCommitSite hp hX hScore
  have hBank : qkStage block = stage := Fin.ext hStage
  obtain ⟨g,i⟩ := commit
  obtain ⟨k,hK,d,op,acc,mask,hQk⟩ := qkLastFragmentAdjacentToScoreCommit hp hX block he
  obtain ⟨_,inst,leader,hElect,_⟩ := scoreCommitLeader hp hX block he
  have hOwner := (scoreCommitActor hp hX hScore).1
  have hOp := hQk.queryOperand hp hX
  let row := tmemRow l load.1
  have hResult := hQk.scoreCell hp hX row col
  rw [hBank,hOwner] at hResult
  have hWrite := writeCell_no_mask_128
    (show op.descriptor.group = .one by rw [hOp.descriptor]; rfl)
    (show op.descriptor.m = 128 by rw [hOp.descriptor]; rfl) row.isLt row.isLt hResult
  have hFields := hQk.issueFlags hX
  rw [← hFields.2] at hWrite
  let hIssue : X.MmaIssue (g,k) d op acc mask := ⟨_,hQk.decoded⟩
  refine ⟨(g,k),block,d,op,acc,mask,hBank,hQk,⟨d,op,acc,mask,row.val,col.val,hIssue,hWrite⟩,
    ⟨event_thread_lt hX hQk.decoded,event_thread_lt hX hRead,hOwner⟩,rfl,hK,?_⟩
  rintro ⟨other,j⟩ wd wo wa wm ⟨pc,hWriter⟩ hLane hBefore
  change other = g at hLane
  subst other
  by_contra! hAfter
  have hj : j = i-1 := by dsimp at hBefore hAfter; omega
  rw [hj] at hWriter
  change X.get (g,i-1) = some ⟨_,.elect _ inst leader⟩ at hElect
  rw [hWriter] at hElect
  cases congrArg Event.kind (Option.some.inj hElect)

/-- The final QK fragment precedes its observed commit and every earlier issue is bounded by it. -/
theorem ScoreLoadCell.qkCandidateExact {commit : EvId} {spec : TcCommit.Spec} {rank : Fin 16}
    (hScore : ScoreCommit l X commit (load.1/l.block) stage spec rank) :
    ∃ source block d op acc mask,
      qkStage block = stage ∧ QkInstruction X source block 7 d op acc mask ∧
      X.MmaCell source cell ∧ SameCta l source.1 load.1 ∧ source.1 = commit.1 ∧
      source.2 < commit.2 ∧
      ∀ {writer wd wo wa wm}, X.MmaIssue writer wd wo wa wm →
        writer.1 = commit.1 → writer.2 < commit.2 → writer.2 ≤ source.2 := by

  obtain ⟨source,block,d,op,acc,mask,hStage,hQk,hCell,hCta,hThread,hPos,hEarlier⟩ :=
    h.qkCandidateAdjacent hp hX hScore
  exact ⟨source,block,d,op,acc,mask,hStage,hQk,hCell,hCta,hThread,by omega,hEarlier⟩

/-- The observed commit pins an actual final QK fragment with every cell it used to publish. -/
theorem ScoreLoadCell.qkCandidate {commit : EvId} {spec : TcCommit.Spec} {rank : Fin 16}
    (hScore : ScoreCommit l X commit (load.1/l.block) stage spec rank) :
    ∃ source d op acc mask, X.MmaIssue source d op acc mask ∧ X.MmaCell source cell ∧
      SameCta l source.1 load.1 ∧ source.2 < commit.2 := by

  obtain ⟨source,_,d,op,acc,mask,_,hQk,hCell,hCta,_,hBefore,_⟩ :=
    h.qkCandidateExact hp hX hScore
  exact ⟨source,d,op,acc,mask,⟨_,hQk.decoded⟩,hCell,hCta,hBefore⟩
end

/-- The score load's implicit or deferred wait is recorded before a later joint credit. -/
theorem ScoreLoadCell.waitThroughCredit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} {load credit consumer : EvId} {cell : Cell} {stage : Fin 2}
    (h : ScoreLoadCell l X load cell stage) (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
    (hCredit : ProbabilityCredit l X credit (load.1/l.block) stage 0)
    (hLane : credit.1 = load.1)
    (hOrd : probabilityOrdinal l X (load.1/l.block) stage 0 load ≤
      probabilityOrdinal l X (load.1/l.block) stage 0 credit)
    (hCausal : baseCausality l X credit consumer) :
    WaitBefore l X .waitLd load consumer := by
  obtain ⟨round,quarter,address,words,shape,j,he,hJ,hCell,hStage⟩ := h
  have hBefore := eventBeforeProbabilityCredit he rfl hCredit hLane hOrd
  cases round with
  | first =>
    exact delayedScoreLoadWaitThroughCredit hp hX
      (DelayedScoreLoad.of_decoded (repeated := false) he) hCredit hBefore hCausal
  | biased =>
    exact delayedScoreLoadWaitThroughCredit hp hX
      (DelayedScoreLoad.of_decoded (repeated := true) he) hCredit hBefore hCausal
  | unbiased =>
    have hData := DataflowLoad.of_decoded
      ((by decide : ∀ q, scorePc .unbiased q ∈ Assumptions.tcLdDataflowSites) quarter) he
    obtain ⟨_,hCredit⟩ := hCredit
    exact dataflowLoadWaitThroughEvent hX hData hCredit hBefore (by intro h; cases h) hCausal

/-- A competing MMA writer of an observed score cell belongs to the same score tile. -/
theorem ScoreLoadCell.mmaWriter {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} {load writer : EvId} {cell : Cell} {stage : Fin 2}
    (h : ScoreLoadCell l X load cell stage) (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hWrite : X.MmaCell writer cell) :
    ∃ block frag d op acc mask, qkStage block = stage ∧
      QkInstruction X writer block frag d op acc mask ∧ SameCta l writer.1 load.1 := by
  obtain ⟨col,rfl⟩ := h.geometry hp hX
  obtain ⟨_,_,_,_,_,_,hRead,_,_,_⟩ := h
  obtain ⟨d,op,acc,mask,row,col',hIssue,hWrite⟩ := hWrite
  have hResult := writeCell_resultCell hWrite
  obtain ⟨hr,hc⟩ := resultCell_rowcol hResult
  rcases actualMmaInstruction hX hIssue with ⟨block,frag,hQk⟩ | ⟨block,frag,hPv⟩
  · have hDesc := (hQk.queryOperand hp hX).descriptor
    rw [hDesc] at hr hc
    have hCells := Option.some.inj (hResult.symm.trans (hQk.scoreCell hp hX ⟨row,hr⟩ ⟨col',hc⟩))
    have hOwner := congrArg Cell.cta hCells
    have hColumn := congrArg Cell.column hCells
    have hTile : qkStage block = stage := by
      apply Fin.ext
      change scoreColumn stage+col.val = scoreColumn (qkStage block)+col' at hColumn
      unfold scoreColumn at hColumn
      have hc' : col' < 128 := hc
      have := col.isLt
      omega
    exact ⟨block,frag,d,op,acc,mask,hTile,hQk,event_thread_lt hX hQk.decoded,
      event_thread_lt hX hRead,hOwner.symm⟩
  · obtain ⟨_,_,hDesc,_,_⟩ := hPv.valueOperand hp hX
    rw [hDesc] at hr hc
    have hCells := Option.some.inj (hResult.symm.trans (hPv.outputCell hp hX ⟨row,hr⟩ ⟨col',hc⟩))
    have hColumn := congrArg Cell.column hCells
    change scoreColumn stage+col.val = outputColumn (pvSite block).stage+col' at hColumn
    have hScore := scoreColumn_range stage
    have := col.isLt
    unfold outputColumn at hColumn
    omega

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {load store : EvId} {cell : Cell} {stage : Fin 2}
    (hLoad : ScoreLoadCell l X load cell stage) (hStore : StoreCell l X store cell)
include hp hX hLoad hStore

/-- Every ordinary store aliasing a score cell is a same-lane probability store. -/
theorem scoreLoadStoreScope :
    store.1 = load.1 ∧ Nonempty (TensorStoreFootprint l store cell (.probability stage)) := by
  obtain ⟨col,hCell⟩ := hLoad.geometry hp hX
  obtain ⟨tile,hFoot⟩ := tensorStoreFootprint hp hX hStore
  have hStoreLo := hFoot.columnLo
  have hStoreHi := hFoot.columnHi
  rw [hCell] at hStoreLo hStoreHi
  have hTile : tile = .probability stage := by
    have hScore := scoreColumn_range stage
    have hCol := col.isLt
    cases tile with
    | probability k =>
      simp only [TensorStoreTile.columns,probabilityColumn,scoreColumn] at hStoreLo hStoreHi
      have hk : k = stage := Fin.ext (by omega)
      rw [hk]
    | rescale k =>
      simp only [TensorStoreTile.columns,outputColumn] at hStoreLo
      omega
  subst tile
  obtain ⟨_,_,_,_,_,_,_,_,_,hStage⟩ := hLoad
  have hCta : store.1/l.block = load.1/l.block :=
    hFoot.cta.symm.trans (congrArg Cell.cta hCell)
  have hRow : TmlFa4Fwd.Correction.rowOf l store.1 = (tmemRow l load.1).val :=
    hFoot.lane.symm.trans (congrArg Cell.lane hCell)
  have hGroup : store.1%l.block/128 = stage.val := hFoot.warpGroup
  have hLane : store.1 = load.1 := by
    unfold warpIndex at hStage
    have hLoadRow : (tmemRow l load.1).val = load.1 % l.block % 128 := by
      change load.1%l.block/32%4*32+load.1%l.block%32 = load.1%l.block%128
      omega
    rw [hLoadRow] at hRow
    unfold TmlFa4Fwd.Correction.rowOf at hRow
    rw [hp.block] at hGroup hStage hRow hCta
    have hA := Nat.mod_add_div store.1 512
    have hB := Nat.mod_add_div load.1 512
    omega
  exact ⟨hLane,⟨hFoot⟩⟩

/-- Probabilities overwrite part of the score row, on the very lane that reads it. -/
theorem scoreLoadStoreOrdered :
    WriteBefore l X store load ∨ ReadBefore l X .ld load store := by

  obtain ⟨hLane,_⟩ := scoreLoadStoreScope hp hX hLoad hStore
  obtain ⟨_,_,address,words,shape,_,he,_,_,_⟩ := hLoad
  obtain ⟨a,vs,s,_,hSt,_,_⟩ := hStore
  exact tensorLoadStoreOrderedOnThread hX ⟨address,words,shape,_,he⟩ ⟨a,vs,s,hSt⟩ hLane

/-- A probability store before a load is separated from it by an additional score acquire. -/
theorem scoreLoadStoreCursor (hBefore : store.2 < load.2) :
    let object := scoreReadyObject l (load.1/l.block) stage
    okPolls object ((X.tr store.1).take store.2) <
      okPolls object ((X.tr load.1).take load.2) := by
  obtain ⟨hLane,⟨hFoot⟩⟩ := scoreLoadStoreScope hp hX hLoad hStore
  obtain ⟨round,q,addr,vals,shape,_,hGet,_,_,hStage⟩ := hLoad
  obtain ⟨stAddr,stVals,stShape,_,⟨pc,hSt⟩,_,_⟩ := hStore
  obtain ⟨previous,q',hPc⟩ : ∃ r : Softmax.Round, ∃ q' : Fin 4,
      pc = Softmax.probabilityPc r q' := by
    rcases tensorStoreSite hX hSt with h | ⟨other,chunk,rfl⟩
    · exact h
    · have h := correctionStoreWarpGroup hp hX other chunk hSt
      have hGroup : store.1 % l.block / 128 = stage.val := hFoot.warpGroup
      have hStage := stage.isLt
      omega
  subst pc
  have hBefore' : store.2 < load.2 := hBefore
  have hSt' : X.get (load.1,store.2) = some
      ⟨Softmax.probabilityPc previous q',.tc (.st stAddr stVals stShape)⟩ := by
    simpa [← hLane] using hSt
  have hRaw := scoreLoadAfterStoreHasNewWait hX round previous q q' hSt' hGet hBefore'
  have hEq : phaseAcquired true = scoreAcquireMark := by
    funext e
    rw [scoreReadyMarkKind]
    rfl
  rw [← hEq] at hRaw
  have hW : warpIndex l load.1 < 8 := by
    change warpIndex l load.1/4 = stage.val at hStage
    have := stage.isLt
    omega
  rw [scoreCount (j := store.2) hp hX stage hW rfl hStage,
    scoreCount (j := load.2) hp hX stage hW rfl hStage] at hRaw
  simpa only [hLane] using hRaw

/-- The load is pipeline-ordered before a same-cell probability store issued after it. -/
theorem scoreLoadBeforeLaterProbabilityStore (hLater : load.2 ≤ store.2) :
    ReadBefore l X .ld load store := by
  obtain ⟨hLane,_⟩ := scoreLoadStoreScope hp hX hLoad hStore
  obtain ⟨_,_,address,words,shape,_,hRd,_,_,_⟩ := hLoad
  obtain ⟨stAddr,stVals,stShape,_,⟨pc,hWr⟩,_,_⟩ := hStore
  have hOrder : load.2 < store.2 := by
    rcases lt_or_eq_of_le hLater with h | h
    · exact h
    · rw [Prod.ext hLane.symm h,hWr] at hRd
      have hBad : False :=
        TcKind.noConfusion (Kind.tc.inj (congrArg Event.kind (Option.some.inj hRd)))
      exact hBad.elim
  have hWarp : SameWarp l load.1 store.1 :=
    ⟨⟨event_thread_lt hX hRd,event_thread_lt hX hWr,congrArg (· / l.block) hLane.symm⟩,
      congrArg (warpIndex l) hLane.symm⟩
  have hPo := po_of_not_access hLane.symm hOrder (len_of_get hWr) (by rw [hWr]; rfl)
  exact .inr ⟨hWarp,.inl (.single (.inl hPo)),⟨address,words,shape,_,hRd⟩,
    ⟨stAddr,stVals,stShape,pc,hWr⟩⟩
end

/-- The score load's successful poll is the latest prior poll of its stage. -/
theorem ScoreLoadCell.pollCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {load : EvId} {cell : Cell} {stage : Fin 2} (hLoad : ScoreLoadCell l X load cell stage) :
    okPolls (scoreReadyObject l (load.1/l.block) stage) ((X.tr load.1).take load.2) =
      probabilityOrdinal l X (load.1/l.block) stage 0 load+1 := by
  obtain ⟨round,q,_,_,_,_,he,_,_,hStage⟩ := hLoad
  have hWarp : warpIndex l load.1 < 8 := by
    change warpIndex l load.1/4 = stage.val at hStage
    have := stage.isLt
    omega
  change X.get (load.1,load.2) = _ at he
  exact scoreLoadExactCursor hp hX stage hWarp hStage round q he

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
