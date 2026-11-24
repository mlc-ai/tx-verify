-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstScoreCommitObservation
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstScoreAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitActors
import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityScore
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
public import Kernels.TmlFa4Fwd.Proof.MmaQkQuerySetupReplay
import Kernels.TmlFa4Fwd.Proof.Thread.FirstQueryStatisticsTrace
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Lemmas.Flow.ElectActor
import Lemmas.Flow.MarkedCut
import Lemmas.Order.OrderBaseCausality
import Lemmas.Order.WarpBarOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption PTX.TcMma PTX.AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Mma
open Prologue (warpIndex)

private def scoreEntryBand (pc : Nat) : Prop :=
  (3103 ≤ pc ∧ pc ≤ 3418) ∨ 7733 ≤ pc

private instance (p : Nat) : Decidable (scoreEntryBand p) :=
  inferInstanceAs (Decidable (_ ∨ _))

private def scoreEntryControl (i : Instr) : Bool :=
  (i.op.isLocal || Epilogue.ordinaryEvent i.op) &&
    match i.op with
    | .bra dst _ => decide (scoreEntryBand dst)
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem scoreEntryAudit :
    ((kernel.code.drop 3103).take (3418 - 3103)).all scoreEntryControl = true := by kernel_rfl

private theorem scoreEntryStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 3103 ≤ s.pc) (hHi : s.pc < 3418)
    (hs : WStep kernel Assumptions.all l g s ev u) : scoreEntryBand u.pc := by
  have hCheck {ins : Instr} (he : kernel.code[s.pc]? = some ins) :
      scoreEntryControl ins = true := by
    apply List.all_eq_true.mp scoreEntryAudit _
    apply List.mem_of_getElem? (i := s.pc-3103)
    rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]
  rcases hs with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · obtain ⟨ins,hCode,_,hExec⟩ := Softmax.tauScoreSource ht
    rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hLocal⟩
    · exact .inl ⟨by change 3103 ≤ s.pc+1; omega,by change s.pc+1 ≤ 3418; omega⟩
    · rcases Softmax.scoreExecLocal hLocal with hFrame | ⟨_,hSite,_,_⟩
      · have hPc := hFrame.pc
        have hAudit := (Bool.and_eq_true_iff.mp (hCheck hCode)).2
        cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
        case bra => simpa only [hOp,hPc,decide_eq_true_eq] using hAudit
        case brx => simp [hOp] at hAudit
        all_goals exact .inl ⟨by omega,by omega⟩
      · simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hSite
        omega
  · obtain ⟨ins,hCode,hNoLocal,hFire⟩ := estep_event_source he
    have hOrd := (Bool.and_eq_true_iff.mp (hCheck hCode)).1
    have hFrame := Epilogue.ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g)
      (s := s) (by simpa only [hNoLocal,Bool.false_or] using hOrd)
    rcases callbackFrame_fires hFrame hFire with hPc | hPc <;>
      exact .inl ⟨by omega,by omega⟩

set_option maxRecDepth 100000 in
private theorem emptyScoreFloor :
    (kernel.code.drop 7733).all (fun i => staysPastEvent 7733 i.op) = true := by kernel_rfl

private theorem emptyScoreSegmentFloor (site : Nat) (hLo : 7733 ≤ site)
    (hIn : site ∈ Assumptions.swExp2Sites) :
    ∀ seg, cuteExp2.matchAt kernel site = some seg → 7733 ≤ seg.stop := by
  intro seg hr
  simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hIn
  omega

private theorem activeScoreEntry {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hs : s.pc = 3103) (hw : Walk kernel Assumptions.all l g s es vs)
    {e : Event} (he : e ∈ es) (hBounds : 3418 < e.pc ∧ e.pc < 7733) :
    ∃ t pre rest post, t.pc = 3418 ∧ es = pre++rest ∧ e ∈ rest ∧
      Walk kernel Assumptions.all l g t rest post := by
  obtain ⟨t,pre,rest,post,hList,hIn,_,hCut,_,hTail⟩ :=
    hw.cut_marked (P := fun t => scoreEntryBand t.pc)
      (cut := fun t => t.pc = 3418 ∨ 7733 ≤ t.pc) (fun _ => 0) (fun _ => false)
      (by intros; rfl)
      (fun {s u ev} hP hNo h =>
        let hPc := hP.resolve_right (fun h => hNo (.inr h))
        ⟨scoreEntryStep hPc.1 (lt_of_le_of_ne hPc.2 (fun h => hNo (.inl h))) h,
          by cases ev <;> rfl⟩)
      (by rw [hs]; exact .inl ⟨by decide,by decide⟩)
      he (fun t hP hNo hPc => by
        have hS := hP.resolve_right (fun h => hNo (.inr h))
        omega)
  rcases hCut with hPc | hTailHi
  · exact ⟨t,pre,rest,post,hPc,hList,hIn,hTail⟩
  · have hLate := eventTailEventsOfSegmentFloor emptyScoreFloor emptyScoreSegmentFloor
      hTail hTailHi e hIn
    omega

set_option maxRecDepth 100000 in
private theorem afterScoreWaitFloor :
    (kernel.code.drop 3428).all (fun i => staysPastEvent 3428 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterScoreWaitSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (3428 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem firstScoreWaitBeforeLaterEvent {g i : Nat} {target : Event} (stage : Fin 2)
    (hwGroup : warpIndex l g / 4 = stage.val) (he : X.get (g,i) = some target)
    (hBounds : 3581 < target.pc ∧ target.pc < 7733) :
    ∃ wait, X.get (g,wait) =
      some ⟨3425,.wait (firstScoreObject l (g/l.block) stage) 0 true true .cta⟩ ∧ wait < i := by
  obtain ⟨w,hWarp,pos,s,_,hIndex,hAt,hRun⟩ :=
    Softmax.softmaxBodySuffix hp hX he (by omega)
      (by omega)
  obtain ⟨visits,hWalk⟩ := walkFromRun hRun
  have hIn : target ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := i-pos)
    rwa [List.getElem?_drop,Nat.add_sub_of_le hIndex]
  obtain ⟨t,pre,rest,post,ht,hList,hFound,hTail⟩ :=
    activeScoreEntry hAt.1 hWalk hIn (by omega)
  obtain ⟨pre',gap,tail,obj,hSplit,_⟩ := firstScoreFenceTrace ht hBounds.1 hTail hFound
  let wait := pos+pre.length+pre'.length
  have hGet : X.get (g,wait) = some ⟨3425,.wait obj 0 true true .cta⟩ := by
    change (X.tr g)[pos+pre.length+pre'.length]? = _
    rw [Nat.add_assoc,← List.getElem?_drop,hList,hSplit,
      ← List.append_assoc,← List.length_append,List.getElem?_append_right le_rfl]
    simp
  have hObj := (Softmax.firstScoreWaitAddress hp hX hGet)
  rw [hwGroup] at hObj
  change obj = firstScoreObject l (g/l.block) stage at hObj
  have hBefore := traceOrderOfPcFloor hX afterScoreWaitFloor afterScoreWaitSegments hGet he
    (by decide : 3425 < 3428) (by omega)
  exact ⟨wait,hObj ▸ hGet,hBefore⟩

private theorem probabilityHasFirstScoreWait {g i : Nat} {address : Nat} {vals : List Value}
    {shape : TcShape} (round : Softmax.Round) (quarter : Fin 4) (stage : Fin 2)
    (hwGroup : warpIndex l g / 4 = stage.val)
    (he : X.get (g,i) = some ⟨Softmax.probabilityPc round quarter,.tc (.st address vals shape)⟩) :
    ∃ wait, X.get (g,wait) =
      some ⟨3425,.wait (firstScoreObject l (g/l.block) stage) 0 true true .cta⟩ ∧ wait < i := by
  let target : Event := ⟨Softmax.probabilityPc round quarter,.tc (.st address vals shape)⟩
  have hBounds : 3581 < target.pc ∧ target.pc < 7733 := by
    change 3581 < Softmax.probabilityPc round quarter ∧ Softmax.probabilityPc round quarter < 7733
    cases round <;> fin_cases quarter <;> decide
  exact firstScoreWaitBeforeLaterEvent hp hX stage hwGroup he hBounds

/-- The tail publication's full-warp rendezvous implies that every participating lane
has returned from its first score acquire. -/
theorem firstScoreAcquireOfTailPeer {g : Nat} {credit : EvId} {stage : Fin 2}
    (hSame : SameWarp l g credit.1) (hStage : warpIndex l g / 4 = stage.val)
    (hCredit : Scores.ProbabilityCredit l X credit (g/l.block) stage 1) :
    ∃ j, Scores.FirstScoreAcquire l X (g,j) stage := by
  obtain ⟨round, _, _, _, hElect⟩ := Scores.tailCreditElectionBefore hp hX stage hCredit
  obtain ⟨bar, inst, _, hLeader⟩ := Scores.tailBarrierBeforeElection hX round hElect
  obtain ⟨own, mask, instanceId, _, pc, he⟩ :=
    WarpBar.partner hX (sameWarp_symm hSame) hLeader (Scores.allLanesInTailMask l g)
  have hSites := Scores.warpBarrierSite hX he
  have hBounds : 3581 < pc ∧ pc < 7733 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hSites
    omega
  obtain ⟨wait, hWait, _⟩ := firstScoreWaitBeforeLaterEvent hp hX stage hStage he hBounds
  exact ⟨wait, Scores.FirstScoreAcquire.ofDecoded hWait⟩


omit hp hX in
private def initialScoreFloor (stage : Fin 2) : Nat :=
  if stage = 0 then 2208 else 2270

omit hp hX in
set_option maxRecDepth 100000 in
private theorem initialScoreFloorCode (stage : Fin 2) :
    (kernel.code.drop (initialScoreFloor stage)).all (fun i =>
      staysPastEvent (initialScoreFloor stage) i.op) = true := by
  fin_cases stage <;> kernel_rfl

omit hp hX in
set_option maxRecDepth 100000 in
private theorem initialScoreSegments (stage : Fin 2) :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (initialScoreFloor stage ≤ seg.stop)
      | none => false) = true := by fin_cases stage <;> kernel_rfl

/-- An actual initial fragment precedes every score commit of its CTA and stage. -/
theorem initialScoreIssueBeforeCommit (stage : Fin 2) {mma commit : EvId} {frag : Fin 8}
    {cta d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat} {spec : TcCommit.Spec}
    {rank : Fin 16} (hMma : QkInstruction X mma (initialQkBlock stage) frag d op acc mask)
    (hScore : Scores.ScoreCommit l X commit cta stage spec rank) (hCta : mma.1/l.block = cta)
    : mma.2 < commit.2 := by
  have hMmaGet := hMma.decoded
  obtain ⟨block,hBank,hRecorded⟩ := Scores.scoreCommitSite hp hX hScore
  have hLane := Scores.mmaAndScoreCommitSameThread hp hX ⟨_,hMmaGet⟩ hScore hCta
  have hEarly : qkPc (initialQkBlock stage)+frag.val < initialScoreFloor stage := by
    fin_cases stage <;> fin_cases frag <;> decide
  have hCommitLate : initialScoreFloor stage ≤ (commitSite (qkCommitSite block)).pc := by
    fin_cases stage <;> fin_cases block <;> (first | decide | cases hBank)
  obtain ⟨a,ai⟩ := mma
  obtain ⟨c,ci⟩ := commit
  change a = c at hLane
  subst c
  exact traceOrderOfPcFloor hX (initialScoreFloorCode stage) (initialScoreSegments stage)
    hMmaGet hRecorded hEarly hCommitLate

/-- Every actual probability store follows completion of the stage's initial score fragments. -/
theorem initialScoreDoneBeforeProbabilityStore (stage : Fin 2) {mma store : EvId} {frag : Fin 8}
    {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hMma : QkInstruction X mma (initialQkBlock stage) frag d op acc mask) {cell : Cell}
    (hStore : StoreCell l X store cell)
    (hFootprint : TensorStoreFootprint l store cell (.probability stage))
    (hCta : mma.1/l.block = store.1/l.block) :
    DoneBefore l X mma store := by
  have hMmaGet := hMma.decoded
  obtain ⟨address,values,shape,_,⟨site,hStoreGet⟩,_,_⟩ := hStore
  have hGroup := hFootprint.warpGroup
  obtain ⟨round,quarter,hPc⟩ : ∃ (round : Softmax.Round) (q : Fin 4),
      site = Softmax.probabilityPc round q := by
    rcases tensorStoreSite hX hStoreGet with h | ⟨other,chunk,rfl⟩
    · exact h
    · have hc := correctionStoreWarpGroup hp hX other chunk hStoreGet
      change store.1%l.block/128 = stage.val at hGroup
      have := stage.isLt
      omega
  subst site
  obtain ⟨g,j⟩ := store
  change g%l.block/128 = stage.val at hGroup
  have hWarpGroup : warpIndex l g / 4 = stage.val := by unfold warpIndex; omega
  obtain ⟨wait,hWait,hBefore⟩ :=
    probabilityHasFirstScoreWait hp hX round quarter stage hWarpGroup hStoreGet
  obtain ⟨b,commit,s,rank,hCommit,_,hTarget,hNotified,hObserve⟩ :=
    firstScoreWaitObservesCommit hp hX stage hWait
  let issued : X.MmaIssue mma d op acc mask := ⟨_,hMmaGet⟩
  let score : Scores.ScoreCommit l X commit (g/l.block) stage s rank :=
    ⟨⟨_,hCommit⟩,hTarget⟩
  have hCta' : mma.1/l.block = g/l.block := hCta
  have hLane := Scores.mmaAndScoreCommitSameThread hp hX issued score hCta'
  have hChronological := initialScoreIssueBeforeCommit hp hX stage hMma score hCta'
  have hTracked : TracksMma X mma commit :=
    ⟨hLane,hChronological,.inl ⟨_,_,_,_,issued⟩,s,⟨_,hCommit⟩⟩
  have hWaitOrder := po_of_not_access (show (g,wait).1 = (g,j).1 from rfl) hBefore
    (len_of_get hStoreGet) (by rw [hStoreGet]; rfl)
  have hScope : SameCta l mma.1 g :=
    ⟨event_thread_lt hX hMmaGet,event_thread_lt hX hWait,hCta⟩
  exact .inl ⟨(g,wait),.cta,
    ⟨_,_,⟨commit,s,rank,rfl,hTracked,⟨_,hCommit⟩,hTarget,hNotified⟩,hObserve⟩,
    MbarRing.Unit.Gate.scopesMeet hScope .cluster .cta,.single (.inl hWaitOrder)⟩

end PTX.Kernels.TmlFa4Fwd.Thread
