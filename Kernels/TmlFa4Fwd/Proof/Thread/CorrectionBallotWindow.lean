-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Flow.NotClc
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionBallotCounts
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Proof.CorrectionObservedRescaleEntry
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Lemmas.Flow.Final
import Lemmas.Flow.CountTake
import Lemmas.Flow.VoteMask
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Correction

private def isVoteData (e : Event) : Bool := (voteClass e.kind).isSome

private def NotVoteData : Tmpl → Prop
  | .vote .. | .voteMode .. => False
  | _ => True

private theorem widen_notVoteData {A : List Assumption} {site : Nat} {m : Tmpl}
    (h : NotVoteData m) :
    NotVoteData (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

private theorem ofExec_notVoteData {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotVoteData r) :
    NotVoteData (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

private def voteDataOp : Op → Bool
  | .warp w => match w.kind with | .vote .. => true | _ => false
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction fires no vote. -/
private theorem localSregTmpl_notVoteData {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotVoteData (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotVoteData]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
private theorem ruleTmpl_notVoteData {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotVoteData (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notVoteData
  · simp only [NotVoteData]

/-- A conditional template preserves the absence of votes. -/
private theorem ite_notVoteData {c : Prop} [Decidable c] {a b : Tmpl}
    (ha : NotVoteData a) (hb : NotVoteData b) :
    NotVoteData (if c then a else b) := by
  split <;> assumption

/-- A non-vote instruction fires neither kind of vote. -/
private theorem eventTmpl_notVoteData {A : List Assumption} {L : Launch} {g : Nat}
    {t : TState} {op : Op}
    (hop : voteDataOp op = false) : NotVoteData (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notVoteData (op := .int i)
  case move m => exact ruleTmpl_notVoteData (op := .move m)
  case cvt c => exact ruleTmpl_notVoteData (op := .cvt c)
  case warp w =>
    change NotVoteData (warpTmpl L g t w)
    unfold warpTmpl
    split
    all_goals try (simp_all only [voteDataOp])
    all_goals try contradiction
    all_goals try simp only [shflTmpl, reduxTmpl, matchTmpl, activemaskTmpl, electTmpl, warpBarTmpl]
    all_goals repeat' first
      | trivial
      | split
  all_goals simp only [voteDataOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notVoteData
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notVoteData)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, tensorTmpl, tensorMulticast]
       repeat' first
         | trivial
         | (apply ofExec_notVoteData)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notVoteData)
         | split)
    | trivial

private theorem fires_voteData_op {A : List Assumption} {L : Launch} {g : Nat}
    {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t op) e o)
    (hk : isVoteData e = true) : voteDataOp op = true := by
  cases hq : voteDataOp op
  · exfalso
    have hm := eventTmpl_notVoteData (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    cases ek <;> simp only [isVoteData,voteClass, Option.isSome_none, Bool.false_eq_true] at hk
    all_goals
      cases ht : eventTmpl A L g t op <;> rw [ht] at hm hf <;> simp only [NotVoteData] at hm <;>
        simp only [Fires] at hf <;> aesop
  · rfl

private def inRescaleBallotBand (pc : Nat) (op : Op) : Bool :=
  !voteDataOp op || (pc == 8009 || pc == 8228)

set_option maxRecDepth 100000 in
private theorem rescaleBallotBandCode :
    (((kernel.code.drop 7932).take (8447-7932)).zipIdx 7932).all
      (fun (i,pc) => inRescaleBallotBand pc i.op) = true := by kernel_rfl

section
variable {l : Launch} {m : Mem0} {X : Execution}

private theorem voteSiteInRescaleBand (hX : Consistent l kernel Assumptions.all m X) {g j : Nat}
    {e : Event} (he : X.get (g,j) = some e) (hLo : 7932 ≤ e.pc) (hHi : e.pc < 8447)
    (hVote : isVoteData e = true) :
    e.pc = 8009 ∨ e.pc = 8228 := by
  rcases get_source hX he with ⟨_,hf⟩ | ⟨_,ins,_,_,hc,hf⟩
  · simp [hf, isVoteData, voteClass] at hVote
  have hKind := fires_voteData_op hf hVote
  have hGet :
      (((kernel.code.drop 7932).take (8447-7932)).zipIdx 7932)[e.pc - 7932]? =
      some (ins,e.pc) := by
    rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
      Nat.add_sub_of_le hLo,hc]
    rfl
  have hAll := List.all_eq_true.mp rescaleBallotBandCode _ (List.mem_of_getElem? hGet)
  simpa [inRescaleBallotBand,hKind] using hAll

private theorem ballotEventOfTemplate {l : Launch} {g d a pc : Nat} {t : TState}
    {e : Event} {o : Option TState} {neg : Bool} {mask : Opnd}
    (hf : Fires pc (voteTmpl l g t d a neg mask) e o)
    (hNoFault : ∀ fault, e.kind ≠ .ub fault) :
    ∃ a b, e.kind = .vote (2 ^ 32 - 1) a b := by
  unfold voteTmpl at hf
  split at hf
  · split_ifs at hf with hFull
    · obtain ⟨b,hEq,_⟩ := hf
      exact ⟨_, b, hFull.1 ▸ congrArg Event.kind hEq⟩
    · exact (hNoFault _ (congrArg Event.kind hf.1)).elim
  all_goals exact (hNoFault _ (congrArg Event.kind hf.1)).elim

theorem recordedAtRescaleVoteSite (hX : Consistent l kernel Assumptions.all m X) {g j : Nat}
    {e : Event} (he : X.get (g,j) = some e) (hSite : e.pc = 8009 ∨ e.pc = 8228)
    (hNoFault : ∀ fault, e.kind ≠ .ub fault) :
    ∃ a b, e.kind = .vote (2 ^ 32 - 1) a b := by
  rcases get_source hX he with ⟨fault,hf⟩ | ⟨_,ins,_,_,hc,hf⟩
  · exact (hNoFault fault hf).elim
  rcases hSite with h | h
  · rw [h,Flow.code_8009] at hc
    obtain rfl := Option.some.inj hc
    simp only [eventTmpl, warpTmpl_vote] at hf
    exact ballotEventOfTemplate hf hNoFault
  · rw [h,Flow.code_8228] at hc
    obtain rfl := Option.some.inj hc
    simp only [eventTmpl, warpTmpl_vote] at hf
    exact ballotEventOfTemplate hf hNoFault

private theorem rescaleBallotSum {es : List Event} {test : Event → Bool}
    (hClass : ∀ e ∈ es, test e = (isRescaleStageVote 0 e || isRescaleStageVote 1 e)) :
    es.countP test = es.countP (isRescaleStageVote 0) +
      es.countP (isRescaleStageVote 1) := by
  have hDisjoint (e : Event) :
      (if (isRescaleStageVote 0 e || isRescaleStageVote 1 e) then 1 else 0) =
      (if isRescaleStageVote 0 e then 1 else 0) +
        (if isRescaleStageVote 1 e then 1 else 0) := by
    by_cases h0 : e.pc = 8009 <;> by_cases h1 : e.pc = 8228 <;>
      simp_all [isRescaleStageVote, correctionRescaleMarkPc, barrierMark]
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hTail := ih (fun e he => hClass e (List.mem_cons_of_mem _ he))
    simp only [List.countP_cons, hTail, hClass e List.mem_cons_self, hDisjoint]
    omega

private theorem segmentsBelowCorrection (floor : Nat) (hFloor : 7932 ≤ floor)
    (site : Nat) (hLo : floor ≤ site) (hSite : site ∈ Assumptions.swExp2Sites) :
    ∀ seg, PTX.Assumption.cuteExp2.matchAt kernel site = some seg → floor ≤ seg.stop := by
  simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hSite
  omega

set_option maxRecDepth 100000 in
private theorem correctionChosenFloor :
    (kernel.code.drop 7932).all (fun i => staysPastEvent 7932 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem correctionInitialVoteFloor :
    (kernel.code.drop 7989).all (fun i => staysPastEvent 7989 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem correctionFinalizationFloor :
    (kernel.code.drop 8447).all (fun i => staysPastEvent 8447 i.op) = true := by kernel_rfl

private theorem earlierRescaleEventSite (hX : Consistent l kernel Assumptions.all m X)
    {thread pos j : Nat} {x e : Event} (hx : X.get (thread,pos) = some x)
    (he : X.get (thread,j) = some e) (hOrder : pos < j) (hLate : e.pc < 8447) :
    x.pc < 8447 := by
  by_contra! hf
  have h := traceOrderOfSegmentFloor (floor := 8447) hX correctionFinalizationFloor
    (segmentsBelowCorrection 8447 (by decide)) he hx hLate hf
  omega

theorem earlierRescaleEventNotFault (hX : Consistent l kernel Assumptions.all m X)
    {thread pos j : Nat} {x e : Event} (hx : X.get (thread,pos) = some x)
    (he : X.get (thread,j) = some e) (hOrder : pos < j) (bad : Fault) : x.kind ≠ .ub bad := by
  intro h
  obtain ⟨_,hr⟩ := hX.thr thread (event_thread_lt hX hx)
  have hLast := PTX.Flow.Run.end_last hr hx (.inl ⟨bad,h⟩)
  have hJ : j < (X.tr thread).length := len_of_get he
  omega

private theorem fullBallotIsVoteData {x : Event} (h : isFullWarpVote x = true) :
    isVoteData x = true := by
  cases hs : voteClass x.kind <;> simp [isVoteData, isWarpVote, hs] at h ⊢

private theorem fullBallotOfKind {x : Event} {a : Bool} {b : BitVec 32} {mask : Nat}
    (hVote : x.kind = .vote mask a b) : isWarpVote mask x = true := by
  simp [isWarpVote, voteClass, hVote]

private theorem rescaleVoteClassBeforeFinalization (hX : Consistent l kernel Assumptions.all m X)
    {thread pos j : Nat} {x e : Event} (hx : X.get (thread,pos) = some x)
    (he : X.get (thread,j) = some e) (hOrder : pos < j) (hLo : 7932 ≤ x.pc) (hLate : e.pc < 8447) :
    isFullWarpVote x = (isRescaleStageVote 0 x || isRescaleStageVote 1 x) := by
  have hMark : (isRescaleStageVote 0 x || isRescaleStageVote 1 x) = true ↔
      x.pc = 8009 ∨ x.pc = 8228 := by
    simp [isRescaleStageVote, correctionRescaleMarkPc, barrierMark]
  apply Bool.eq_iff_iff.mpr
  rw [hMark]
  constructor
  · intro h
    exact voteSiteInRescaleBand hX hx hLo (earlierRescaleEventSite hX hx he hOrder hLate)
      (fullBallotIsVoteData h)
  · intro h
    obtain ⟨a,b,hVote⟩ := recordedAtRescaleVoteSite hX hx h
      (earlierRescaleEventNotFault hX hx he hOrder)
    exact fullBallotOfKind hVote

private theorem relativeRescaleVoteOrdinal (hX : Consistent l kernel Assumptions.all m X)
    {thread pos j voteBase : Nat} {e : Event} (he : X.get (thread,j) = some e) (hStart : pos ≤ j)
    (hLate : e.pc < 8447) (hFloor : ∀ x ∈ (X.tr thread).drop pos, 7932 ≤ x.pc)
    (hBase : ((X.tr thread).take pos).countP isFullWarpVote = voteBase) :
    let es := ((X.tr thread).drop pos).take (j-pos)
    ((X.tr thread).take j).countP isFullWarpVote =
      voteBase + (es.countP (isRescaleStageVote 0) + es.countP (isRescaleStageVote 1)) := by
  dsimp only
  let remain := (X.tr thread).drop pos
  let es := remain.take (j-pos)
  have hClass (x : Event) (hx : x ∈ es) :
      isFullWarpVote x = (isRescaleStageVote 0 x || isRescaleStageVote 1 x) := by
    obtain ⟨i, hGet⟩ := List.mem_iff_getElem?.mp hx
    have hi : i < j-pos := ((List.getElem?_eq_some_iff.mp hGet).1).trans_le (List.length_take_le ..)
    change (remain.take _)[i]? = some x at hGet
    rw [List.getElem?_take_of_lt hi] at hGet
    have hx' : X.get (thread,pos+i) = some x := by
      change (X.tr thread)[pos+i]? = some x
      rw [← List.getElem?_drop]
      exact hGet
    exact rescaleVoteClassBeforeFinalization hX hx' he (by omega)
      (hFloor x (List.mem_of_getElem? hGet)) hLate
  have hSplit := List.take_add (l := X.tr thread) (i := pos) (j := j-pos)
  rw [Nat.add_sub_of_le hStart] at hSplit
  rw [hSplit,List.countP_append,hBase]
  exact congrArg (voteBase+·) (rescaleBallotSum hClass)

/-- From the common selected cursor to a rescale ballot, the only vote instances are the
two rescale stations. This counts them relative to the scheduler's initial ordinal. -/
theorem correctionRescaleVoteOrdinalFromActive {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X) {g batch shuffles votes : Nat}
    {ends : Nat → Option TState} {lane j : Nat} {e : Event}
    (cur : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch)
      shuffles votes ends) (hFollow : WarpFollowsEvent l X g cur.pos lane j e)
    (hLate : e.pc < 8447) :
    let es := ((X.tr (warpLane l g lane)).drop (cur.pos lane)).take (j - cur.pos lane)
    ((X.tr (warpLane l g lane)).take j).countP isFullWarpVote =
      votes + (es.countP (isRescaleStageVote 0) + es.countP (isRescaleStageVote 1)) := by
  have hAt := cur.checkpoint lane hFollow.lane
  have hRun := (cur.continuation lane hFollow.lane).after_local_nonempty
    (cur.localSteps lane hFollow.lane) hFollow.nonempty
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hRun
  have hFloor := eventTailEventsOfSegmentFloor (floor := 7932) correctionChosenFloor
    (segmentsBelowCorrection 7932 le_rfl) hWalk hAt.1.ge
  exact relativeRescaleVoteOrdinal hX hFollow.get hFollow.before hLate hFloor
    (cur.ordinals.vote lane hFollow.lane)

theorem noRescaleMarkerBeforeInitial (hX : Consistent l kernel Assumptions.all m X) {g k : Nat}
    (hInit : X.get (g,k) = some ⟨7988,.bar (statsBarrierId l g 1) (some 64) .sync⟩) (stage : Fin 2)
    :
    ((X.tr g).take (k+1)).countP (isRescaleStageVote stage) = 0 := by
  apply List.countP_eq_zero.mpr
  intro e hMem hVote
  obtain ⟨i,hGet⟩ := List.mem_iff_getElem?.mp hMem
  have hi : i < k+1 := ((List.getElem?_eq_some_iff.mp hGet).1).trans_le (List.length_take_le ..)
  rw [List.getElem?_take_of_lt hi] at hGet
  have hMark : e.pc = correctionRescaleMarkPc stage + 3 := beq_iff_eq.mp hVote
  have hLate : 7989 ≤ e.pc := by rw [hMark]; fin_cases stage <;> decide
  have hOrder := traceOrderOfSegmentFloor (floor := 7989) hX correctionInitialVoteFloor
    (segmentsBelowCorrection 7989 (by decide)) hInit hGet (show 7988 < 7989 by decide) hLate
  omega
end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g batch shuffles votes : Nat}
    {ends : Nat → Option TState} {lane j : Nat} {e : Event}
    (cur : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch) shuffles votes ends)
    (hFollow : WarpFollowsEvent l X g cur.pos lane j e) (hb : batch < p.batch)
    (hCtaLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hCtaHi : g/l.block < tilePrefix p (batch+1) * p.heads)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k))
include hp hX cur hFollow hb hCtaLo hCtaHi hUsedK

private theorem rescaleBallotWholeBoundOfActive (hLate : 7988 < e.pc) (stage : Fin 2) :
    (X.tr (warpLane l g lane)).countP (isRescaleStageVote stage) ≤
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 - 1 := by
  let thread := warpLane l g lane
  have hRun := (cur.continuation lane hFollow.lane).after_local_nonempty
    (cur.localSteps lane hFollow.lane) hFollow.nonempty
  obtain ⟨u,hU,_,_,_,hInit,hTail⟩ := correctionLaneBeforeRescaleOfEvent hp hX hb hCtaLo hCtaHi
    (cur.checkpoint lane hFollow.lane) hRun hUsedK hFollow.before hLate hFollow.get
  have hPrefix := noRescaleMarkerBeforeInitial hX hInit stage
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hTail
  obtain ⟨_,v,hv,hV⟩ := correctionLaneRescaleSetup hp hb hCtaLo hCtaHi hU
  let blocks := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  change (X.tr thread).countP (isRescaleStageVote stage) ≤ blocks-1
  rw [← List.take_append_drop (cur.pos lane+6) (X.tr thread),List.countP_append,
    show ((X.tr thread).take (cur.pos lane+6)).countP (isRescaleStageVote stage) = 0
      from hPrefix, Nat.zero_add]
  rcases Mma.advanceWalkLocals hv hWalk with hNil | ⟨_,_,_,hRest⟩
  · rw [hNil]
    exact Nat.zero_le _
  have hEntry : v.pc = (if blocks < 2 then 8447 else 8006) := hV.1
  by_cases hSkip : blocks < 2
  · rw [correctionRescaleVoteNone stage (hEntry.trans (ite_eq_left hSkip)).ge hRest]
    exact Nat.zero_le _
  have hPc : v.pc = 8006 := hEntry.trans (ite_eq_right hSkip)
  have hSeed : v.regs 7278 = some (b32 (2^32-blocks)) := by
    have h := hV.2.2.2.2
    unfold correctionRescaleSetupFacts at h
    rw [ite_eq_right hSkip] at h
    exact h.1
  have hK := (hp.lengths batch hb).2.2
  have hTrips : blocks ≤ (p.kLength batch+127)/128 :=
    (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hCtaLo hCtaHi).1).2.1
  rcases correctionRescaleVotePrefix stage hPc (by rw [hV.2.1]; decide)
      (Nat.le_of_not_gt hSkip) (by omega) hSeed hRest with
    ⟨hCount,_⟩ | ⟨out, before, after, tail, hEs, hOut, hCount, _, hAfter⟩
  · exact hCount
  · rw [hEs,List.countP_append,hCount,correctionRescaleVoteNone stage hOut.ge hAfter]
    exact Nat.le_refl _

private theorem rescaleMaskUpperOfActive (hSite : e.pc = 8009 ∨ e.pc = 8228) :
    ((X.tr (warpLane l g lane)).take j).countP isFullWarpVote <
      votes + 2 * (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1) := by
  have hBounds : 7988 < e.pc ∧ e.pc < 8447 := by rcases hSite with h | h <;> omega
  have hCount := correctionRescaleVoteOrdinalFromActive hX cur hFollow hBounds.2
  let es := ((X.tr (warpLane l g lane)).drop (cur.pos lane)).take (j - cur.pos lane)
  have hSplit := List.take_add (l := X.tr (warpLane l g lane))
    (i := cur.pos lane) (j := j-cur.pos lane)
  rw [Nat.add_sub_of_le hFollow.before] at hSplit
  have hBound (stage : Fin 2) := rescaleBallotWholeBoundOfActive hp hX cur hFollow hb hCtaLo
    hCtaHi hUsedK hBounds.1 stage
  have hLe (stage : Fin 2) : es.countP (isRescaleStageVote stage) ≤
      ((X.tr (warpLane l g lane)).take j).countP (isRescaleStageVote stage) := by
    rw [hSplit,List.countP_append]
    exact Nat.le_add_left _ _
  have hMono (stage : Fin 2) := (List.take_sublist (j+1)
    (X.tr (warpLane l g lane))).countP_le (p := isRescaleStageVote stage)
  have hStep : ∃ stage : Fin 2, isRescaleStageVote stage e = true := by
    rcases hSite with h | h
    · exact ⟨0, beq_iff_eq.mpr h⟩
    · exact ⟨1, beq_iff_eq.mpr h⟩
  obtain ⟨stage,hStage⟩ := hStep
  have hNext := countP_take_succ hFollow.get hStage
  have h0 := hBound 0
  have h1 := hBound 1
  have hl0 := hLe 0
  have hl1 := hLe 1
  have hm0 := hMono 0
  have hm1 := hMono 1
  have hmEarly0 := (List.take_sublist j (X.tr (warpLane l g lane))).countP_le
    (p := isRescaleStageVote 0)
  have hmEarly1 := (List.take_sublist j (X.tr (warpLane l g lane))).countP_le
    (p := isRescaleStageVote 1)
  change ((X.tr (warpLane l g lane)).take j).countP isFullWarpVote =
    votes + (es.countP (isRescaleStageVote 0) + es.countP (isRescaleStageVote 1)) at hCount
  fin_cases stage
  · change ((X.tr (warpLane l g lane)).take (j+1)).countP (isRescaleStageVote 0) =
      ((X.tr (warpLane l g lane)).take j).countP (isRescaleStageVote 0) + 1 at hNext
    omega
  · change ((X.tr (warpLane l g lane)).take (j+1)).countP (isRescaleStageVote 1) =
      ((X.tr (warpLane l g lane)).take j).countP (isRescaleStageVote 1) + 1 at hNext
    omega
end


variable {p : Params}

set_option maxHeartbeats 2000000 in
private theorem rescaleMaskLowerOfActiveExit {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g h batch shuffles votes : Nat}
    {ends : Nat → Option TState} {src i j pc : Nat} {e : Event} (hWarp : SameWarp l g h)
    (cur : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch) shuffles votes ends)
    (hFollow : WarpFollowsEvent l X g cur.pos src i e) (hb : batch < p.batch)
    (hCtaLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hCtaHi : g/l.block < tilePrefix p (batch+1) * p.heads) (hLo : 8 ≤ warpIndex l h)
    (hHi : warpIndex l h < 12)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k)) (he : X.get (h,j) = some ⟨pc,.exit⟩) :
    votes + 2 * (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1) ≤
      ((X.tr h).take j).countP isFullWarpVote := by
  obtain rfl := actualExitPc hX he
  let lane := laneOf l h
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = h := Step.warpLane_of_sameWarp hWarp
  have hCur : WarpFollowsEvent l X g cur.pos lane j ⟨9205,.exit⟩ := by
    refine ⟨hl,hLane.symm ▸ he,?_,hFollow.noExit⟩
    by_contra! hj
    exact hFollow.noExit lane hl j hj 9205 (hLane.symm ▸ he)
  have hRun := (cur.continuation lane hl).after_local_nonempty (cur.localSteps lane hl)
    hCur.nonempty
  obtain ⟨_,_,_,_,_,hInit,_⟩ := correctionLaneBeforeRescaleOfEvent hp hX hb hCtaLo hCtaHi
    (cur.checkpoint lane hl) hRun hUsedK hCur.before (show 7988 < 9205 by decide) hCur.get
  have hCTA : g/l.block = h/l.block := hWarp.1.2.2
  have hWork : h/l.block < tilePrefix p p.batch * p.heads := by
    rw [← hCTA]
    exact hCtaHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  have hTotal (stage : Fin 2) : (X.tr h).countP (isRescaleStageVote stage) =
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1 := by
    obtain ⟨b',hB',hLo',hHi',hEq⟩ := correctionRescaleBallotCountOfTail hp hX
      hLo hHi hWork hUsedK he (show 8447 ≤ 9205 by decide) stage
    rw [← hCTA] at hLo' hHi' hEq
    have hGWork : g/l.block < tilePrefix p p.batch * p.heads := hCTA.symm ▸ hWork
    have hSame := ExistsUnique.unique (tileBatch_existsUnique p hGWork)
      ⟨hB',hLo',hHi'⟩ ⟨hb,hCtaLo,hCtaHi⟩
    simpa only [hSame] using hEq
  let es := ((X.tr h).drop (cur.pos lane)).take (j - cur.pos lane)
  have hSplit := List.take_add (l := X.tr h) (i := cur.pos lane) (j := j-cur.pos lane)
  rw [Nat.add_sub_of_le hCur.before] at hSplit
  have hVotes : ((X.tr h).take (cur.pos lane)).countP isFullWarpVote = votes := by
    simpa only [hLane] using cur.ordinals.vote lane hl
  have hEnd := Execution.exit_last hX hWarp.1.2.1 he
  have hCount (stage : Fin 2) : es.countP (isRescaleStageVote stage) =
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1 := by
    have hPrefix := noRescaleMarkerBeforeInitial hX hInit stage
    rw [hLane] at hPrefix
    have hMono := countP_take_mono (isRescaleStageVote stage) (X.tr h)
      (show cur.pos lane ≤ cur.pos lane+5+1 by omega)
    have hZero : ((X.tr h).take (cur.pos lane)).countP (isRescaleStageVote stage) = 0 := by
      change ((X.tr h).take (cur.pos lane+5+1)).countP (isRescaleStageVote stage) = 0 at hPrefix
      omega
    have hBefore := countP_take_succ_false (p := isRescaleStageVote stage) he (by
      fin_cases stage <;> rfl)
    rw [hEnd,List.take_length,hSplit,List.countP_append,hZero,Nat.zero_add] at hBefore
    exact hBefore.symm.trans (hTotal stage)
  have hSub : es.countP (fun e => isRescaleStageVote 0 e || isRescaleStageVote 1 e) ≤
      es.countP isFullWarpVote := by
    apply List.countP_mono_left
    intro x hx hMarker
    obtain ⟨i,hGet⟩ := List.mem_iff_getElem?.mp hx
    have hi : i < j-cur.pos lane := ((List.getElem?_eq_some_iff.mp hGet).1).trans_le
      (List.length_take_le ..)
    change (((X.tr h).drop (cur.pos lane)).take (j-cur.pos lane))[i]? = some x at hGet
    rw [List.getElem?_take_of_lt hi,List.getElem?_drop] at hGet
    have hNoFault (bad : Fault) : x.kind ≠ .ub bad := by
      intro hBad
      obtain ⟨_,hOriginal⟩ := hX.thr h hWarp.1.2.1
      have hLast := PTX.Flow.Run.end_last hOriginal hGet (.inl ⟨bad,hBad⟩)
      have hJ : j < (X.tr h).length := len_of_get he
      omega
    have hSite : x.pc = 8009 ∨ x.pc = 8228 := by
      simpa [isRescaleStageVote,correctionRescaleMarkPc,barrierMark] using hMarker
    obtain ⟨a,b,hBallot⟩ := recordedAtRescaleVoteSite hX hGet hSite hNoFault
    exact fullBallotOfKind hBallot
  rw [rescaleBallotSum (test := fun e => isRescaleStageVote 0 e || isRescaleStageVote 1 e)
    (fun _ _ => rfl),hCount 0,hCount 1] at hSub
  rw [hSplit,List.countP_append,hVotes]
  change _ ≤ votes + es.countP isFullWarpVote
  omega

/-- A full-warp rescale ballot cannot lose a same-warp peer to an early exit. -/
theorem correctionRescaleBallotNoPeerExit {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g h j k pc : Nat} {a : Bool} {b : BitVec 32}
    (hWarp : SameWarp l g h) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k))
    (he : X.get (g,j) = some ⟨pc,.vote (2^32-1) a b⟩) (hSite : pc = 8009 ∨ pc = 8228)
    (hk : X.MaskK voteClass (g,j) (2^32-1) k) :
    ¬ MaskExited voteClass X h (2^32-1) k := by
  let lane := laneOf l g
  let e : Event := ⟨pc,.vote (2^32-1) a b⟩
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hg := hWarp.1.1
  have hSelf : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have he' : X.get (warpLane l g lane,j) = some e := hSelf.symm ▸ he
  have hBounds : 7988 < pc ∧ pc < 9201 := by rcases hSite with h | h <;> omega
  have hWork := correctionWorkOfLateEvent hp hX hg hLo hHi hl (by
    change 7859 < pc; omega) hBounds.2 he'
  obtain ⟨batch,hb,hCtaLo,hCtaHi,ends,shuffles,votes,active,hFollow⟩ :=
    correctionActiveTileOfEvent hp hX hg hLo hHi hl hWork (by change 7884 < pc; omega) he'
  have hUpper := rescaleMaskUpperOfActive hp hX active hFollow hb hCtaLo hCtaHi hUsedK hSite
  rw [hSelf] at hUpper
  have hOrd : ((X.tr g).take j).countP isFullWarpVote = k := hk.2
  rw [hOrd] at hUpper
  rintro ⟨idx,exitPc,hExit,hShort⟩
  have hRole : warpIndex l g = warpIndex l h := hWarp.2
  have hLo' : 8 ≤ warpIndex l h := hRole ▸ hLo
  have hHi' : warpIndex l h < 12 := hRole ▸ hHi
  have hLower := rescaleMaskLowerOfActiveExit hp hX hWarp active hFollow hb hCtaLo hCtaHi
    hLo' hHi' hUsedK hExit
  change ((X.tr h).take idx).countP isFullWarpVote ≤ k at hShort
  omega

end PTX.Kernels.TmlFa4Fwd.Thread
