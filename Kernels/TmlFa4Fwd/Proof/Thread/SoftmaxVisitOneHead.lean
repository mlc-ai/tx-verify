-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasedLoopHead
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasedBodyInputs
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityAck
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityTailCredit
import all Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityElection
import all Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningWaitHistory
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTailRendezvous
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorNotice
import Kernels.TmlFa4Fwd.Proof.SoftmaxCreditReuse
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSoftmaxStages
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Order.ElectOrdinal
import Lemmas.Order.WarpBarOrdinal
import Lemmas.Flow.ElectMask
import Lemmas.Flow.CountTake
import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.ContinuingEvent
import Lemmas.Protocol.ElectCount

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.EventFrame Prologue Epilogue

/-! # The biased loop head of visit one

A lane of a tile with two or more KV blocks enters its first repeated visit at the biased loop
head (pc 5032) right after the opening probability acknowledgement. This file computes the
warp-barrier and election counts at that head. Before the head the lane has acquired exactly one
score generation (the opening one, at pc 3425), so it has not entered the body of either
repeated loop: every event inside a loop body follows a successful score wait of that loop
(the window ledger of `SoftmaxBiasReadyOrder`). Hence the only warp barrier before the head is
the opening tail barrier, and the only election after the opening tail election (pc 4859) and
before the head would have to be a loop election, which is excluded. The opening tail elections
of two lanes of a warp are partners, because a lane executes pc 4859 only once. -/

set_option maxRecDepth 100000 in
private theorem pastElectionNoBack :
    (kernel.code.drop 4860).all (fun i => Thread.staysPastEvent 4860 i.op) = true := by
  kernel_rfl

private theorem pastElectionSegmentFloor : Assumptions.swExp2Sites.all (fun site =>
    match cuteExp2.matchAt kernel site with
    | some seg => decide (4860 ≤ seg.stop)
    | none => false) = true := by kernel_rfl

private def lateElectSite (ins : Instr) (pc : Nat) : Bool :=
  match ins.op with
  | .warp w =>
    match w.kind with
    | .elect => decide (pc < 4860) || pc == 6544 || pc == 7449
    | _ => true
  | _ => true

set_option maxRecDepth 100000 in
private theorem lateElectSites :
    (kernel.code.zipIdx 0).all (fun x => lateElectSite x.1 x.2) = true := by kernel_rfl

/-- The elections at pc 4860 or later are the two repeated tail elections. -/
private theorem electSiteLate {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {pc mask inst lead : Nat}
    (h : X.Elect i pc mask inst lead) : pc < 4860 ∨ pc = 6544 ∨ pc = 7449 := by
  have hGet : X.get i = some ⟨pc,.elect mask inst lead⟩ := h
  obtain ⟨ins,ty,d,q,mk,hCode,hOp,_⟩ :=
    elect_mask (hX.thr _ (event_thread_lt hX hGet)) (List.mem_of_getElem? hGet) rfl
  have hAll := List.all_eq_true.mp lateElectSites (ins,pc)
    (List.mem_zipIdx_iff_getElem?.mpr (by simpa using hCode))
  simp only [lateElectSite,hOp] at hAll
  simpa only [Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq,or_assoc] using hAll

private theorem memTake {X : Execution} {g k : Nat} {e : Event} (h : e ∈ (X.tr g).take k) :
    ∃ j < k, X.get (g,j) = some e := by
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp h
  have hlt := (List.getElem?_eq_some_iff.mp hj).1
  simp only [List.length_take] at hlt
  rw [List.getElem?_take_of_lt (by omega)] at hj
  exact ⟨j,by omega,hj⟩

private theorem getTake {X : Execution} {g j k : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hj : j < k) : e ∈ (X.tr g).take k := by
  apply List.mem_of_getElem? (i := j)
  rw [List.getElem?_take_of_lt hj]
  exact he

/-- A count of a lane's prefix is unchanged over a window of events outside the predicate. -/
private theorem countP_take_window {X : Execution} {g a b : Nat} {mark : Event → Bool}
    (hab : a ≤ b) (hb : b ≤ (X.tr g).length)
    (h : ∀ k e, a ≤ k → k < b → X.get (g,k) = some e → mark e = false) :
    ((X.tr g).take b).countP mark = ((X.tr g).take a).countP mark := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hlt : n < (X.tr g).length := by omega
    have hGet : X.get (g,n) = some (X.tr g)[n] := List.getElem?_eq_getElem hlt
    rw [countP_take_succ_false hGet (h n _ hn (by omega) hGet)]
    exact ih (by omega) (fun k e h1 h2 => h k e h1 (by omega))

/-- Every event after the opening tail election of a lane is at pc 4860 or later. -/
theorem OpeningProbabilityElection.laterEvents {p : Params} {l : Launch} {X : Execution}
    {g : Nat} {stage : Fin 2} (c : OpeningProbabilityElection p l X g stage) {k : Nat}
    {e : Event} (hk : c.barrier.wait.tail.main.main.stored.wait.statistics.index+10 < k)
    (he : X.get (g,k) = some e) : 4860 ≤ e.pc := by
  let start := c.barrier.wait.tail.main.main.stored.wait.statistics.index
  have ht : At (next (next c.barrier.wait.tail.state)) 4859 [] :=
    c.barrier.wait.tail.ready.next.next
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun c.continuation
  have hStart : 4860 ≤
      (tailElectionReturn l g (next (next c.barrier.wait.tail.state)) c.leader).pc := by
    have h := ht.1
    simp only [tailElectionReturn,next,setReg] at h ⊢
    omega
  apply Thread.eventTailEvents pastElectionNoBack pastElectionSegmentFloor hWalk hStart
  apply List.mem_of_getElem? (i := k-(start+11))
  rw [List.getElem?_drop,show start+11+(k-(start+11)) = k by omega]
  exact he

/-- A lane executes the opening tail election site (pc 4859) only once. -/
theorem OpeningProbabilityElection.electionUnique {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X) {g : Nat} {stage : Fin 2}
    (c : OpeningProbabilityElection p l X g stage) {x mask inst lead : Nat}
    (h : X.Elect (g,x) 4859 mask inst lead) :
    x = c.barrier.wait.tail.main.main.stored.wait.statistics.index+10 := by
  let start := c.barrier.wait.tail.main.main.stored.wait.statistics.index
  have hGet : X.get (g,x) = some ⟨4859,.elect mask inst lead⟩ := h
  rcases lt_trichotomy x (start+10) with hlt | heq | hgt
  · exfalso
    have hWait := Thread.traceOrderOfPcFloor hX electionNoBack electionSegmentFloor
      c.barrier.wait.waited hGet (show probabilityWaitPc .first true < 4859 by decide)
      (Nat.le_refl _)
    obtain ⟨pc,hBar⟩ := c.barrier.arrived
    have hx : x = start+9 := by omega
    rw [hx] at hGet
    rw [hGet] at hBar
    cases hBar
  · exact heq
  · exfalso
    have hLate : 4860 ≤ 4859 := c.laterEvents hgt hGet
    omega

/-- The opening tail elections of two lanes of a warp follow equally many elections. -/
theorem OpeningProbabilityElection.electionsAgree {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X) {g h : Nat}
    {stage stage' : Fin 2} (hs : SameWarp l g h) (c : OpeningProbabilityElection p l X g stage)
    (d : OpeningProbabilityElection p l X h stage') :
    elections X g (c.barrier.wait.tail.main.main.stored.wait.statistics.index+10) =
      elections X h (d.barrier.wait.tail.main.main.stored.wait.statistics.index+10) := by
  obtain ⟨x,hPair⟩ := ElectOrd.partner hX hs c.elected (PTX.electMember_full l h)
  obtain ⟨pc,pc',mask,mask',inst,a,b,hy,hx⟩ := hPair
  have hSame := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ hy hx hs).1
  have hPc : pc = 4859 := congrArg Event.pc (Option.some.inj (hy.symm.trans c.elected))
  rw [← hSame,hPc] at hx
  have hIndex := d.electionUnique hX hx
  have hOrd : ElectOrdinal l X :=
    electOrdinal hX (ElectMutual.of_full (fun e => Thread.actualFullElectionMask hX e))
  have hCount := hOrd hs hy hx
  change elections X g _ = elections X h x at hCount
  rw [hCount,hIndex]

/-- Along any path from the initial state, the tail-barrier sites (pcs 4858, 6543, 7448) are
reached at most as often as a score wait succeeds. -/
private theorem tailSitesWithinScores {l : Launch} {g : Nat} {t : TState} {es : List Event}
    (h : TraceReach kernel Assumptions.all l g {} es t) :
    es.countP (fun e => ([4858,6543,7448] : List Nat).contains e.pc) ≤
      es.countP scoreAcquired := by
  have hBound (w : Fin 22) : es.countP (biasReturnMark w) ≤ es.countP (biasAcquireMark w) := by
    have hZ : biasBodyDebt w ({} : TState) = 0 := by fin_cases w <;> rfl
    have hB := biasReadOrderPath w h
    omega
  have hRaw := sumDistinctMarks es 4858 6543 7448 (by decide) (by decide) (by decide)
    (fun _ => true)
  simp only [Bool.true_and] at hRaw
  have hAcq := scoreMarkerSum es
  simp only [statsWindows,Finset.mem_insert,Finset.mem_singleton,Fin.reduceEq,or_self,
    not_false_eq_true,Finset.sum_insert,Finset.sum_singleton] at hAcq
  have h17 := hBound 17
  have h18 := hBound 18
  have h19 := hBound 19
  have r17 : biasReturnMark 17 = fun e => e.pc == 4858 := rfl
  have r18 : biasReturnMark 18 = fun e => e.pc == 6543 := rfl
  have r19 : biasReturnMark 19 = fun e => e.pc == 7448 := rfl
  have a17 : biasAcquireMark 17 = biasAcquireMark 8 := rfl
  have a18 : biasAcquireMark 18 = biasAcquireMark 9 := rfl
  have a19 : biasAcquireMark 19 = biasAcquireMark 10 := rfl
  have hMark : scoreAcquireMark = scoreAcquired := rfl
  rw [r17] at h17
  rw [r18] at h18
  rw [r19] at h19
  rw [a17] at h17
  rw [a18] at h18
  rw [a19] at h19
  rw [hMark] at hAcq
  omega

/-- An event inside the body of a repeated loop (from the score loads to the probability
release) follows a second successful score wait. -/
private theorem loopBodyScores {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j k : Nat} {e : Event}
    (he : X.get (g,k) = some e) (hBody : 5112 ≤ e.pc ∧ e.pc ≤ 6552 ∨ 6679 ≤ e.pc ∧ e.pc ≤ 7457)
    {loc : Loc} {q : Nat} {acq : Bool} {sc : MbarScope}
    (hFirst : X.get (g,j) = some ⟨3425,.wait loc q true acq sc⟩) (hj : j < k) :
    2 ≤ ((X.tr g).take k).countP scoreAcquired := by
  have hAcq := scoreMarkerSum ((X.tr g).take k)
  simp only [statsWindows,Finset.mem_insert,Finset.mem_singleton,Fin.reduceEq,or_self,
    not_false_eq_true,Finset.sum_insert,Finset.sum_singleton] at hAcq
  have hMark : scoreAcquireMark = scoreAcquired := rfl
  rw [hMark] at hAcq
  have h8 : 1 ≤ ((X.tr g).take k).countP (biasAcquireMark 8) :=
    List.countP_pos_iff.mpr ⟨_,getTake hFirst hj,rfl⟩
  rcases hBody with hb | hb
  · have hInside : insideBiasBody 5 e.pc := by
      have h1 : (biasWindowWait 5).pc = 5109 := rfl
      have h2 : biasWindowEnd 5 = 6552 := rfl
      unfold insideBiasBody
      omega
    have hD := windowDebtMatched hX {5} he ⟨5,Finset.mem_singleton_self _,hInside⟩
    simp only [Finset.sum_singleton] at hD
    have a5 : biasAcquireMark 5 = biasAcquireMark 9 := rfl
    rw [a5] at hD
    change ((X.tr g).take k).countP _ + 1 ≤ ((X.tr g).take k).countP _ at hD
    omega
  · have hInside : insideBiasBody 7 e.pc := by
      have h1 : (biasWindowWait 7).pc = 6676 := rfl
      have h2 : biasWindowEnd 7 = 7457 := rfl
      unfold insideBiasBody
      omega
    have hD := windowDebtMatched hX {7} he ⟨7,Finset.mem_singleton_self _,hInside⟩
    simp only [Finset.sum_singleton] at hD
    have a7 : biasAcquireMark 7 = biasAcquireMark 10 := rfl
    rw [a7] at hD
    change ((X.tr g).take k).countP _ + 1 ≤ ((X.tr g).take k).countP _ at hD
    omega

/-- A probability credit before a position counts as an arrival on its object there. -/
theorem probabilityArrivalBefore {l : Launch} {X : Execution} {g i k cta : Nat}
    {stage packet : Fin 2} (h : Thread.Scores.ProbabilityCredit l X (g,i) cta stage packet)
    (hik : i < k) :
    1 ≤ ((X.tr g).take k).countP
      (arrivesOn (Thread.Scores.probabilityObject l cta stage packet)) := by
  obtain ⟨pc,he⟩ := h
  exact List.countP_pos_iff.mpr ⟨_,getTake he hik,by simp [arrivesOn,sourceArrive]⟩

/-- A biased loop head is a head for equal warp and count parameters. -/
theorem BiasedLoopHead.recast {p : Params} {l : Launch} {X : Execution} {g : Nat}
    {warp warp' : Fin 8} {visit block floor counter bars bars' elects elects' : Nat}
    {maximum : Option ℝ} {sum : ℝ}
    (head : BiasedLoopHead p l X g warp visit block floor counter bars elects maximum sum)
    (hw : warp = warp') (hb : bars = bars') (he : elects = elects') :
    ∃ head' : BiasedLoopHead p l X g warp' visit block floor counter bars' elects' maximum sum,
      head'.cursor.pos = head.cursor.pos ∧ head'.blocks = head.blocks ∧
        head'.split = head.split ∧ head'.pastTile = head.pastTile := by
  subst hw hb he
  exact ⟨head,rfl,rfl,rfl,rfl⟩

/-- A lane of a repeated tile reaches the biased loop head of visit one right after its opening
acknowledgement. At the head it has passed exactly one warp barrier and one election more than
before its opening tail election, and the head lies after that election and after the elected
lane's tail credit. -/
theorem OpeningProbabilityAck.visitOneHead {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads) (stage : Fin 2)
    (hRole : warpIndex l g/4 = stage.val) (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (c : OpeningProbabilityElection p l X g stage) (ack : OpeningProbabilityAck l X g) :
    let tile := (assignedCoordinates p batch (g/l.block)).1
    let blocks := Mma.trips p batch tile
    let cap := blocks-stageGeometryBlocks p batch tile stage+10
    let past := p.kLength batch-p.qLength batch+256*tile
    let start := c.barrier.wait.tail.main.main.stored.wait.statistics.index
    ∃ maximum sum, ∃ head : BiasedLoopHead p l X g (warpOf l g) 1 (blocks-1) (past/128)
        (2^32-(blocks-firstPlainSplit blocks cap)) 1 (elections X g (start+10)+1) maximum sum,
      head.blocks = blocks ∧ head.split = firstPlainSplit blocks cap ∧ head.pastTile = past ∧
      start+11 < head.cursor.pos := by
  intro tile blocks cap past start
  have hw : warpIndex l g < 8 := by have := stage.isLt; omega
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  have stageEq : stageOf warp = stage := Fin.ext hRole
  obtain ⟨d,hd⟩ := ack.denominatorOfMaximal hp hMax frame hg stage hRole hb lo hi
  obtain ⟨positive,bound,room⟩ := Mma.trips_bounds hp hb (assignedCoordinates_valid hp lo hi).1
  obtain ⟨_,_,lengthBound⟩ := hp.lengths batch hb
  change blocks ≤ _ at bound
  change 2 ≤ blocks at multiple
  have small : blocks < 2^31-10 := by omega
  have capPos : 0 < cap := by dsimp [cap]; omega
  have capSmall : cap < 2^31 := by dsimp [cap]; omega
  have pastSmall : past+256 < 2^31 := by
    change p.kLength batch-p.qLength batch+256*(tile+1) < 2^31 at room
    simpa only [past,Nat.mul_succ,Nat.add_assoc] using room
  have bias : firstBiasedRepeats blocks cap ≠ 0 := by
    unfold firstBiasedRepeats firstPlainSplit cap
    omega
  -- the four counts the head needs
  have hScoresObj := d.scoreCountOfMaximal hp hMax frame hg stage hRole hb lo hi
  have hScoreCount : ((X.tr g).take d.cursor.pos).countP scoreAcquired = 1 :=
    (scorePollCursor hp hMax.1 stage hRole.symm).symm.trans hScoresObj
  have hNotices : ((X.tr g).take d.cursor.pos).countP Thread.Scores.publishesStats = 1 := by
    have h := d.noticesOfMaximal hp hMax frame hg stage hRole hb lo hi
    rwa [Thread.Scores.beforeNotices] at h
  obtain ⟨loc,parity,hA⟩ := ack.site
  have hCreditStep : ((X.tr g).take (ack.index+1)).countP Thread.Scores.creditAcquired =
      ((X.tr g).take ack.index).countP Thread.Scores.creditAcquired + 1 := by
    obtain ⟨e,he,hMark⟩ := creditObservationOfAcquire ack.acquired
    exact countP_take_succ he hMark
  have hCreditHi : ((X.tr g).take ack.index).countP Thread.Scores.creditAcquired ≤ 1 := by
    have hIdx : ((X.tr g).take (ack.index+1))[ack.index]? =
        some ⟨4874,.wait loc parity true true .cta⟩ := by
      rw [List.getElem?_take_of_lt (by omega)]
      exact hA
    obtain ⟨t,_,hReach,hStep⟩ := ack.recorded.before_event hIdx
    have ht : t.pc = 4874 := (estep_source_pc hStep).symm
    have h := creditCountAtOpeningAck hReach ht
    rwa [List.take_take,Nat.min_eq_left (by omega)] at h
  have hCreditLo : 1 ≤ ((X.tr g).take ack.index).countP Thread.Scores.creditAcquired := by
    obtain ⟨e,hMem,hPub⟩ := List.countP_pos_iff.mp (show 0 < _ by rw [hNotices]; decide)
    obtain ⟨j,hj,he⟩ := memTake hMem
    obtain ⟨round,hRound⟩ := Option.isSome_iff_exists.mp hPub
    have hCredits := creditCursorBeforePublication hp hMax.1
      (show Thread.Scores.Publishes X (g,j) round from ⟨e,he,hRound⟩)
    rw [Thread.Scores.beforeNotices,Thread.Scores.beforeCredits] at hCredits
    change ((X.tr g).take j).countP _ + 1 ≤ ((X.tr g).take j).countP _ at hCredits
    have hMono := countP_take_mono Thread.Scores.creditAcquired (X.tr g)
      (show j ≤ ack.index by rw [hd] at hj; omega)
    omega
  have hCredits : ((X.tr g).take d.cursor.pos).countP Thread.Scores.creditAcquired = 2 := by
    rw [hd]
    omega
  have hScores : okPolls (Thread.Scores.scoreReadyObject l (g/l.block)
      (stageOf ⟨warpIndex l g,hw⟩)) ((X.tr g).take d.cursor.pos) = 1 := by
    rw [show stageOf ⟨warpIndex l g,hw⟩ = stage from stageEq]
    exact hScoresObj
  obtain ⟨head,hPos,_,hBlocks,hSplit,hPast⟩ := d.biasedLoopHead hp hw positive
    (show blocks < 2^31 by omega) capPos capSmall pastSmall bias hScores hNotices hCredits
    hScoreCount
  -- the opening election precedes the acknowledgement
  have hElect : X.get (g,start+10) = some ⟨4859,.elect 4294967295 c.label c.leader⟩ := c.elected
  have hAfter : start+10 < ack.index := Thread.traceOrderOfPcFloor hMax.1 pastElectionNoBack
    pastElectionSegmentFloor hElect hA (show 4859 < 4860 by decide)
    (show 4860 ≤ 4874 by decide)
  have hBound : d.cursor.pos ≤ (X.tr g).length := d.cursor.bounded
  have hPosA : d.cursor.pos = ack.index+1 := hd
  -- exactly one warp barrier before the head
  have hBars : warpBars X g d.cursor.pos = 1 := by
    have hLo : 1 ≤ warpBars X g d.cursor.pos := by
      have hBar : X.WarpBar (g,start+9) 4294967295 c.barrier.label := c.barrier.arrived
      have hStep : warpBars X g (start+9+1) = warpBars X g (start+9)+1 :=
        WarpBar.warpBars_succ hBar
      have hMono := countP_take_mono Execution.isWarpBar (X.tr g)
        (show start+9+1 ≤ d.cursor.pos by omega)
      change warpBars X g (start+9+1) ≤ warpBars X g d.cursor.pos at hMono
      omega
    have hReach := d.cursor.recorded.returning_reach
    have hSites := tailSitesWithinScores hReach
    have hPrior : warpBars X g d.cursor.pos ≤ ((X.tr g).take d.cursor.pos).countP
        (fun e => ([4858,6543,7448] : List Nat).contains e.pc) := by
      apply List.countP_mono_left
      intro e hMem hm
      obtain ⟨k,_,hGet⟩ := memTake hMem
      obtain ⟨source,kind⟩ := e
      cases kind <;> cases hm
      exact List.contains_iff_mem.mpr (Thread.Scores.warpBarrierSite hMax.1 (i := (g,k)) hGet)
    change ((X.tr g).take d.cursor.pos).countP scoreAcquired = 1 at hScoreCount
    omega
  -- no election between the opening tail election and the head
  obtain ⟨j,first⟩ := Progress.openingSoftmaxAcquireOfAllStages hp hMax frame hg stage hRole
    hb lo hi
  have hFirst := first.decoded
  have hj : j < start+10 := c.afterEarlierEvent hMax.1 hFirst
    (show 3425 < 4859 by decide)
  have hElections : elections X g d.cursor.pos = elections X g (start+10)+1 := by
    have hSucc := ElectOrd.elections_succ (show X.Elect (g,start+10) 4859 4294967295 c.label
      c.leader from c.elected)
    have hWindow : elections X g d.cursor.pos = elections X g (start+10+1) := by
      apply countP_take_window (by omega) hBound
      intro k e hk hkPos he
      cases hIs : isElectEv e
      · rfl
      · exfalso
        obtain ⟨pc,kind⟩ := e
        cases kind <;> simp [isElectEv] at hIs
        rename_i mask inst lead
        have hLate : 4860 ≤ pc := c.laterEvents (show start+10 < k by omega) he
        have hSite := electSiteLate hMax.1 (show X.Elect (g,k) pc mask inst lead from he)
        have hTwo := loopBodyScores hMax.1 he (by dsimp only; omega) hFirst (by omega)
        have hMono := countP_take_mono scoreAcquired (X.tr g) (show k ≤ d.cursor.pos by omega)
        omega
    rw [hWindow,hSucc]
  obtain ⟨head',hPos',hBlocks',hSplit',hPast'⟩ := head.recast
    (show warp = warpOf l g from (Fin.ext (warpOf_val hw)).symm) hBars hElections
  exact ⟨_,_,head',hBlocks'.trans hBlocks,hSplit'.trans hSplit,hPast'.trans hPast,by omega⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
