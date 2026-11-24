-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionObservedRescaleEntry
public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditBalance
import Kernels.TmlFa4Fwd.Proof.FirstStatsOrdinal
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Flow.NthEv
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
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

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

private theorem waitMarkCount (stage : Fin 2) (events : List Event) :
    events.countP (correctionStatsWaitMark stage) =
      events.countP (barrierMark (correctionSingleStatsPc stage false)) +
        events.countP (isRescaleStageWait stage) +
        events.countP (barrierMark (correctionSingleStatsPc stage true)) := by
  have hOne (e : Event) : (if correctionStatsWaitMark stage e then 1 else 0) =
      (if barrierMark (correctionSingleStatsPc stage false) e then 1 else 0) +
        (if isRescaleStageWait stage e then 1 else 0) +
        (if barrierMark (correctionSingleStatsPc stage true) e then 1 else 0) := by
    fin_cases stage
    · by_cases ha : e.pc = 7985 <;> by_cases hb : e.pc = 8006 <;> by_cases hc : e.pc = 8465 <;>
        simp [correctionStatsWaitMark_iff, correctionStatsSites, correctionSingleStatsPc,
          isRescaleStageWait, correctionRescaleMarkPc, barrierMark, ha, hb, hc]
    · by_cases ha : e.pc = 7988 <;> by_cases hb : e.pc = 8225 <;> by_cases hc : e.pc = 8761 <;>
        simp [correctionStatsWaitMark_iff, correctionStatsSites, correctionSingleStatsPc,
          isRescaleStageWait, correctionRescaleMarkPc, barrierMark, ha, hb, hc]
  induction events with
  | nil => simp
  | cons e rest ih =>
    simp only [List.countP_cons, ih]
    have he := hOne e
    omega

section
variable {p : Params}

private theorem initialWaitPrefix {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g pos : Nat} (stage : Fin 2)
    (hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (he0 : X.get (g,pos) = some ⟨7985,.bar (statsBarrierId l g 0) (some 64) .sync⟩)
    (heR : X.get (g,pos+1) = some ⟨7987,.arrive ⟨.shared,g/l.block,l.sharedBase+192⟩ 0 1 true .cta⟩)
    (he1 : X.get (g,pos+2) = some ⟨7988,.bar (statsBarrierId l g 1) (some 64) .sync⟩) :
    ((X.tr g).take (pos+3)).countP (correctionStatsWaitMark stage) = 1 := by
  have hSource (stage : Fin 2) :
      ∃ members, NamedBar.Sources l X (some 64) members (statsBarrierId l g stage) := by
    have hw := Nat.mod_lt (warpIndex l g) (by decide : 0 < 4)
    have hs := stage.isLt
    let pair : Fin 8 := ⟨warpIndex l g % 4 + 4*stage.val,by omega⟩
    have hId : 3+pair.val = statsBarrierId l g stage := by simp [pair,statsBarrierId]; omega
    exact ⟨_,hId ▸ statsBarrierSources hp hX pair⟩
  fin_cases stage
  · change ((X.tr g).take (pos+2+1)).countP (correctionStatsWaitMark 0) = 1
    obtain ⟨_,hS⟩ := hSource 0
    have hFirst := firstCorrectionStatsOrdinal hp hX 0 he0 hS
    have hLen : pos < (X.tr g).length := (List.getElem?_eq_some_iff.mp he0).1
    have hZero := (correctionWaitPrefixCount hp hX 0 hLen hWarp).trans hFirst
    rw [countP_take_succ_false he1 (p := correctionStatsWaitMark 0) (by
          apply Bool.eq_false_iff.mpr
          intro h
          have := (correctionStatsWaitMark_iff 0 _).mp h
          simp [correctionStatsSites] at this),
        countP_take_succ_false heR (p := correctionStatsWaitMark 0) (by
          apply Bool.eq_false_iff.mpr
          intro h
          have := (correctionStatsWaitMark_iff 0 _).mp h
          simp [correctionStatsSites] at this),
        countP_take_succ he0 ((correctionStatsWaitMark_iff 0 _).mpr
          (by simp [correctionStatsSites])),
        hZero]
  · change ((X.tr g).take (pos+2+1)).countP (correctionStatsWaitMark 1) = 1
    obtain ⟨_,hS⟩ := hSource 1
    have hFirst := firstCorrectionStatsOrdinal hp hX 1 he1 hS
    have hLen : pos+2 < (X.tr g).length := (List.getElem?_eq_some_iff.mp he1).1
    have hZero := (correctionWaitPrefixCount hp hX 1 hLen hWarp).trans hFirst
    rw [countP_take_succ he1 ((correctionStatsWaitMark_iff 1 _).mpr
      (by simp [correctionStatsSites])),
      hZero]

private theorem firstCreditOrdinal {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g index : Nat} {e : Event}
    (he : X.get (g,index) = some e) (hFirst : e.pc = 7987) :
    (Thread.correctionBefore X (g,index)).count (.statsCredit stage) = 0 := by
  rw [correctionCreditCursor hp hX stage he]
  apply List.countP_eq_zero.mpr
  intro before hBefore hMark
  obtain ⟨pos,hAt⟩ := List.mem_iff_getElem?.mp hBefore
  have hi := (List.getElem?_eq_some_iff.mp he).1
  have hIndex := (List.getElem?_eq_some_iff.mp hAt).1
  change index < (X.tr g).length at hi
  simp only [List.length_take] at hIndex
  have hpIndex : pos < index := by omega
  rw [List.getElem?_take_of_lt hpIndex] at hAt
  obtain ⟨_,hRun⟩ := hX.thr g (Step.CtaBar.thread_lt_of_get hX he)
  obtain ⟨s,u,hStep,hTail⟩ := hRun.after_event (g := g) hAt (by omega)
  have hSrc := correctionCreditReturnsForward stage hStep hMark
  have hSite := (correctionStatsCreditMark_iff stage before).mp hMark
  have hLo : 7988 ≤ u.pc := by
    fin_cases stage <;> simp at hSite <;> omega
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hTail
  have hMember : e ∈ (X.tr g).drop (pos+1) := by
    apply List.mem_of_getElem? (i := index-(pos+1))
    rwa [List.getElem?_drop,Nat.add_sub_of_le (by omega)]
  exact (Nat.not_le_of_lt (by omega)) (correctionEventsAfterFirstRelease hLo hWalk e hMember)

private theorem suffixWaitsBound {l : Launch} {m : Mem0} (hp : Pre p l m) {g batch lane : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads) (stage : Fin 2) {u : TState}
    (ht : At u 7989 (correctionBeforeRescale p l g batch lane)) {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l (warpLane l g lane) u es vs) :
    es.countP (correctionStatsWaitMark stage) ≤
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
  have hBound : 7985 ≤ u.pc := by rw [ht.1]; decide
  have hZero := correctionSingleStatsRankBound stage false hBound hw
  have hOne := correctionSingleStatsBound stage true hBound hw
  have hRepeated := correctionRescaleBoundFromSetup hp hb hLo hHi ht stage hw
  have hInitial : barrierRemaining (correctionSingleStatsPc stage false) u = 0 := by
    unfold barrierRemaining
    rw [ht.1]
    fin_cases stage <;> decide
  rw [hInitial] at hZero
  rw [waitMarkCount]
  have hPos := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).1
  omega

/-- A correction lane's real credit ordinal is bounded by the assigned tile's KV blocks,
including a trace prefix that ends at the credit. -/
theorem correctionCreditsWithinTrips {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {e : Event}
    (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k)) (stage : Fin 2)
    (he : X.get (g,index) = some e)
    (hCredit : Thread.correctionAction e = some (.statsCredit stage)) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      (Thread.correctionBefore X (g,index)).count (.statsCredit stage) ≤
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
  by_cases hFirst : e.pc = 7987
  · obtain ⟨batch,⟨hb,hLo,hHi⟩,_⟩ := tileBatch_existsUnique p hWork
    rw [firstCreditOrdinal hp hX stage he hFirst]
    exact ⟨batch,hb,hLo,hHi,Nat.zero_le _⟩
  obtain ⟨loc,n,heKind⟩ := Thread.correctionStatsCreditKind hCredit
  have hSite := (Thread.correctionStatsCreditObservation stage heKind).mp hCredit
  have hMark := (correctionStatsCreditMark_iff stage e).mpr hSite
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hPc : 7987 ≤ e.pc ∧ e.pc ≤ 8764 := by
    fin_cases stage <;> simp at hSite <;> omega
  have hNoHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hNoHint
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  have hLate : 7988 < e.pc := by fin_cases stage <;> simp at hSite <;> omega
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hThread : warpLane l g lane = g := Nat.sub_add_cancel
    ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have he' : X.get (warpLane l g lane,index) = some e := hThread.symm ▸ he
  obtain ⟨batch,hb,hLo,hHi,ends,sh,votes,active,hActive⟩ :=
    correctionActiveTileOfEvent hp hX hg hWarp.1 hWarp.2 hl hWork (by omega) he'
  have hr := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨u,hU,hReach,he0,heR,he1,hRun⟩ := correctionLaneBeforeRescaleOfEvent
    hp hX hb hLo hHi (active.checkpoint lane hl) hr hUsedK hActive.before hLate he'
  let pos := active.pos lane
  have hWarp' : 8 ≤ warpIndex l (warpLane l g lane) ∧ warpIndex l (warpLane l g lane) < 12 :=
    hThread.symm ▸ hWarp
  have hPrefix := initialWaitPrefix hp hX stage hWarp' he0 heR he1
  obtain ⟨_,hw⟩ := Mma.walkFromRun hRun
  have hBound := suffixWaitsBound hp hb hLo hHi stage hU hw
  rw [hThread] at hPrefix hBound
  change ((X.tr g).drop (pos+6)).countP (correctionStatsWaitMark stage) ≤
    Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 at hBound
  change ((X.tr g).take (pos+6)).countP (correctionStatsWaitMark stage) = 1 at hPrefix
  have hMono := countP_take_mono (correctionStatsWaitMark stage) ((X.tr g).drop (pos+6))
    (Nat.le_max_left (index-(pos+6)) (((X.tr g).drop (pos+6)).length))
  have hDropLen : index-(pos+6) ≤ ((X.tr g).drop (pos+6)).length := by
    have hI := (List.getElem?_eq_some_iff.mp he).1
    change index < (X.tr g).length at hI
    rw [List.length_drop]
    omega
  rw [max_eq_right hDropLen, List.take_length] at hMono
  have hWait := correctionCreditRequiresWait hX stage he hMark
  have hSplit := List.take_add (l := X.tr g) (i := pos+6) (j := index-(pos+6))
  rw [Nat.add_sub_of_le hReach] at hSplit
  rw [← correctionCreditCursor hp hX stage he] at hWait
  rw [hSplit,List.countP_append,hPrefix] at hWait
  exact ⟨batch,hb,hLo,hHi,by omega⟩

private theorem reachWalk {l : Launch} {g : Nat} {s t : TState} {before rest : List Event}
    {tail : List Visit} (h : TraceReach kernel Assumptions.all l g s before t)
    (hw : Walk kernel Assumptions.all l g t rest tail) :
    ∃ vs, Walk kernel Assumptions.all l g s (before ++ rest) vs := by
  induction h with
  | refl => exact ⟨tail,hw⟩
  | tau ht _ ih =>
    obtain ⟨vs,hWalk⟩ := ih hw
    exact ⟨_,.tau ht hWalk⟩
  | event he _ ih =>
    obtain ⟨vs,hWalk⟩ := ih hw
    exact ⟨_,.ev he hWalk⟩

private theorem walkThroughEvent {l : Launch} {g index : Nat} {s : TState}
    {es : List Event} {result : Option TState} {e : Event}
    (hr : Run kernel Assumptions.all l g s es result) (he : es[index]? = some e) :
    ∃ vs, Walk kernel Assumptions.all l g s (es.take index ++ [e]) vs := by
  obtain ⟨t,q,hReach,hStep⟩ := hr.before_event he
  cases q with
  | none => exact reachWalk hReach (.last hStep)
  | some u => exact reachWalk hReach (.ev hStep (.stop u))

private theorem suffixRescaleExact {l : Launch} {m : Mem0} (hp : Pre p l m) {g batch lane : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads) (stage : Fin 2) {s : TState}
    (hs : At s 7989 (correctionBeforeRescale p l g batch lane)) {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l (warpLane l g lane) s es vs) {target : Event}
    (hTarget : target ∈ es) (hLate : 8447 ≤ target.pc) :
    es.countP (isRescaleStageWait stage) =
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 - 1 := by
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let blocks := Mma.trips p batch tile
  have hTrips : blocks ≤ (p.kLength batch + 127) / 128 :=
    (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hK := (hp.lengths batch hb).2.2
  obtain ⟨_,t,hRun,hT⟩ := correctionLaneRescaleSetup hp hb hLo hHi hs
  rcases Mma.advanceWalkLocals hRun hw with rfl | ⟨_,_,_,hRest⟩
  · cases hTarget
  have hEntry : t.pc = (if blocks < 2 then 8447 else 8006) := hT.1
  change es.countP (isRescaleStageWait stage) = blocks-1
  by_cases hSkip : blocks < 2
  · have hPc : t.pc = 8447 := hEntry.trans (ite_eq_left hSkip)
    rw [correctionRescaleMarkedNone stage hPc.ge hRest]
    omega
  have hPc : t.pc = 8006 := hEntry.trans (ite_eq_right hSkip)
  have hSeed : t.regs 7278 = some (b32 (2^32-blocks)) := by
    have h := hT.2.2.2.2
    unfold correctionRescaleSetupFacts at h
    rw [ite_eq_right hSkip] at h
    exact h.1
  obtain ⟨u,first,last,tail,hEs,_,hU,hCount,hWalk⟩ :=
    correctionRescaleMarkedCount stage hPc (by rw [hT.2.1]; decide)
      (Nat.le_of_not_gt hSkip) (by omega) hSeed hRest hTarget hLate
  rw [hEs,List.countP_append,hCount,correctionRescaleMarkedNone stage hU.ge hWalk,Nat.add_zero]
end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {stage : Fin 2}
    (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k))
include hp hX hWork hUsedK

/-- The reached terminal correction wait has one completed named generation for every
block of its selected tile. Subsequence geometry is determined by the protected inputs. -/
theorem terminalWaitOrdinalOfTrips (hWait : Thread.CorrectionWaits X (g,index) .terminal stage) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      (Thread.correctionBefore X (g,index)).barrier (statsBarrierId l g stage) =
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
  obtain ⟨e,he,hAction⟩ := hWait
  have hSite := Thread.correctionTerminalWaitSite hAction
  have hpLate : 8447 ≤ e.pc ∧ e.pc < 9205 := by rw [hSite]; fin_cases stage <;> decide
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hNoHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hNoHint
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hThread : warpLane l g lane = g := Nat.sub_add_cancel
    ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have he' : X.get (warpLane l g lane,index) = some e := hThread.symm ▸ he
  obtain ⟨batch,hb,hLo,hHi,ends,sh,votes,active,hActive⟩ :=
    correctionActiveTileOfEvent hp hX hg hWarp.1 hWarp.2 hl hWork (by omega) he'
  have hr := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨s,hs,hReach,he0,heR,he1,hRun⟩ := correctionLaneBeforeRescaleOfEvent
    hp hX hb hLo hHi (active.checkpoint lane hl) hr hUsedK hActive.before (by omega) he'
  let pos := active.pos lane + 6
  let tr := (X.tr (warpLane l g lane)).drop pos
  let rel := index-pos
  have hWarp' : 8 ≤ warpIndex l (warpLane l g lane) ∧ warpIndex l (warpLane l g lane) < 12 :=
    hThread.symm ▸ hWarp
  have hPrefix := initialWaitPrefix hp hX stage hWarp' he0 heR he1
  have heAt : tr[rel]? = some e := by
    dsimp only [tr,rel]
    rwa [List.getElem?_drop,Nat.add_sub_of_le hReach]
  obtain ⟨visits,hW⟩ := walkThroughEvent hRun heAt
  have hMember : e ∈ tr.take rel ++ [e] := by simp
  have hRepeated := suffixRescaleExact hp hb hLo hHi stage hs hW hMember hpLate.1
  have hRp : isRescaleStageWait stage e = false := by
    apply Bool.eq_false_iff.mpr
    intro hm
    have hPc : e.pc = correctionRescaleMarkPc stage := beq_iff_eq.mp hm
    fin_cases stage <;> simp [correctionRescaleMarkPc] at hPc <;> omega
  have hInit : barrierRemaining (correctionSingleStatsPc stage false) s = 0 := by
    unfold barrierRemaining
    rw [hs.1]
    fin_cases stage <;> decide
  have hBefore : 7985 ≤ s.pc := by rw [hs.1]; decide
  have hNoInitial := correctionSingleStatsRankBound stage false hBefore hW
  have hFinal := correctionSingleStatsBound stage true hBefore hW
  have hTerm : barrierMark (correctionSingleStatsPc stage true) e = true := by
    apply beq_iff_eq.mpr
    rw [hSite]
    fin_cases stage <;> rfl
  simp only [List.countP_append, List.countP_cons, List.countP_nil, hRp, hTerm,
    Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hInit] at hRepeated hNoInitial hFinal
  let blocks := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  change (tr.take rel).countP (isRescaleStageWait stage) = blocks-1 at hRepeated
  have hNone : (tr.take rel).countP (barrierMark (correctionSingleStatsPc stage false)) = 0 := by
    change (tr.take rel).countP (barrierMark (correctionSingleStatsPc stage false)) + _ ≤ 0
      at hNoInitial
    omega
  change (tr.take rel).countP (barrierMark (correctionSingleStatsPc stage true)) + 1 ≤ 1 at hFinal
  have hLen : index < (X.tr (warpLane l g lane)).length := (List.getElem?_eq_some_iff.mp he').1
  have hSplit := List.take_add (l := X.tr (warpLane l g lane)) (i := pos) (j := rel)
  have hAdd : pos+rel = index := Nat.add_sub_of_le hReach
  rw [hAdd] at hSplit
  have hCount : ((X.tr (warpLane l g lane)).take index).countP (correctionStatsWaitMark stage) =
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
    rw [hSplit,List.countP_append]
    change ((X.tr (warpLane l g lane)).take pos).countP (correctionStatsWaitMark stage) +
      (tr.take rel).countP (correctionStatsWaitMark stage) = blocks
    rw [show ((X.tr (warpLane l g lane)).take pos).countP (correctionStatsWaitMark stage) = 1
      from hPrefix,waitMarkCount]
    have hPos : 0 < blocks := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).1
    omega
  rw [correctionWaitPrefixCount hp hX stage hLen hWarp',hThread] at hCount
  exact ⟨batch,hb,hLo,hHi,(Thread.correctionBarrierOrdinal ..).trans hCount⟩

/-- The ordinal of an observed rescale wait is bounded by its tile's actual KV trip count. -/
theorem rescaleWaitOrdinalWithinTrips (hWait : Thread.CorrectionWaits X (g,index) .rescale stage) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      (Thread.correctionBefore X (g,index)).barrier (statsBarrierId l g stage) ≤
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
  obtain ⟨e,he,hAction⟩ := hWait
  have hSite := Thread.correctionRescaleWaitSite hAction
  have hLate : 7988 < e.pc := by rw [hSite]; fin_cases stage <;> decide
  have hEarly : e.pc < 9205 := by rw [hSite]; fin_cases stage <;> decide
  have hMark := (correctionStatsWaitMark_iff stage e).mpr (by
    rw [hSite]; fin_cases stage <;> decide)
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hNoHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hNoHint
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hThread : warpLane l g lane = g := Nat.sub_add_cancel
    ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have he' : X.get (warpLane l g lane,index) = some e := hThread.symm ▸ he
  obtain ⟨batch,hb,hLo,hHi,_,_,_,active,hActive⟩ :=
    correctionActiveTileOfEvent hp hX hg hWarp.1 hWarp.2 hl hWork (by omega) he'
  have hr := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨s,hs,_,he0,heR,he1,hRun⟩ := correctionLaneBeforeRescaleOfEvent
    hp hX hb hLo hHi (active.checkpoint lane hl) hr hUsedK hActive.before hLate he'
  have hWarp' : 8 ≤ warpIndex l (warpLane l g lane) ∧ warpIndex l (warpLane l g lane) < 12 :=
    hThread.symm ▸ hWarp
  have hPrefix := initialWaitPrefix hp hX stage hWarp' he0 heR he1
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hRun
  have hSuffix := suffixWaitsBound hp hb hLo hHi stage hs hWalk
  rw [hThread] at hPrefix hSuffix
  have hTotal : (X.tr g).countP (correctionStatsWaitMark stage) ≤
      1 + Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
    rw [← List.take_append_drop (active.pos lane + 6) (X.tr g), List.countP_append, hPrefix]
    exact Nat.add_le_add_left hSuffix 1
  have hPast : ((X.tr g).take (index+1)).countP (correctionStatsWaitMark stage) ≤
      (X.tr g).countP (correctionStatsWaitMark stage) := (List.take_sublist _ _).countP_le
  change (X.tr g)[index]? = some e at he
  rw [List.take_add_one, he, List.countP_append] at hPast
  have hSingle : (some e).toList.countP (correctionStatsWaitMark stage) = 1 := by
    change [e].countP (correctionStatsWaitMark stage) = 1
    simp [hMark]
  have hLen := (List.getElem?_eq_some_iff.mp he).1
  rw [hSingle, correctionWaitPrefixCount hp hX stage hLen hWarp] at hPast
  rw [Thread.correctionBarrierOrdinal]
  refine ⟨batch,hb,hLo,hHi,?_⟩
  change ((X.tr g).take index).countP (Execution.isBarId (statsBarrierId l g stage)) ≤ _
  omega

/-- A rescale wait follows the initial generation and precedes the terminal one. -/
theorem rescaleWaitOrdinalBoundsBeforeTerminal
    (hWait : Thread.CorrectionWaits X (g,index) .rescale stage) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      0 < (Thread.correctionBefore X (g,index)).barrier (statsBarrierId l g stage) ∧
      (Thread.correctionBefore X (g,index)).barrier (statsBarrierId l g stage) <
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
  obtain ⟨e,he,hAction⟩ := hWait
  have hSite := Thread.correctionRescaleWaitSite hAction
  have hLate : 7988 < e.pc := by rw [hSite]; fin_cases stage <;> decide
  have hEarly : e.pc < 9205 := by rw [hSite]; fin_cases stage <;> decide
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hNoHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hNoHint
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hThread : warpLane l g lane = g := Nat.sub_add_cancel
    ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have he' : X.get (warpLane l g lane,index) = some e := hThread.symm ▸ he
  obtain ⟨batch,hb,hLo,hHi,_,_,_,active,hActive⟩ :=
    correctionActiveTileOfEvent hp hX hg hWarp.1 hWarp.2 hl hWork (by omega) he'
  have hr := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨s,hs,hReach,he0,heR,he1,hRun⟩ := correctionLaneBeforeRescaleOfEvent
    hp hX hb hLo hHi (active.checkpoint lane hl) hr hUsedK hActive.before hLate he'
  have hWarp' : 8 ≤ warpIndex l (warpLane l g lane) ∧ warpIndex l (warpLane l g lane) < 12 :=
    hThread.symm ▸ hWarp
  have hPrefix := initialWaitPrefix hp hX stage hWarp' he0 heR he1
  let pos := active.pos lane + 6
  let tr := (X.tr (warpLane l g lane)).drop pos
  let rel := index-pos
  have heAt : tr[rel]? = some e := by
    dsimp only [tr,rel]
    rwa [List.getElem?_drop,Nat.add_sub_of_le hReach]
  obtain ⟨_,hWalk⟩ := walkThroughEvent hRun heAt
  have hUpper := correctionRescaleBoundFromSetup hp hb hLo hHi hs stage hWalk
  have hMarkRescale : isRescaleStageWait stage e = true := by
    apply beq_iff_eq.mpr
    rw [hSite]
    fin_cases stage <;> decide
  rw [List.countP_append,List.countP_singleton,ite_eq_left hMarkRescale] at hUpper
  have hAt : 7985 ≤ s.pc := by rw [hs.1]; decide
  have hInitial := correctionSingleStatsRankBound stage false hAt hWalk
  have hZero : barrierRemaining (correctionSingleStatsPc stage false) s = 0 := by
    unfold barrierRemaining
    rw [hs.1]
    fin_cases stage <;> decide
  rw [hZero,List.countP_append] at hInitial
  have hNoTerminal : (tr.take rel).countP (barrierMark (correctionSingleStatsPc stage true)) =
      0 := by
    apply List.countP_eq_zero.mpr
    intro f hF hMarkF
    have hPC : f.pc = correctionSingleStatsPc stage true := beq_iff_eq.mp hMarkF
    obtain ⟨j,hGet⟩ := List.mem_iff_getElem?.mp hF
    have hLen := (List.getElem?_eq_some_iff.mp hGet).1
    simp only [List.length_take] at hLen
    have hj : j < rel := by omega
    rw [List.getElem?_take_of_lt hj] at hGet
    change ((X.tr (warpLane l g lane)).drop pos)[j]? = some f at hGet
    rw [List.getElem?_drop] at hGet
    have hFloor : (kernel.code.drop 8447).all (fun i => Thread.staysPastEvent 8447 i.op) =
        true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hSites : ∀ site ∈ Assumptions.swExp2Sites, site < 8447 := by decide
    have hSegment : ∀ site, 8447 ≤ site → site ∈ Assumptions.swExp2Sites →
        ∀ seg, PTX.Assumption.cuteExp2.matchAt kernel site = some seg → 8447 ≤ seg.stop := by
      intro site hLow hMem
      exact False.elim ((Nat.not_le_of_lt (hSites site hMem)) hLow)
    have hPast : pos+j < index := by dsimp [rel] at hj; omega
    have hEarly : e.pc < 8447 := by rw [hSite]; fin_cases stage <;> decide
    have hLate : 8447 ≤ f.pc := by rw [hPC]; fin_cases stage <;> decide
    have hi : index < (X.tr (warpLane l g lane)).length := (List.getElem?_eq_some_iff.mp he').1
    have hg' : warpLane l g lane < l.threads := hThread.symm ▸ hg
    obtain ⟨_,hFull⟩ := hX.thr _ hg'
    have hLe : pos+j+1 ≤ index := by omega
    obtain ⟨start,u,hStep,hTail⟩ := hFull.after_event hGet (lt_of_le_of_lt hLe hi)
    obtain ⟨_,hAfter⟩ := Mma.walkFromRun hTail
    have hHere : 8447 ≤ start.pc := (PTX.EventFrame.estep_source_pc hStep).symm ▸ hLate
    have hMember : e ∈ f :: (X.tr (warpLane l g lane)).drop (pos+j+1) := by
      apply List.mem_cons_of_mem
      apply List.mem_of_getElem? (i := index-(pos+j+1))
      rw [List.getElem?_drop,Nat.add_sub_of_le hLe]
      exact he'
    exact (Nat.not_le_of_lt hEarly) (Thread.eventTailEventsOfSegmentFloor (floor := 8447)
      hFloor hSegment (.ev hStep hAfter) hHere e hMember)
  have hAtLeast : 1 ≤
      ((X.tr (warpLane l g lane)).take index).countP (correctionStatsWaitMark stage) := by
    have hMono := countP_take_mono (correctionStatsWaitMark stage)
      (X.tr (warpLane l g lane)) hReach
    rw [hPrefix] at hMono
    exact hMono
  have hCount : ((X.tr (warpLane l g lane)).take index).countP (correctionStatsWaitMark stage) <
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
    have hSplit := List.take_add (l := X.tr (warpLane l g lane)) (i := pos) (j := rel)
    rw [Nat.add_sub_of_le hReach] at hSplit
    rw [hSplit,List.countP_append]
    change ((X.tr (warpLane l g lane)).take pos).countP (correctionStatsWaitMark stage) + _ < _
    rw [show ((X.tr (warpLane l g lane)).take pos).countP (correctionStatsWaitMark stage) = 1
      from hPrefix,waitMarkCount,hNoTerminal]
    let blocks := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
    change (tr.take rel).countP (isRescaleStageWait stage) + 1 ≤ blocks-1 at hUpper
    change (tr.take rel).countP (barrierMark (correctionSingleStatsPc stage false)) + _ ≤ 0
      at hInitial
    change 1 + ((tr.take rel).countP (barrierMark (correctionSingleStatsPc stage false)) +
      (tr.take rel).countP (isRescaleStageWait stage) + 0) < blocks
    omega
  have hLen := (List.getElem?_eq_some_iff.mp he').1
  rw [correctionWaitPrefixCount hp hX stage hLen hWarp',hThread] at hCount hAtLeast
  have hOrdinal := Thread.correctionBarrierOrdinal (X := X) (i := (g,index))
    (id := statsBarrierId l g stage)
  exact ⟨batch,hb,hLo,hHi,hOrdinal.symm ▸ hAtLeast,hOrdinal.trans_lt hCount⟩

/-- A rescale wait strictly precedes the terminal correction generation for its actual tile. -/
theorem rescaleWaitOrdinalBeforeTerminal (hWait : Thread.CorrectionWaits X (g,index) .rescale stage)
    :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      (Thread.correctionBefore X (g,index)).barrier (statsBarrierId l g stage) <
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
  obtain ⟨batch,hb,hLo,hHi,_,hUpper⟩ :=
    rescaleWaitOrdinalBoundsBeforeTerminal hp hX hWork hUsedK hWait
  exact ⟨batch,hb,hLo,hHi,hUpper⟩
end

private theorem statsWorkFromEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g position : Nat} {e : Event}
    (hLo : 7980 ≤ e.pc) (hHi : e.pc < 9201) (he : X.get (g,position) = some e) :
    g / l.block < tilePrefix p p.batch * p.heads := by
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hNoHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hNoHint
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hThread : warpLane l g lane = g := Nat.sub_add_cancel
    ((Nat.mod_le ..).trans (Nat.mod_le ..))
  exact correctionWorkOfLateEvent hp hX hg hWarp.1 hWarp.2 hl (by omega) hHi
    (hThread.symm ▸ he)

/-- An observed statistics credit was issued for an assigned work tile. -/
theorem statsCreditHasWork {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {credit : EvId} {stage : Fin 2}
    {e : Event}
    (he : X.get credit = some e) (hAction : Thread.correctionAction e = some (.statsCredit stage)) :
    credit.1 / l.block < tilePrefix p p.batch * p.heads := by
  obtain ⟨_, _, hk⟩ := Thread.correctionStatsCreditKind hAction
  have hSite := (Thread.correctionStatsCreditObservation stage hk).mp hAction
  have hBounds : 7980 ≤ e.pc ∧ e.pc < 9201 := by
    fin_cases stage <;> simp at hSite <;> omega
  exact statsWorkFromEvent hp hX hBounds.1 hBounds.2 he

/-- An observed statistics wait was issued for an assigned work tile. -/
theorem statsWaitHasWork {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {stage : Fin 2}
    {round : Thread.CorrectionRound}
    (hWait : Thread.CorrectionWaits X i round stage) :
    i.1 / l.block < tilePrefix p p.batch * p.heads := by
  obtain ⟨e, he, hAction⟩ := hWait
  have hBounds := Thread.correctionStatsWaitSiteBounds hAction
  exact statsWorkFromEvent hp hX hBounds.1 hBounds.2 he

/-- An observed terminal statistics wait was issued for an assigned work tile. -/
theorem terminalStatsWaitHasWork {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {stage : Fin 2}
    (hWait : Thread.CorrectionWaits X i .terminal stage) :
    i.1 / l.block < tilePrefix p p.batch * p.heads :=
  statsWaitHasWork hp hX hWait

end
end PTX.Kernels.TmlFa4Fwd.Correction
