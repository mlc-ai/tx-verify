-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.BiasBarrierProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.SharedReadSites
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasPhase
public import Lemmas.Async.AsyncMBarrier
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
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Lemmas.Protocol.CountNth
import Lemmas.Order.DependencyWitness
import Kernels.TmlFa4Fwd.Proof.PollSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Flow PTX.MBarrier PTX.AsyncCopy PTX.EventFrame PTX.Assumption
open Prologue Epilogue Thread.Loader
open PTX.Kernels.TmlFa4Fwd.Softmax

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem biasBarrierAtEvent (repeated : Bool) {g j : Nat} {e : Event}
    (he : X.get (g,j) = some e) (hSite : e.pc = (if repeated then 5271 else 3583))
    (hLength : j+1 < (X.tr g).length) :
    e.kind = .bar (11+warpIndex l g/4) (some 128) .sync := by
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨s,u,hStep,_⟩ := hRun.after_event he (by omega)
  have hPc := (estep_source_pc hStep).symm.trans hSite
  have hDecode : ∃ ins, kernel.code[s.pc]? = some ins ∧ barOp ins.op = true := by
    rw [hPc]
    cases repeated
    · exact ⟨_,Flow.code_3583,rfl⟩
    · exact ⟨_,Flow.code_5271,rfl⟩
  obtain ⟨ins,hCode,hBar⟩ := hDecode
  obtain ⟨_,id,count,mode,hKind⟩ := markedBarrierContinues rfl hCode hBar hStep
  have he' : X.get (g,j) = some ⟨(if repeated then 5271 else 3583),.bar id count mode⟩ := by
    convert he using 2
    obtain ⟨site,kind⟩ := e
    change site = _ at hSite
    change kind = _ at hKind
    rw [hSite,hKind]
  obtain ⟨_,hCount,hMode,_,_⟩ := actualNamedBarrier hp hX he'
  have hId := (actualBiasBarrierStage hp hX repeated he').2
  rw [hCount,hMode,hId] at hKind
  cases repeated <;> exact hKind

private theorem markerIsBiasBarrier (stage : Fin 2) {i : EvId} {e : Event} (he : X.get i = some e)
    (hMark : Execution.isBarId (11+stage.val) e = true) :
    BarrierArrival X i (11+stage.val) (some 128) .sync ∧
      (e.pc = 3583 ∨ e.pc = 5271) := by
  obtain ⟨site,kind⟩ := e
  cases kind <;> try cases hMark
  rename_i id count mode
  have hId : id = 11+stage.val := by simpa [Execution.isBarId] using hMark
  subst id
  have hIds : 11+stage.val = 11 ∨ 11+stage.val = 12 := by fin_cases stage <;> decide
  have hArrival : BarrierArrival X i (11+stage.val) count mode := ⟨_,he,rfl⟩
  obtain ⟨_,_,rfl,rfl⟩ := biasArrivalStage hp hX hIds hArrival
  obtain ⟨hSite,hCount,_,_,_⟩ := actualNamedBarrier hp hX he
  exact ⟨hArrival,biasCountSite hSite hCount.symm⟩

/-- A real stage rendezvous requires a successful Bias-ready wait in this lane. -/
theorem biasReadyCountOfRendezvous (stage : Fin 2) {g j : Nat} {mode : BarMode}
    (hBar : BarrierArrival X (g,j) (11+stage.val) (some 128) mode) :
    0 < okPolls (biasReadyObject l (g/l.block) stage) (X.tr g) := by
  obtain ⟨event,he,hKind⟩ := hBar
  have hMark : Execution.isBarId (11+stage.val) event = true := by
    simp [Execution.isBarId,hKind]
  have hSite := (markerIsBiasBarrier hp hX stage he hMark).2
  have hId : 11+stage.val = 11 ∨ 11+stage.val = 12 := by fin_cases stage <;> decide
  obtain ⟨hw,hStage,_,_⟩ := biasArrivalStage hp hX hId ⟨event,he,hKind⟩
  have hIndex : warpIndex l g/4 = stage.val := by
    change 11+stage.val = 11+warpIndex l g/4 at hStage
    omega
  have hPositive := biasRendezvousHasReadySuccess hX he hSite
  rw [Thread.Softmax.softmaxBiasSourceCount hp hX stage hw rfl hIndex] at hPositive
  exact hPositive.trans_le (List.IsPrefix.countP_le (List.take_prefix _ _))

omit hp hX in
set_option maxRecDepth 100000 in
private theorem afterInitialBiasRendezvous :
    (kernel.code.drop 3583).all (fun i => Thread.staysPastEvent 3583 i.op) = true := by kernel_rfl

omit hp hX in
set_option maxRecDepth 100000 in
private theorem afterInitialBiasRendezvousSegments :
    Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | some seg => decide (3583 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

omit hp hX in
/-- Lane events below the initial Bias rendezvous boundary precede every event
recorded at or above that boundary. -/
theorem orderAtInitialBiasRendezvous {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {a b : Event} (ha : X.get (g,i) = some a) (hb : X.get (g,j) = some b)
    (hBefore : a.pc < 3583) (hAfter : 3583 ≤ b.pc) : i < j :=
  traceOrderOfPcFloor hX afterInitialBiasRendezvous afterInitialBiasRendezvousSegments
    ha hb hBefore hAfter

/-- An initial Bias vector load precedes every arrival on its stage rendezvous. -/
theorem initialBiasReadOrdinal (stage : Fin 2) {i : EvId} {v : Fin 16} {a : Acc}
    {bytes : List (Option Byte)} (hRead : BiasVectorRead X i false v a bytes) :
    observedBarrierOrdinal X i (11+stage.val) = 0 := by
  obtain ⟨g,read⟩ := i
  apply List.countP_eq_zero.mpr
  intro e hMem hMarker
  obtain ⟨k,hGet⟩ := List.mem_iff_getElem?.mp hMem
  have hLen := (List.getElem?_eq_some_iff.mp hGet).1
  rw [List.length_take] at hLen
  have hBefore : k < read := by omega
  rw [List.getElem?_take_of_lt hBefore] at hGet
  change X.get (g,k) = some e at hGet
  have hSite := (markerIsBiasBarrier hp hX stage (i := (g,k)) hGet hMarker).2
  have hFloor : 3583 ≤ e.pc := by omega
  have hPc : biasReadPc false v < 3583 := by fin_cases v <;> decide
  have hPast := orderAtInitialBiasRendezvous hX hRead hGet hPc hFloor
  omega

/-- The Bias read's stage rendezvous ordinal is below its own successful wait count. -/
theorem biasReadReadyBudget (stage : Fin 2) {i : EvId} {repeated : Bool} {v : Fin 16} {a : Acc}
    {bytes : List (Option Byte)} (hRead : BiasVectorRead X i repeated v a bytes)
    (hWarp : warpIndex l i.1 < 8) (hStage : warpIndex l i.1/4 = stage.val) :
    observedBarrierOrdinal X i (11+stage.val) <
      okPolls (biasReadyObject l (i.1/l.block) stage) ((X.tr i.1).take i.2) := by
  obtain ⟨g,j⟩ := i
  have h := biasReadRendezvousBudget hX repeated v hRead
  let past := (X.tr g).take j
  have hMarkLe : past.countP (Execution.isBarId (11+stage.val)) ≤
      past.countP (fun e => e.pc == 3583 || e.pc == 5271) := by
    apply List.countP_mono_left
    intro e hMem hMark
    obtain ⟨k,hGet⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hMem)
    have hP := (markerIsBiasBarrier hp hX stage (i := (g,k)) hGet hMark).2
    simp only [Bool.or_eq_true,beq_iff_eq]
    exact hP
  have hEither : past.countP (fun e => e.pc == 3583 || e.pc == 5271) ≤
      past.countP (fun e => e.pc == 3583) + past.countP (fun e => e.pc == 5271) := by
    induction past with
    | nil => exact Nat.zero_le _
    | cons e prior ih =>
      simp only [List.countP_cons]
      cases a : e.pc == 3583 <;> cases b : e.pc == 5271 <;> simp_all <;> omega
  have hCount := Thread.Softmax.softmaxBiasSourceCount hp hX (j := j) stage hWarp rfl hStage
  change past.countP (fun e => e.pc == 3583) + past.countP (fun e => e.pc == 5271) + 1 ≤
    past.countP readSuccess at h
  change past.countP readSuccess = okPolls (biasReadyObject l (g/l.block) stage) past at hCount
  change past.countP (Execution.isBarId (11+stage.val)) <
    okPolls (biasReadyObject l (g/l.block) stage) past
  rw [← hCount]
  omega

/-- The read's rendezvous is recorded in its lane whenever that lane has already exited. -/
theorem biasReadRendezvousOfExit (stage : Fin 2) {i : EvId} {repeated : Bool} {v : Fin 16} {a : Acc}
    {bytes : List (Option Byte)} (hRead : BiasVectorRead X i repeated v a bytes)
    (hStage : warpIndex l i.1/4 = stage.val) (hExit : Exited X i.1) :
    ∃ j, BarrierArrival X (i.1,j) (11+stage.val) (some 128) .sync ∧
      observedBarrierOrdinal X (i.1,j) (11+stage.val) =
        observedBarrierOrdinal X i (11+stage.val) := by
  obtain ⟨g,read⟩ := i
  obtain ⟨finish,⟨site,kind⟩,hGet,hKind⟩ := hExit
  change kind = .exit at hKind
  subst kind
  have hSite := actualExitPc hX hGet
  subst site
  have hLast := Execution.exit_last hX (event_thread_lt hX hGet) hGet
  change finish + 1 = (X.tr g).length at hLast
  have hReadLen : read < (X.tr g).length := len_of_get hRead
  have hNe : read ≠ finish := by
    intro heq
    subst finish
    have hEq := congrArg Event.kind (Option.some.inj (hRead.symm.trans hGet))
    cases hEq
  have hAfter : read < finish := by omega
  obtain ⟨bar,e,_,hBar,hEvent,hPc,hNone⟩ :=
    biasReadRendezvousBefore hX repeated v hRead hGet hAfter (by cases repeated <;> decide)
  have hLen : finish < (X.tr g).length := len_of_get hGet
  have hKind := biasBarrierAtEvent hp hX repeated hEvent hPc (by omega)
  change warpIndex l g/4 = stage.val at hStage
  rw [hStage] at hKind
  refine ⟨bar,⟨e,hEvent,hKind⟩,?_⟩
  have countUnchanged (n : Nat) (hLo : read ≤ n) (hHi : n ≤ bar) :
      observedBarrierOrdinal X (g,n) (11+stage.val) =
      observedBarrierOrdinal X (g,read) (11+stage.val) := by
    induction n with
    | zero =>
      have h : read = 0 := by omega
      simp [h]
    | succ n ih =>
      rcases Nat.eq_or_lt_of_le hLo with h | h
      · rw [h]
      · have hLt : n < bar := by omega
        have hIn : n < (X.tr g).length := hLt.trans (len_of_get hEvent)
        let before := (X.tr g)[n]
        have hBefore : (X.tr g)[n]? = some before :=
          List.getElem?_eq_some_iff.mpr ⟨hIn,rfl⟩
        have hMark : Execution.isBarId (11+stage.val) before = false := by
          cases hh : Execution.isBarId (11+stage.val) before
          · rfl
          have hBefore' : X.get (g,n) = some before := hBefore
          have hP := (markerIsBiasBarrier hp hX stage hBefore' hh).2
          exact (hP.elim (hNone n before (by omega) hLt hBefore').1
            (hNone n before (by omega) hLt hBefore').2).elim
        unfold observedBarrierOrdinal at *
        rw [List.take_add_one,hBefore,Option.toList_some,List.countP_append]
        simp [hMark,ih (by omega) (by omega)]
  exact countUnchanged bar (by omega) le_rfl

private theorem returnMarkerForm {cta : Nat} (stage : Fin 2) {i : EvId} {e : Event}
    (he : X.get i = some e) (hMark : arrivesOn (biasEmptyObject l cta stage) e = true) :
    X.Arrive i (biasEmptyObject l cta stage) 0 1 true .cta := by
  obtain ⟨site,kind⟩ := e
  obtain ⟨tx,count,rel,scope,hKind⟩ := arrivesOn_form hMark
  change kind = _ at hKind
  subst kind
  have hSite := actualBiasEmptyArrivalSite hp hX stage he rfl
  obtain ⟨rfl,rfl,rfl,rfl,_,_⟩ := biasEmptyArriveFacts hp hX he hSite
  exact ⟨site,he⟩

private theorem biasReturnRendezvous {cta : Nat} (stage : Fin 2) {issue : EvId}
    (hIssue : X.Arrive issue (biasEmptyObject l cta stage) 0 1 true .cta) :
    ∃ k, k+1 = issue.2 ∧ BarrierArrival X (issue.1,k) (11+stage.val) (some 128) .sync := by
  obtain ⟨g,j⟩ := issue
  obtain ⟨site,he⟩ := hIssue
  have hSite := actualBiasEmptyArrivalSite hp hX stage he rfl
  have hAddr := congrArg Loc.addr (biasEmptyArriveFacts hp hX he hSite).2.2.2.2.2
  change l.sharedBase + (336+8*stage.val) = l.sharedBase + (336+8*(warpIndex l g/4)) at hAddr
  have hStage : warpIndex l g/4 = stage.val := by omega
  have pick (repeated : Bool)
      (hc : site = (if repeated then 5271 else 3583) + 7) :
      ∃ k, k+1 = j ∧ BarrierArrival X (g,k) (11+stage.val) (some 128) .sync := by
    obtain ⟨k,e,hK,hAt,hBefore⟩ := biasCorridorPrecedingEvent hX repeated true he hc
    simp only [↓reduceIte,Nat.sub_zero] at hBefore
    have hLen : j < (X.tr g).length := len_of_get he
    have hKind := biasBarrierAtEvent hp hX repeated hAt hBefore (by omega)
    rw [hStage] at hKind
    exact ⟨k,hK,⟨e,hAt,hKind⟩⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite
  exact hSite.elim (pick false) (pick true)

/-- Every earlier unit Bias return has a separate stage rendezvous in its issuing lane. -/
theorem biasReturnRendezvousBudget {cta : Nat} (stage : Fin 2) {issue : EvId}
    (hIssue : X.Arrive issue (biasEmptyObject l cta stage) 0 1 true .cta) :
    ∃ k, k+1 = issue.2 ∧ BarrierArrival X (issue.1,k) (11+stage.val) (some 128) .sync ∧
      arrivals (biasEmptyObject l cta stage) ((X.tr issue.1).take issue.2) ≤
        observedBarrierOrdinal X (issue.1,k) (11+stage.val) := by
  classical
  obtain ⟨g,j⟩ := issue
  obtain ⟨k,hK,hBar⟩ := biasReturnRendezvous hp hX stage hIssue
  let tr := X.tr g
  let isReturn := arrivesOn (biasEmptyObject l cta stage)
  let isBarrier := Execution.isBarId (11+stage.val)
  let returns := (Finset.range j).filter (fun n => (tr[n]?).any isReturn = true)
  let rendezvous := (Finset.range k).filter (fun n => (tr[n]?).any isBarrier = true)
  have hOrigin (n : Nat) (hn : n ∈ returns) : 0 < n ∧ n-1 ∈ rendezvous := by
    obtain ⟨hRange,hMark⟩ := Finset.mem_filter.mp hn
    cases he : tr[n]? with
    | none => simp [he] at hMark
    | some e =>
      have hm : isReturn e = true := by simpa only [he,Option.any_some] using hMark
      have hr := returnMarkerForm hp hX stage (i := (g,n)) he hm
      obtain ⟨prior,hPrior,⟨event,hGet,hKind⟩⟩ := biasReturnRendezvous hp hX stage hr
      change prior+1 = n at hPrior
      have hIndex : prior = n-1 := by omega
      subst prior
      change tr[n-1]? = some event at hGet
      have hN := Finset.mem_range.mp hRange
      change k+1 = j at hK
      exact ⟨by omega,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        by simp [hGet,isBarrier,Execution.isBarId,hKind]⟩⟩
  have hCard := Finset.card_le_card_of_injOn (fun n => n-1)
    (fun n hn => (hOrigin n hn).2) (fun a ha b hb h => by
      have := (hOrigin a ha).1
      have := (hOrigin b hb).1
      change a-1 = b-1 at h
      omega)
  refine ⟨k,hK,hBar,?_⟩
  rw [show arrivals (biasEmptyObject l cta stage) (tr.take j) = returns.card from
      MbarRing.Slot.countP_take_card tr isReturn j,
    show observedBarrierOrdinal X (g,k) (11+stage.val) = rendezvous.card from
      MbarRing.Slot.countP_take_card tr isBarrier k]
  exact hCard

private theorem biasFenceOfRendezvous (stage : Fin 2) {g j : Nat} {mode : BarMode}
    (hBar : BarrierArrival X (g,j) (11+stage.val) (some 128) mode) :
    ∃ k, k+1 = j ∧ X.IsProxyFence (g,k) (.async (some (.shared .cta))) none := by
  obtain ⟨e,he,hKind⟩ := hBar
  have hMark : Execution.isBarId (11+stage.val) e = true := by
    simp [Execution.isBarId,hKind]
  have hSite := (markerIsBiasBarrier hp hX stage he hMark).2
  have decideSite (repeated : Bool) (hPc : e.pc = (if repeated then 5271 else 3583)) :
      ∃ k, k+1 = j ∧ X.IsProxyFence (g,k) (.async (some (.shared .cta))) none := by
    obtain ⟨k,prior,hK,hGet,hBefore⟩ :=
      biasCorridorPrecedingEvent hX repeated false he (by exact hPc)
    have hLen : j < (X.tr g).length := len_of_get he
    obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX hGet)
    obtain ⟨s,u,hStep,_⟩ := hRun.after_event hGet (by omega)
    have hSource := (estep_source_pc hStep).symm.trans hBefore
    obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source hStep
    have hc : ins.op = .fence (.proxy (.async (some (.shared .cta))) none none) := by
      rw [hSource] at hCode
      cases repeated
      · change kernel.code[3581]? = some ins at hCode
        rw [Flow.code_3581] at hCode
        exact (congrArg Instr.op (Option.some.inj hCode)).symm
      · change kernel.code[5269]? = some ins at hCode
        rw [Flow.code_5269] at hCode
        exact (congrArg Instr.op (Option.some.inj hCode)).symm
    rw [hc] at hFire
    change prior = ⟨s.pc,.fenceProxy (.async (some (.shared .cta))) none⟩ ∧ _ at hFire
    exact ⟨k,hK,⟨s.pc,hFire.1 ▸ hGet⟩⟩
  exact hSite.elim (decideSite false) (decideSite true)

private theorem biasOrdinalRendezvous (stage : Fin 2) {g stop n : Nat}
    (hBar : BarrierArrival X (g,stop) (11+stage.val) (some 128) .sync)
    (hOrd : n ≤ observedBarrierOrdinal X (g,stop) (11+stage.val)) :
    ∃ j, j ≤ stop ∧ BarrierArrival X (g,j) (11+stage.val) (some 128) .sync ∧
      observedBarrierOrdinal X (g,j) (11+stage.val) = n := by
  let id := 11+stage.val
  obtain ⟨e,he,hKind⟩ := hBar
  change (X.tr g)[stop]? = some e at he
  let past := (X.tr g).take (stop+1)
  have hMore : n+1 ≤ past.countP (Execution.isBarId id) := by
    dsimp only [past]
    rw [List.take_add_one,he,Option.toList_some,List.countP_append]
    change n ≤ ((X.tr g).take stop).countP (Execution.isBarId id) at hOrd
    simpa [Execution.isBarId,hKind,id] using Nat.add_le_add_right hOrd 1
  obtain ⟨j,prior,hGet,hMarker,hAt⟩ :=
    MbarRing.Slot.exists_nth_countP (Execution.isBarId id) hMore
  have hLen := (List.getElem?_eq_some_iff.mp hGet).1
  change j < ((X.tr g).take (stop+1)).length at hLen
  rw [List.length_take] at hLen
  have hLe : j ≤ stop := by omega
  have hGet' : X.get (g,j) = some prior := by
    rw [List.getElem?_take_of_lt (show j < stop+1 by omega)] at hGet
    exact hGet
  rw [List.take_take,Nat.min_eq_left (show j ≤ stop+1 by omega)] at hAt
  exact ⟨j,hLe,(markerIsBiasBarrier hp hX stage hGet' hMarker).1,hAt⟩

/-- A recorded Bias-empty return implies that the returning lane passed the
initial stage rendezvous, including when this return credits a later generation. -/
theorem biasReturnInitialRendezvous (stage : Fin 2) {cta : Nat} {issue : EvId}
    (hIssue : X.Arrive issue (biasEmptyObject l cta stage) 0 1 true .cta) :
    ∃ j, j < issue.2 ∧ BarrierArrival X (issue.1,j) (11+stage.val) (some 128) .sync ∧
      observedBarrierOrdinal X (issue.1,j) (11+stage.val) = 0 := by
  obtain ⟨stop,hStop,hBar,_⟩ := biasReturnRendezvousBudget hp hX stage hIssue
  obtain ⟨j,hJ,hArrival,hOrd⟩ := biasOrdinalRendezvous hp hX stage hBar (Nat.zero_le _)
  exact ⟨j,by omega,hArrival,hOrd⟩

/-- A Bias read precedes the actual proxy fence joined by its stage rendezvous before the
selected reuse credit. The prefix need only contain that credit and the read itself. -/
theorem biasReadReturnRendezvous (stage : Fin 2) {i : EvId} {repeated : Bool} {v : Fin 16} {a : Acc}
    {bytes : List (Option Byte)} (hRead : BiasVectorRead X i repeated v a bytes)
    (hWarp : warpIndex l i.1 < 8) (hStage : warpIndex l i.1/4 = stage.val) {issue : EvId}
    (hIssue : X.Arrive issue (biasEmptyObject l (i.1/l.block) stage) 0 1 true .cta)
    (hCta : i.1/l.block = issue.1/l.block)
    (hLower : observedBarrierOrdinal X i (11+stage.val) ≤
      arrivals (biasEmptyObject l (i.1/l.block) stage) ((X.tr issue.1).take issue.2)) :
    ∃ fence x y : Nat, X.IsProxyFence (i.1,fence) (.async (some (.shared .cta))) none ∧
      i.1 < l.threads ∧ baseCausality l X i (i.1,fence) ∧
      baseCausality l X (i.1,fence) issue ∧
      TraceBefore X i (i.1,x) ∧ Witness l X (.thread (i.1,x)) (issue.1,y) ∧
      Resumes kernel X (issue.1,y) issue := by
  obtain ⟨g,read⟩ := i
  obtain ⟨peer,ret⟩ := issue
  let id := 11+stage.val
  let n := observedBarrierOrdinal X (g,read) id
  obtain ⟨stop,hStop,hBar,hBudget⟩ := biasReturnRendezvousBudget hp hX stage hIssue
  have hEnough : n ≤ observedBarrierOrdinal X (peer,stop) id := hLower.trans hBudget
  obtain ⟨y,hY,hPeer,hPeerOrd⟩ := biasOrdinalRendezvous hp hX stage hBar hEnough
  have hRetLen : ret < (X.tr peer).length := by
    obtain ⟨_,he⟩ := hIssue
    exact len_of_get he
  have hPass : y+1 < (X.tr peer).length := by
    change stop+1 = ret at hStop
    omega
  let hSrc := biasBarrierSources hp hX stage
  let hShape := biasBarrierShape hp stage
  have hMember : warpIndex l g ∈ biasParticipants stage :=
    (biasParticipantIff stage (warpIndex l g)).mpr ⟨hWarp,hStage⟩
  obtain ⟨x,mode,hOwn,hOwnOrd⟩ :=
    memberBarrierArrival hX hSrc hShape hPeer hPass hCta hMember (by
      intro hExit
      obtain ⟨j,hArrival,hAt⟩ := biasReadRendezvousOfExit hp hX stage hRead hStage hExit
      exact ⟨j,.sync,hArrival,hAt.trans hPeerOrd.symm⟩)
  obtain ⟨fence,hFenceIx,hFence⟩ := biasFenceOfRendezvous hp hX stage hOwn
  have hXAfter : read < x := by
    by_contra! hEarlier
    obtain ⟨e,hGet,hKind⟩ := hOwn
    have hDifferent : x ≠ read := by
      intro hEq
      rw [hEq] at hGet
      have hE := congrArg Event.kind (Option.some.inj (hGet.symm.trans hRead))
      rw [hKind] at hE
      cases hE
    have hNext : x+1 ≤ read := by omega
    let tr := X.tr g
    have hGet' : tr[x]? = some e := hGet
    have hAdd : (tr.take (x+1)).countP (Execution.isBarId id) =
        observedBarrierOrdinal X (g,x) id + 1 := by
      rw [List.take_add_one,hGet',Option.toList_some,List.countP_append]
      simp [observedBarrierOrdinal,tr,Execution.isBarId,id,hKind]
    have hLe : (tr.take (x+1)).countP (Execution.isBarId id) ≤ n :=
      (List.take_sublist_take_left (l := tr) hNext).countP_le
    rw [hAdd,hOwnOrd,hPeerOrd] at hLe
    omega
  obtain ⟨site,hFenceGet⟩ := hFence
  have hReadBefore : read < fence := by
    have hNe : read ≠ fence := by
      intro hEq
      rw [← hEq] at hFenceGet
      cases congrArg Event.kind (Option.some.inj (hRead.symm.trans hFenceGet))
    omega
  have hPo := po_of_not_access (X := X) (e := (g,read)) (f := (g,fence))
    rfl hReadBefore (len_of_get hFenceGet) (by rw [hFenceGet]; rfl)
  obtain ⟨key,hKey,hReleased⟩ := barrierSyncReturned hX hPeer hPass
  have hReleaseRecord := hReleased
  have hKeyEq : key = id + 16*n := by
    obtain ⟨⟨pc,kind⟩,he,hKind⟩ := hPeer
    change kind = _ at hKind
    subst kind
    have h := hSrc.arrival_key hX hShape he (CtaBarK.arrival hKey)
    change key = id + 16 * observedBarrierOrdinal X (peer,y) id at h
    rwa [hPeerOrd] at h
  have hIdLt : id < 16 := hShape.id_lt
  have hRelease : CtaBarrier.Released l.block (X.barriers (g/l.block)) id n := by
    unfold CtaBarDone at hReleased
    rw [hKeyEq, show (id+16*n)%16 = id by omega,
      show (id+16*n)/16 = n by omega, ← hCta] at hReleased
    exact hReleased
  have hOwnKey := barrierArrivalKeyOfReleased hX hSrc hShape hOwn
    (hOwnOrd.symm ▸ hPeerOrd.symm ▸ hRelease)
  rw [hOwnOrd,hPeerOrd,← hKeyEq] at hOwnKey
  have hg := event_thread_lt hX hFenceGet
  have hh := hKey.1
  have hSync : CtaBarSync l X (g,fence) (peer,ret) :=
    ⟨⟨hg,hh,hCta⟩,key,x,y,hOwnKey,hKey,by omega,
      by change stop+1 = ret at hStop; omega,hRetLen⟩
  obtain ⟨releaseIndex,hRecord⟩ := hReleaseRecord
  have hWitness := Witness.of_ctaBarCounted hKey hRecord hOwnKey hCta
  have hOwnLen : x < (X.tr g).length := by
    obtain ⟨_,he,_⟩ := hOwn
    exact len_of_get he
  obtain ⟨⟨peerSite,kind⟩,hPeerGet,hKind⟩ := hPeer
  change kind = _ at hKind
  subst kind
  have hPeerBefore : TraceBefore X (peer,y) (peer,ret) :=
    ⟨rfl,by change stop+1 = ret at hStop; omega,hRetLen⟩
  have hResume := Resumes.of_blocking (K := kernel) hPeerGet rfl hPeerBefore
  exact ⟨fence,x,y,⟨site,hFenceGet⟩,hg,.single (.inl hPo),.single (.inr (.inl hSync)),
    ⟨rfl,hXAfter,hOwnLen⟩,hWitness,hResume⟩

/-- The actual proxy fence and stage rendezvous protect a Bias read from reuse. -/
theorem biasReadFenceBeforeReturn (stage : Fin 2) {i : EvId} {repeated : Bool} {v : Fin 16}
    {a : Acc} {bytes : List (Option Byte)} (hRead : BiasVectorRead X i repeated v a bytes)
    (hWarp : warpIndex l i.1 < 8) (hStage : warpIndex l i.1/4 = stage.val) {issue : EvId}
    (hIssue : X.Arrive issue (biasEmptyObject l (i.1/l.block) stage) 0 1 true .cta)
    (hCta : i.1/l.block = issue.1/l.block)
    (hLower : observedBarrierOrdinal X i (11+stage.val) ≤
      arrivals (biasEmptyObject l (i.1/l.block) stage) ((X.tr issue.1).take issue.2)) :
    ∃ fence : Nat, X.IsProxyFence (i.1,fence) (.async (some (.shared .cta))) none ∧
      i.1 < l.threads ∧ baseCausality l X i (i.1,fence) ∧
      baseCausality l X (i.1,fence) issue := by
  obtain ⟨fence,_,_,hFence,hThread,hBefore,hAfter,_,_,_⟩ :=
    biasReadReturnRendezvous hp hX stage hRead hWarp hStage hIssue hCta hLower
  exact ⟨fence,hFence,hThread,hBefore,hAfter⟩
end

/-- A successful Bias acquire resumes every later instruction in its lane. -/
theorem biasAcquireResumes {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {notice : Ref} {wait endEvent : EvId} {target : Loc} {acq : Bool} {scope : MbarScope}
    (hWait : WaitObserves X notice wait target acq scope)
    (hBefore : TraceBefore X wait endEvent) : Resumes kernel X wait endEvent := by
  obtain ⟨site,q,he⟩ := hWait.1
  obtain ⟨exit,hSpin⟩ := actualCanonicalPoll hX he
  refine ⟨hBefore,?_⟩
  simp only [he,Option.map_some,Kind.resume]
  exact ⟨site,exit,target,q,acq,scope,he,hSpin,hBefore⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
