-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCursorStart
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorParity
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyGate
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingKeyPrefix
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingValuePrefix
public import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry
import all Kernels.TmlFa4Fwd.Proof.LoaderReadyOrder
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketGuardWindow
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Kernel.ExitChain

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.EventFrame PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Loader
  (reuseEntry reuseArrival loaderSliceEvents RingShape ringShapeOfAt
    copyCommitCode recurringPacketSite loaderOutCore packetArrivalStepFrame walkVisitIssuePc
    recurringEmptyWait recurringEmptyWaitCode recurringBarrierInput recurringBarrierFacts
    recurringBarrierPrep emptySlot emptySlot_address kvUseStage kvUseStage_val kvEmptyPhase
    loaderEventAfterLocal pollBeforeSliceEvent loaderWaitTemplate loaderAfterWait runOfLoaderLocals)

noncomputable section

/-- Count exactly the recurring ready publications in the actual loader trace. -/
def recurringPublicationMark (e : Event) : Bool :=
  match e.kind with
  | .asyncArrive _ true =>
    [reuseArrival 0, reuseArrival 1, reuseArrival 2, reuseArrival 3].contains e.pc
  | _ => false

/-- The executable publication marker recognizes exactly the recurring arrivals. -/
theorem recurringPublicationMark_iff (e : Event) :
    recurringPublicationMark e = true ↔ recurringPublicationEvent e := by
  constructor
  · obtain ⟨pc, kind⟩ := e
    cases kind <;> simp only [recurringPublicationMark, Bool.false_eq_true, false_implies]
    case asyncArrive loc noinc =>
      cases noinc
      · intro h
        cases h
      · intro h
        have hm : pc ∈ [reuseArrival 0, reuseArrival 1, reuseArrival 2, reuseArrival 3] :=
          List.contains_iff_mem.mp h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl
        exacts [⟨0, loc, rfl⟩, ⟨1, loc, rfl⟩, ⟨2, loc, rfl⟩, ⟨3, loc, rfl⟩]
  · rintro ⟨site, loc, rfl⟩
    fin_cases site <;> rfl

section
variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g use : Nat} (site : Fin 4)
    {s : TState} {es : List Event} {vs : List Visit} {last : Event}
    (hPlane : site.val % 2 = use % 2) (hs : At s (reuseEntry site) (emptyCursorFrame l site use))
    (hw : Walk kernel Assumptions.all l g s es vs) (hScope : ∀ v ∈ vs, v.pc < 1744)
include hp site hPlane hs hw hScope

/-- The end of a walk at a recurring wait or vector reaches its own packet entry.
The cursor advances once for each earlier recorded publication. -/
private theorem pendingPacketCursor (hLast : es.getLast? = some last)
    (hWork : recurringPacketWork last) :
    ∃ (current : Fin 4) (t : TState) (pre tail : List Event) (post : List Visit),
      let ordinal := use + pre.countP recurringPublicationMark
      es = pre ++ tail ∧ At t (reuseEntry current) (emptyCursorFrame l current ordinal) ∧
      current.val % 2 = ordinal % 2 ∧
      Walk kernel Assumptions.all l g t tail post ∧ tail.getLast? = some last ∧
      (∀ event ∈ tail, ¬ recurringPublicationEvent event) ∧
      RecurringCursorTrace l g use pre := by
  generalize hLength : vs.length = fuel
  induction fuel using Nat.strong_induction_on generalizing use site s es vs with
  | h fuel ih =>
    by_cases hEarlier : ∃ event ∈ es, recurringPublicationEvent event
    · obtain ⟨n, mid, after, u, post, hEs, hShort, hPost, hQuiet, hu, hWalk⟩ :=
        completeEmptyPacket hp site hs hw hEarlier
      change es = List.replicate n (cursorPoll l g use site false) ++
        cursorPoll l g use site true :: mid ++ cursorArrival l g use site :: after at hEs
      have hAfter : after ≠ [] := by
        rintro rfl
        have hAt := hLast
        rw [hEs, List.getLast?_append] at hAt
        simp only [List.getLast?_cons, List.getLast?_append,
          Option.some_or] at hAt
        have hEq := Option.some.inj hAt
        rw [← hEq] at hWork
        rcases hWork with ⟨_,_,_,_,hk⟩ | ⟨_,_,_,_,_,_,hk⟩ <;>
          exact Kind.noConfusion (congrArg Event.kind hk)
      have hAfterLast : after.getLast? = some last := by
        cases hEnd : after.getLast? with
        | none => exact (hAfter (List.getLast?_eq_none_iff.mp hEnd)).elim
        | some event =>
          rw [hEs] at hLast
          simpa [List.getLast?_append, List.getLast?_cons, hEnd] using hLast
      obtain ⟨next, t, gap, tail, following, hThen, hSuffix, hAt, hNext, hGap, hTail⟩ :=
        nextEmptyPacketAtBoundary site hu hWalk (fun v hv => hScope v (hPost.sublist.subset hv))
          ⟨last, List.mem_of_getLast? hAfterLast, .inr hWork⟩
      have hTailLast : tail.getLast? = some last := by
        have hMember : last ∈ tail := by
          have hIn := List.mem_of_getLast? hAfterLast
          rw [hThen] at hIn
          exact (List.mem_append.mp hIn).resolve_left (fun hm => (hGap last hm).2.2 hWork)
        have hNonempty := List.ne_nil_of_mem hMember
        rw [hThen, List.getLast?_append] at hAfterLast
        cases hEnd : tail.getLast? with
        | none => exact (hNonempty (List.getLast?_eq_none_iff.mp hEnd)).elim
        | some event => simpa [hEnd] using hAfterLast
      obtain ⟨current, v, prior, remaining, visits, hSplit, hv, hCurrent, hRemaining, hFinal,
        hNo, hPrior⟩ := ih following.length (by have := hSuffix.length_le; omega)
          (use := use + 1) next (by omega) hAt hTail
          (fun v hv => hScope v ((hSuffix.trans hPost).sublist.subset hv))
          hTailLast rfl
      let closed := List.replicate n (cursorPoll l g use site false) ++
        cursorPoll l g use site true :: mid ++ [cursorArrival l g use site] ++ gap
      have hMid : mid.countP recurringPublicationMark = 0 :=
        List.countP_eq_zero.mpr (fun e he hm => (hQuiet e he).1
          ((recurringPublicationMark_iff e).mp hm))
      have hGapCount : gap.countP recurringPublicationMark = 0 :=
        List.countP_eq_zero.mpr (fun e he hm => (hGap e he).1
          ((recurringPublicationMark_iff e).mp hm))
      have hMark : recurringPublicationMark (cursorArrival l g use site) = true :=
        (recurringPublicationMark_iff _).mpr ⟨site, _, rfl⟩
      have hClosed : closed.countP recurringPublicationMark = 1 := by
        have hFalse : recurringPublicationMark (cursorPoll l g use site false) = false := rfl
        have hTrue : recurringPublicationMark (cursorPoll l g use site true) = false := rfl
        simp [closed, List.countP_append, List.countP_replicate, hFalse, hTrue,
          hMid, hGapCount, hMark]
      refine ⟨current, v, closed ++ prior, remaining, visits, ?_, ?_, ?_,
        hRemaining, hFinal, hNo, ?_⟩
      · rw [hEs, hThen, hSplit]
        simp [closed, List.append_assoc]
      · simpa [List.countP_append, hClosed, Nat.add_assoc] using hv
      · simpa [List.countP_append, hClosed, Nat.add_assoc] using hCurrent
      · have hRoute := RecurringCursorTrace.gap
          (fun ev hm => ⟨(hGap ev hm).1, (hGap ev hm).2.1⟩) hPrior
        simpa [closed, List.append_assoc] using RecurringCursorTrace.packet hPlane hQuiet hRoute
    · have hNo : ∀ e ∈ es, ¬ recurringPublicationEvent e :=
        fun e he hPub => hEarlier ⟨e, he, hPub⟩
      exact ⟨site, s, [], es, vs, rfl, hs, hPlane, hw, hLast, hNo, .nil _⟩

end

/-- The loader's logical use counts every earlier recurring publication on
that lane after its two priming uses. -/
def recurringUseBefore (X : Execution) (copy : EvId) : Nat :=
  2 + ((X.tr copy.1).take copy.2).countP recurringPublicationMark

private theorem publicationCountBefore {X : Execution} {g start index : Nat}
    {published tail : List Event} (hStart : start ≤ index)
    (hBefore : ∀ event ∈ (X.tr g).take start, event.pc < 909)
    (hSplit : ((X.tr g).drop start).take (index - start + 1) = published ++ tail)
    (hQuiet : ∀ event ∈ tail, ¬ recurringPublicationEvent event) (hTail : tail ≠ []) :
    ((X.tr g).take index).countP recurringPublicationMark =
      published.countP recurringPublicationMark := by
  have hSeed : ((X.tr g).take start).countP recurringPublicationMark = 0 :=
    List.countP_eq_zero.mpr fun e he hYes => by
      obtain ⟨site, loc, rfl⟩ := (recurringPublicationMark_iff e).mp hYes
      have hLow : 909 ≤ reuseArrival site := by fin_cases site <;> decide
      have hHigh : reuseArrival site < 909 := hBefore _ he
      omega
  have hLength := congrArg List.length hSplit
  have hPos := List.length_pos_iff.mpr hTail
  simp only [List.length_take, List.length_append] at hLength
  have hPublished : published.length ≤ index - start := by omega
  have hIndex : index = start + (index - start) := (Nat.add_sub_of_le hStart).symm
  nth_rw 1 [hIndex]
  rw [List.take_add, List.countP_append, hSeed, Nat.zero_add]
  have hTake :
      ((X.tr g).drop start).take (index - start) =
        (published ++ tail).take (index - start) := by
    rw [← hSplit, List.take_take, Nat.min_eq_left (Nat.le_succ _)]
  rw [hTake, List.take_append, List.take_of_length_le hPublished, List.countP_append]
  have hNo : (tail.take (index - start - published.length)).countP recurringPublicationMark = 0 :=
    List.countP_eq_zero.mpr fun e he hYes =>
      hQuiet e (List.mem_of_mem_take he) ((recurringPublicationMark_iff e).mp hYes)
  rw [hNo, Nat.add_zero]

/-- An actual recurring issue, including an open packet, has the appropriate
ring cursor before its copy. Its logical use counts the earlier publications. -/
private theorem actualPacketCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hWork : recurringPacketWork e) :
    ∃ (start : Nat) (current : Fin 4) (t : TState) (pre tail : List Event) (post : List Visit),
      let use := 2 + pre.countP recurringPublicationMark
      start ≤ index ∧ (((X.tr g).drop start).take (index - start + 1)) = pre ++ tail ∧
      At t (reuseEntry current) (emptyCursorFrame l current use) ∧
      current.val % 2 = use % 2 ∧ Walk kernel Assumptions.all l g t tail post ∧
      tail.getLast? = some e ∧ (∀ event ∈ tail, ¬ recurringPublicationEvent event) ∧
      RecurringCursorTrace l g 2 pre ∧ use = recurringUseBefore X (g, index) := by
  have hContinues := recurringPacketWorkContinues hWork
  have hBand : 909 ≤ e.pc ∧ e.pc < 1744 := by
    rcases hWork with ⟨site, pair, upper, _, rfl⟩ | ⟨site, _, _, _, _, _, rfl⟩
    · change 909 ≤ Loader.packetPlanePc (Loader.recurringPacketSite site) pair upper ∧
        Loader.packetPlanePc (Loader.recurringPacketSite site) pair upper < 1744
      fin_cases site <;> fin_cases pair <;> cases upper <;> decide
    · have hTable : ∀ s : Fin 4, 909 ≤ (recurringEmptyWait s).pc ∧
          (recurringEmptyWait s).pc < 1744 := by decide
      exact hTable site
  obtain ⟨start, s, visits, hStart, hBefore, hs, hWalk, hScope⟩ :=
    actualCursorSeedPrefix hp hX he hContinues hBand
  let events := ((X.tr g).drop start).take (index - start + 1)
  have hAt : ((X.tr g).drop start)[index - start]? = some e := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le hStart]
  have hLast : events.getLast? = some e := by
    dsimp only [events]
    rw [List.take_add_one, hAt]
    simp
  obtain ⟨site, u, gap, suffix, trail, hGap, hTrail, hu, hPlane, hQuiet, hSuffix⟩ :=
    firstEmptyPacketAtBoundary hs hWalk hScope ⟨e, List.mem_of_getLast? hLast, .inr hWork⟩
  change events = gap ++ suffix at hGap
  have hTailLast : suffix.getLast? = some e := by
    have hMember : e ∈ suffix := by
      have hIn := List.mem_of_getLast? hLast
      rw [hGap] at hIn
      exact (List.mem_append.mp hIn).resolve_left (fun hm => (hQuiet e hm).2.2 hWork)
    have hNonempty := List.ne_nil_of_mem hMember
    rw [hGap, List.getLast?_append] at hLast
    cases hEnd : suffix.getLast? with
    | none => exact (hNonempty (List.getLast?_eq_none_iff.mp hEnd)).elim
    | some last => simpa [hEnd] using hLast
  obtain ⟨current, t, pre, tail, post, hSplit, ht, hCurrent, hTail, hEnd, hNone, hPrior⟩ :=
    pendingPacketCursor hp site hPlane hu hSuffix
      (fun v hv => hScope v (hTrail.sublist.subset hv)) hTailLast hWork
  have hGapCount : gap.countP recurringPublicationMark = 0 :=
    List.countP_eq_zero.mpr (fun ev hm h => (hQuiet ev hm).1
      ((recurringPublicationMark_iff ev).mp h))
  have hEvents : events = (gap ++ pre) ++ tail := by
    rw [hGap, hSplit, List.append_assoc]
  refine ⟨start, current, t, gap ++ pre, tail, post, hStart, hEvents, ?_, ?_,
    hTail, hEnd, hNone, ?_, ?_⟩
  · simpa [List.countP_append, hGapCount] using ht
  · simpa [List.countP_append, hGapCount] using hCurrent
  · exact .gap (fun ev hm => ⟨(hQuiet ev hm).1, (hQuiet ev hm).2.1⟩) hPrior
  · have hRank := publicationCountBefore hStart hBefore hEvents hNone
      (List.ne_nil_of_mem (List.mem_of_getLast? hEnd))
    simp [recurringUseBefore, hRank]

theorem actualVectorCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hCopy : recurringVectorEvent e) :
    ∃ (start : Nat) (current : Fin 4) (t : TState) (pre tail : List Event) (post : List Visit),
      let use := 2 + pre.countP recurringPublicationMark
      start ≤ index ∧ (((X.tr g).drop start).take (index - start + 1)) = pre ++ tail ∧
      At t (reuseEntry current) (emptyCursorFrame l current use) ∧
      current.val % 2 = use % 2 ∧ Walk kernel Assumptions.all l g t tail post ∧
      tail.getLast? = some e ∧ (∀ event ∈ tail, ¬ recurringPublicationEvent event) ∧
      RecurringCursorTrace l g 2 pre ∧ use = recurringUseBefore X (g, index) := by
  exact actualPacketCursor hp hX he (.inl hCopy)

section
variable {l : Launch}

private theorem memberOfPacketSlice {g : Nat} (site : Fin 4) {s : TState} {es : List Event}
    {inside later : List Visit} {e : Event} (hw : Walk kernel Assumptions.all l g s es inside)
    (hInside : ∀ v ∈ inside, (CursorRoute.packet site).inside v.pc = true) (hMem : e ∈ es) :
    e ∈ loaderSliceEvents (reuseEntry site) (reuseArrival site) (inside ++ later) := by
  unfold loaderSliceEvents
  rw [List.takeWhile_append_of_pos]
  · rw [List.filterMap_append, ← hw.events]
    exact List.mem_append_left _ hMem
  · intro v hv
    have h := hInside v hv
    simpa only [CursorRoute.inside, decide_eq_true_eq, Bool.and_eq_true] using h

private theorem pendingEventInPacket {g use : Nat} (site : Fin 4) {s : TState} {es : List Event}
    {vs : List Visit} {e : Event} (hs : At s (reuseEntry site) (emptyCursorFrame l site use))
    (hw : Walk kernel Assumptions.all l g s es vs) (hLast : es.getLast? = some e)
    (hContinue : ¬ Ends e) (hNo : ∀ event ∈ es, ¬ recurringPublicationEvent event) :
    e ∈ loaderSliceEvents (reuseEntry site) (reuseArrival site) vs := by
  let r := CursorRoute.packet site
  have hStart : r.inside s.pc = true := by
    rw [hs.1]
    fin_cases site <;> decide
  have hMem := List.mem_of_getLast? hLast
  rcases r.cutWalk hw hStart (ringShapeOfAt hs) with hAll |
    ⟨t, pre, rest, front, post, hEs, hVs, hFront, ht, hShape, hF, hPre, hTail⟩
  · simpa only [List.append_nil] using
      memberOfPacketSlice site (later := []) hw hAll hMem
  have ht' : t.pc = reuseArrival site := by simpa [r, CursorRoute.stops] using ht
  have hBounds : 174 ≤ reuseArrival site ∧ reuseArrival site < 1901 := by
    fin_cases site <;> decide
  cases hTail with
  | stop =>
    rw [hEs, List.append_nil] at hMem
    rw [hVs]
    exact memberOfPacketSlice site hPre hFront hMem
  | @tau _ u _ _ hTau _ =>
    have hCode := (copyCommitCode (recurringPacketSite site)).2
    change kernel.code[reuseArrival site]? = _ at hCode
    rw [← ht'] at hCode
    have hCore : Tau kernel [] l g t u := by
      unfold Tau at *
      rwa [← loaderOutCore (by omega) (by omega)]
    exact (tau_core_not_event hCode rfl hCore).elim
  | last hStep =>
    rw [hEs, List.getLast?_append] at hLast
    simp only [List.getLast?_singleton, Option.some_or] at hLast
    obtain rfl := Option.some.inj hLast
    obtain ⟨_, _, hFire⟩ := hStep
    exact (hContinue (fires_none_ends hFire)).elim
  | @ev _ u event suffix post hStep hWalk =>
    obtain ⟨target, hKind, _⟩ := packetArrivalStepFrame (recurringPacketSite site) ht' hStep
    have hEvent : event = ⟨reuseArrival site, .asyncArrive target true⟩ := by
      cases event
      rw [Event.mk.injEq]
      exact ⟨(estep_source_pc hStep).trans ht', hKind⟩
    have hOccurred : event ∈ es := by rw [hEs]; simp
    exact (hNo event hOccurred ⟨site, target, hEvent⟩).elim

/-- A still-open packet's last vector comes from that very packet's cursor,
rather than a later visit to the same decoded station. -/
theorem pendingVectorInPacket {g use : Nat} (site : Fin 4) {s : TState} {es : List Event}
    {vs : List Visit} {e : Event} (hs : At s (reuseEntry site) (emptyCursorFrame l site use))
    (hw : Walk kernel Assumptions.all l g s es vs) (hLast : es.getLast? = some e)
    (hCopy : recurringVectorEvent e) (hNo : ∀ event ∈ es, ¬ recurringPublicationEvent event) :
    e ∈ loaderSliceEvents (reuseEntry site) (reuseArrival site) vs := by
  exact pendingEventInPacket site hs hw hLast (recurringPacketWorkContinues (.inl hCopy)) hNo

private theorem vectorAfterPacketWait {g : Nat} (site : Fin 4) {t : TState} {es : List Event}
    {vs : List Visit} {e : Event} (hw : Walk kernel Assumptions.all l g t es vs)
    (hSeen : e ∈ loaderSliceEvents (reuseEntry site) (reuseArrival site) vs)
    (hCopy : recurringVectorEvent e) :
    (recurringEmptyWait site).pc < e.pc := by
  obtain ⟨v, hv, he⟩ := List.mem_filterMap.mp hSeen
  have hPc := walkVisitIssuePc hw (List.takeWhile_subset _ hv) he
  have hBand : reuseEntry site ≤ e.pc ∧ e.pc < reuseArrival site := by
    have h := List.all_eq_true.mp List.all_takeWhile _ hv
    rw [hPc]
    exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).2⟩
  have window (current actual : Fin 4) (pair : Fin 16) (upper : Bool) :
      let pc := Loader.packetPlanePc (recurringPacketSite actual) pair upper
      reuseEntry current ≤ pc ∧ pc < reuseArrival current → (recurringEmptyWait current).pc < pc
      := by
    fin_cases current <;> fin_cases actual <;> fin_cases pair <;> cases upper <;> decide
  obtain ⟨actual, pair, upper, _, rfl⟩ := hCopy
  exact window site actual pair upper hBand

private theorem packetSliceAfterWait {g : Nat} (site : Fin 4) {s : TState} {es : List Event}
    {vs : List Visit} {e : Event} (hs : s.pc = (recurringEmptyWait site).pc + 3)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (he : e ∈ loaderSliceEvents (reuseEntry site) (reuseArrival site) vs) :
    (recurringEmptyWait site).pc + 3 ≤ e.pc := by
  let floor := (recurringEmptyWait site).pc + 3
  let stop := reuseArrival site
  let clipped := vs.takeWhile (fun v => reuseEntry site ≤ v.pc && v.pc < stop)
  have hPrefix : clipped <+: vs := List.takeWhile_prefix _
  have hEq : vs.take clipped.length = clipped := by
    obtain ⟨rest,hRest⟩ := hPrefix
    rw [← hRest, List.take_left' rfl]
  have hWalk := takeLoaderVisits hw clipped.length
  rw [hEq] at hWalk
  have hScope : ∀ v ∈ clipped, v.pc < stop := by
    intro v hv
    exact of_decide_eq_true ((Bool.and_eq_true_iff.mp (List.all_eq_true.mp
      List.all_takeWhile v hv)).2)
  have hCode : ((kernel.code.drop floor).take (stop - floor)).all
      (fun i => Thread.staysPastEvent floor i.op) = true := by
    fin_cases site <;> decide +kernel
  exact Thread.eventTailEventsInSpan hCode
    (fun pc hpc hm seg hMatch => by
      have audit : Assumptions.swExp2Sites.all (fun n => match PTX.Assumption.cuteExp2.matchAt
            kernel n with
          | some seg => decide (1906 ≤ seg.stop)
          | none => false) = true := by decide +kernel
      have h := List.all_eq_true.mp audit pc hm
      rw [hMatch] at h
      have hSmall : floor ≤ 1906 := by fin_cases site <;> decide
      exact hSmall.trans (of_decide_eq_true h)) hWalk hScope hs.ge e he
end

private theorem recurringPollMatchesSlice {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use : Nat} (site : Fin 4) {s : TState} {es : List Event} {vs : List Visit} {e : Event}
    (hs : At s (reuseEntry site) (emptyCursorFrame l site use))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSeen : e ∈ loaderSliceEvents (reuseEntry site) (reuseArrival site) vs)
    (hSite : e.pc = (recurringEmptyWait site).pc) :
    ∃ ok, e = cursorPoll l g use site ok := by
  let gate := recurringEmptyWait site
  let stage := kvUseStage use
  let phase := if kvEmptyPhase use then 1 else 0
  let facts := recurringBarrierFacts l site stage phase
  have input : At s (reuseEntry site) (recurringBarrierInput l site stage phase) :=
    hs.mono ⟨hs.2.2.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.2.1, trivial⟩
  obtain ⟨t, hLocal, ht⟩ := recurringBarrierPrep hp (g := g) site stage phase s input
  obtain ⟨visits, hWalk, hSuffix, hObserved⟩ := loaderEventAfterLocal hLocal hw hSeen
  have hRange : 174 ≤ gate.pc ∧ gate.pc + 3 < 1906 := by fin_cases site <;> decide
  have hAddr : l.sharedBase + 8 * stage.val + 56 < 2 ^ 32 := by
    have := hp.shared.2.1
    have := stage.isLt
    omega
  have hAlign : (l.sharedBase + 8 * stage.val + 56) % 8 = 0 := by
    have := hp.shared.1
    omega
  have hPhase : phase < 2 := by dsimp [phase]; split <;> decide
  have hFresh : ∀ pair ∈ facts, pair.1 ≠ gate.result := by
    fin_cases site <;> simp [facts, gate, recurringBarrierFacts, recurringEmptyWait,
      recurringPacketSite, Loader.copyArrivalAddress]
  have hBounds : reuseEntry site ≤ (recurringEmptyWait site).pc ∧
      (recurringEmptyWait site).pc < reuseArrival site := by
    fin_cases site <;> decide
  clear hw hSeen hLocal hs input hSuffix vs
  induction es generalizing t visits with
  | nil =>
    have h := Loader.sliceEventMem hWalk hObserved
    cases h
  | cons first rest ih =>
    have hOut := loaderWaitTemplate (l := l) (g := g) gate (recurringEmptyWaitCode site)
      hRange hAddr hAlign hPhase ht.1 ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2.1
    cases hWalk with
    | tau hTau _ =>
      rw [Tau, hOut] at hTau
      cases hTau
    | last he =>
      obtain ⟨tmpl, hTmpl, hFire⟩ := he
      rw [hOut] at hTmpl
      obtain rfl := Out.ev.inj hTmpl
      obtain ⟨_, _, hNone⟩ := hFire
      cases hNone
    | @ev _ _ head _ trail he hw =>
      obtain ⟨tmpl, hTmpl, hFire⟩ := he
      rw [hOut] at hTmpl
      obtain rfl := Out.ev.inj hTmpl
      obtain ⟨ok, rfl, hNext⟩ := hFire
      obtain rfl := Option.some.inj hNext
      have hMore : e = ⟨gate.pc, .wait ⟨.shared, g / l.block, l.sharedBase+8*stage.val+56⟩
            phase ok true .cta⟩ ∨
          e ∈ loaderSliceEvents (reuseEntry site) (reuseArrival site) trail := by
        simpa only [loaderSliceEvents, visit, List.takeWhile_cons, hBounds.1, hBounds.2,
          ht.1, decide_true, Bool.true_and, ↓reduceIte, List.filterMap_cons, List.mem_cons]
          using hObserved
      rcases hMore with hHead | hMore
      · exact ⟨ok, by simpa only [cursorPoll, emptySlot_address] using hHead⟩
      · have hAt : At (next (setReg t gate.result (.pred ok))) (gate.pc + 1)
            ((gate.result, .pred ok) :: facts) := ht.set hFresh
        obtain ⟨u, hSteps, hu⟩ := loaderAfterWait gate (recurringEmptyWaitCode site) hRange ok hAt
        obtain ⟨_, hRun⟩ := runOfLoaderLocals hSteps
        obtain ⟨tail, hTail, _, hTarget⟩ := loaderEventAfterLocal hRun hw hMore
        cases ok
        · exact ih u hu tail hTail hTarget
        · exfalso
          have h := packetSliceAfterWait site hu.1 hTail hTarget
          exact (Nat.not_le_of_gt (Nat.lt_add_of_pos_right (by decide))) (hSite ▸ h)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Every recorded recurring loader poll uses the logical use at its actual cursor,
including a prefix consisting only of unsuccessful retries. -/
theorem recurringPollOfCursor (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e) (h : recurringPollAttempt e) :
    ∃ site ok, e = cursorPoll l g (recurringUseBefore X (g,index)) site ok := by
  obtain ⟨start, site, t, pre, tail, post, hStart, hTrace, ht, hPlane, hWalk, hLast,
    hNo, hPrev, hUse⟩ := actualPacketCursor hp hX he (.inr h)
  have hSeen := pendingEventInPacket site ht hWalk hLast
    (recurringPacketWorkContinues (.inr h)) hNo
  have hPc : e.pc = (recurringEmptyWait site).pc := by
    obtain ⟨v,hv,hEvent⟩ := List.mem_filterMap.mp hSeen
    have hPos := walkVisitIssuePc hWalk (List.takeWhile_subset _ hv) hEvent
    have hb := List.all_eq_true.mp List.all_takeWhile _ hv
    rw [← hPos] at hb
    obtain ⟨other,loc,q,ok,acq,scope,rfl⟩ := h
    have audit : ∀ current other : Fin 4,
        reuseEntry current ≤ (recurringEmptyWait other).pc →
        (recurringEmptyWait other).pc < reuseArrival current → other = current := by decide
    obtain rfl := audit site other
      (of_decide_eq_true ((Bool.and_eq_true_iff.mp hb).1))
      (of_decide_eq_true ((Bool.and_eq_true_iff.mp hb).2))
    rfl
  obtain ⟨ok,hPoll⟩ := recurringPollMatchesSlice hp site ht hWalk hSeen hPc
  exact ⟨site,ok,hUse ▸ hPoll⟩

private theorem cursorPollBeforeVector {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use : Nat} (site : Fin 4) {s : TState} {es : List Event} {vs : List Visit} {e : Event}
    (hs : At s (reuseEntry site) (emptyCursorFrame l site use))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSeen : e ∈ loaderSliceEvents (reuseEntry site) (reuseArrival site) vs)
    (hLater : (recurringEmptyWait site).pc < e.pc) :
    ∃ (retries : Nat) (tail : List Event),
      es = List.replicate retries (cursorPoll l g use site false) ++
        cursorPoll l g use site true :: tail ∧ e ∈ tail ∧
      ∃ (u : TState) (visits : List Visit), u.pc = (recurringEmptyWait site).pc + 3 ∧
        RingShape u ∧ Walk kernel Assumptions.all l g u tail visits := by
  let stage := kvUseStage use
  let phase := if kvEmptyPhase use then 1 else 0
  have hInput : At s (reuseEntry site) (recurringBarrierInput l site stage phase) :=
    hs.mono ⟨hs.2.2.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.2.1, trivial⟩
  obtain ⟨t, hLocal, ht⟩ := recurringBarrierPrep hp (g := g) site stage phase s hInput
  obtain ⟨visits, hWalk, _, hVector⟩ := loaderEventAfterLocal hLocal hw hSeen
  have hRange : 174 ≤ (recurringEmptyWait site).pc ∧ (recurringEmptyWait site).pc + 3 < 1906 :=
    by fin_cases site <;> decide
  have hAddr : l.sharedBase + 8 * stage.val + 56 < 2 ^ 32 := by
    have := hp.shared.2.1
    have := stage.isLt
    omega
  have hAlign : (l.sharedBase + 8 * stage.val + 56) % 8 = 0 := by
    have := hp.shared.1
    omega
  have hPhase : phase < 2 := by dsimp [phase]; split <;> decide
  have hFresh : ∀ pair ∈ recurringBarrierFacts l site stage phase,
      pair.1 ≠ (recurringEmptyWait site).result := by
    fin_cases site <;> simp [recurringBarrierFacts, recurringEmptyWait, recurringPacketSite,
      Loader.copyArrivalAddress]
  have hUpper : (recurringEmptyWait site).pc < reuseArrival site := by fin_cases site <;> decide
  obtain ⟨n, u, tail, post, hEvents, hu, hTail, hIssue⟩ :=
    pollBeforeSliceEvent (recurringEmptyWait site) (recurringEmptyWaitCode site)
      hRange (Nat.sub_le ..) hUpper hFresh
      (fun _ state => loaderWaitTemplate _ (recurringEmptyWaitCode site) hRange hAddr hAlign
        hPhase state.1 state.2.2.2.1 state.2.2.2.2.1 state.2.2.2.2.2.1)
      ht hWalk hLater hVector
  have hMember : e ∈ tail := by
    rw [hTail.events]
    obtain ⟨v, hv, hEvent⟩ := List.mem_filterMap.mp hIssue
    exact List.mem_filterMap.mpr ⟨v, List.takeWhile_subset _ hv, hEvent⟩
  exact ⟨n, tail, by simpa only [cursorPoll, emptySlot_address] using hEvents, hMember,
    u,post,hu.1,ringShapeOfAt hu,hTail⟩

/-- An actual recurring copy, including before its publication, is preceded by the
recorded acquire of the slot and parity at its actual logical use. -/
theorem actualVectorUseWithLatestGuard (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e) (hCopy : recurringVectorEvent e) :
    ∃ (start : Nat) (prior : List Event) (wait : EvId),
      let use := 2 + prior.countP recurringPublicationMark
      start ≤ index ∧ ((X.tr g).drop start).take prior.length = prior ∧
      EmptyAcquire l X wait (kvUseStage use) (if kvEmptyPhase use then 1 else 0) ∧
      Resumes kernel X wait (g, index) ∧ RecurringCursorTrace l g 2 prior ∧
      use = recurringUseBefore X (g, index) ∧
      ∃ site : Fin 4, ∃ retries : Nat,
        wait = (g, start + (prior.length + retries)) ∧
        ((X.tr g).drop start).take (wait.2 - start + 1) =
          prior ++ List.replicate retries (cursorPoll l g use site false) ++
            [cursorPoll l g use site true] ∧
        (∃ event, X.get wait = some event ∧ recurringEmptyEvent event) ∧
        ∀ j, wait.2 < j → j < index → ∀ event, X.get (g,j) = some event →
          ¬ recurringEmptyEvent event := by
  obtain ⟨start, site, t, pre, es, vs, hStart, hSplit, ht, _, hw, hLast, hNone, hPrior, hUse⟩ :=
    actualVectorCursor hp hX he hCopy
  let use := 2 + pre.countP recurringPublicationMark
  have hSeen := pendingVectorInPacket site ht hw hLast hCopy hNone
  obtain ⟨n, rest, hEvents, hMem, resume, post, hPc, hShape, hResume⟩ :=
    cursorPollBeforeVector hp site ht hw hSeen (vectorAfterPacketWait site hw hSeen hCopy)
  let wait := start + (pre.length + n)
  have hPoll : X.get (g, wait) = some (cursorPoll l g use site true) := by
    have hLen : (((X.tr g).drop start).take (index - start + 1)).length =
        index - start + 1 := by
      rw [List.length_take, List.length_drop, Nat.min_eq_left]
      have hIndex : index < (X.tr g).length := len_of_get he
      omega
    have hWait : pre.length + n < index - start + 1 := by
      rw [hSplit, hEvents, List.length_append, List.length_append,
        List.length_replicate, List.length_cons] at hLen
      omega
    have hAt : (((X.tr g).drop start).take (index - start + 1))[pre.length + n]? =
        some (cursorPoll l g use site true) := by
      rw [hSplit, List.getElem?_append_right (by omega), hEvents,
        show pre.length + n - pre.length = n by omega,
        List.getElem?_append_right (by simp), List.length_replicate, Nat.sub_self]
      rfl
    change (X.tr g)[start + (pre.length + n)]? = _
    rwa [List.getElem?_take_of_lt hWait, List.getElem?_drop] at hAt
  have hGuard : Resumes kernel X (g, wait) (g, index) := by
    have hWaitLt : wait < index := by
      have hLen := congrArg List.length hSplit
      rw [List.length_take, List.length_append, hEvents, List.length_append,
        List.length_replicate, List.length_cons] at hLen
      have hPos := List.length_pos_iff.mpr (List.ne_nil_of_mem hMem)
      dsimp [wait]
      omega
    obtain ⟨_, hSpin⟩ := actualCanonicalPoll hX hPoll
    exact Resumes.of_spin hPoll hSpin rfl hWaitLt (len_of_get he)
  have hPrefix : ((X.tr g).drop start).take pre.length = pre := by
    have hLe : pre.length ≤ index - start + 1 := by
      have hLen := congrArg List.length hSplit
      simp only [List.length_take, List.length_append] at hLen
      omega
    rw [← Nat.min_eq_left hLe, ← List.take_take, hSplit, List.take_left]
  have hGuardPrefix : ((X.tr g).drop start).take (wait - start + 1) =
      pre ++ List.replicate n (cursorPoll l g use site false) ++
        [cursorPoll l g use site true] := by
    have hLe : wait - start + 1 ≤ index - start + 1 := by
      have hLt := hGuard.1.2.1
      omega
    rw [← Nat.min_eq_left hLe, ← List.take_take, hSplit, hEvents]
    have hLength : wait - start + 1 = (pre ++
        List.replicate n (cursorPoll l g use site false) ++
        [cursorPoll l g use site true]).length := by simp [wait]; omega
    have hAppend : pre ++ (List.replicate n (cursorPoll l g use site false) ++
          cursorPoll l g use site true :: rest) =
        (pre ++ List.replicate n (cursorPoll l g use site false) ++
          [cursorPoll l g use site true]) ++ rest := by simp [List.append_assoc]
    change (pre ++ (List.replicate n (cursorPoll l g use site false) ++
      cursorPoll l g use site true :: rest)).take (wait - start + 1) = _
    rw [hLength, hAppend, List.take_left]
  have afterGuard {j : Nat} (hJ : wait < j) (hBefore : j ≤ index) {event : Event}
      (hGet : X.get (g,j) = some event) : rest[j-(wait+1)]? = some event := by
    have hAt : (((X.tr g).drop start).take (index-start+1))[j-start]? = some event := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        Nat.add_sub_of_le (by dsimp only [wait] at hJ; omega)]
      exact hGet
    rw [hSplit, hEvents, ← List.append_assoc,
      List.getElem?_append_right (by simp; dsimp only [wait] at hJ; omega)] at hAt
    have hOffset : j-start-(pre ++ List.replicate n (cursorPoll l g use site false)).length =
        j-(wait+1)+1 := by simp [wait]; omega
    rw [hOffset, List.getElem?_cons_succ] at hAt
    exact hAt
  have hExact := afterGuard hGuard.1.2.1 le_rfl he
  have hLen := (List.getElem?_eq_some_iff.mp hExact).1
  have hQuiet := packetGuardWindow site hPc hShape hResume hLen
    (fun _ _ event hGet _ => hNone event (hEvents.symm ▸
      List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_of_getElem? hGet))))
  refine ⟨start, pre, (g, wait), hStart, hPrefix, ⟨_, hPoll, rfl⟩, hGuard, hPrior, hUse,
    site, n, rfl, hGuardPrefix, ⟨_,hPoll,site,_,_,rfl⟩, ?_⟩
  intro j hj hBefore event hActual
  exact hQuiet (j-(wait+1)) (by change wait < j at hj; omega) event
    (afterGuard hj hBefore.le hActual)

/-- The recurring guard prefix preserves the actual successful wait and all earlier publications. -/
theorem actualVectorUseWithGuardPrefix (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e) (hCopy : recurringVectorEvent e) :
    ∃ (start : Nat) (prior : List Event) (wait : EvId),
      let use := 2 + prior.countP recurringPublicationMark
      start ≤ index ∧ ((X.tr g).drop start).take prior.length = prior ∧
      EmptyAcquire l X wait (kvUseStage use) (if kvEmptyPhase use then 1 else 0) ∧
      Resumes kernel X wait (g, index) ∧ RecurringCursorTrace l g 2 prior ∧
      use = recurringUseBefore X (g, index) ∧
      ∃ site : Fin 4, ∃ retries : Nat,
        wait = (g, start + (prior.length + retries)) ∧
        ((X.tr g).drop start).take (wait.2 - start + 1) =
          prior ++ List.replicate retries (cursorPoll l g use site false) ++
            [cursorPoll l g use site true] := by
  obtain ⟨start,prior,wait,hStart,hPrefix,hEmpty,hGuard,hPrior,hUse,site,n,hWait,hData,_⟩ :=
    actualVectorUseWithLatestGuard hp hX he hCopy
  exact ⟨start,prior,wait,hStart,hPrefix,hEmpty,hGuard,hPrior,hUse,site,n,hWait,hData⟩

/-- A real ordinary copy is priming K, priming V, or an actual recurring vector. -/
theorem copyPrimingOrRecurringVector {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {copy : EvId} {spec : AsyncCopy.Spec} (hCopy : X.Copy copy spec) :
    (∃ (pair : Fin 16) (upper : Bool), PrimingKeyVector X copy pair upper spec) ∨
    (∃ (pair : Fin 16) (upper : Bool), PrimingValueVector X copy pair upper spec) ∨
    ∃ e, X.get copy = some e ∧ recurringVectorEvent e ∧ e.kind = .copy spec := by
  obtain ⟨g, index⟩ := copy
  obtain ⟨pc, hGet⟩ := hCopy
  obtain ⟨hLo, hHi, hOrdinary⟩ := Loader.actualCopyAtInLoader hX hGet
  obtain ⟨packet, hStart, hStop⟩ := Loader.loaderCopyPcInPacket hLo hHi hOrdinary
  obtain ⟨pair, upper, rfl⟩ := Loader.packetCopyCoordinates packet hStart hStop hOrdinary
  rcases Nat.lt_or_ge packet.val 2 with hPriming | hRepeat
  · let slot : Fin 2 := ⟨packet.val, hPriming⟩
    have hPacket : packet = Loader.primingPacketSite slot := Fin.ext rfl
    rw [hPacket] at hGet
    have hSmall : ∀ q : Fin 2, q = 0 ∨ q = 1 := by decide
    rcases hSmall slot with hZero | hOne
    · have hKey : Loader.packetPlanePc (Loader.primingPacketSite 0) pair upper =
          Loader.kCopyPc pair + (if upper then 1 else 0) := by
        fin_cases pair <;> cases upper <;> decide
      rw [hZero, hKey] at hGet
      exact .inl ⟨pair, upper, hGet⟩
    · have hValue : Loader.packetPlanePc (Loader.primingPacketSite 1) pair upper =
          Loader.vCopyPc pair + (if upper then 1 else 0) := by
        fin_cases pair <;> cases upper <;> decide
      rw [hOne, hValue] at hGet
      exact .inr (.inl ⟨pair, upper, hGet⟩)
  · let site : Fin 4 := ⟨packet.val - 2, by have := packet.isLt; omega⟩
    have hPacket : packet = Loader.recurringPacketSite site := Fin.ext (by
      change packet.val = packet.val - 2 + 2
      omega)
    rw [hPacket] at hGet
    exact .inr (.inr ⟨_, hGet, ⟨site,pair,upper,spec,rfl⟩, rfl⟩)

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
