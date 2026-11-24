-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorRoute
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part020
import Kernels.TmlFa4Fwd.Flow.Code.Part025
import Kernels.TmlFa4Fwd.Flow.Code.Part027

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader
  (recurringPacketSite recurringStageInputs recurringEmptyWait recurringBarrierInput readySlot
    emptySlot reuseArrival reuseEntry packetArrivalStepFrame loaderSliceEvents
    copyCommitCode copyCommitPc loaderOutCore loaderPhaseWord kvUseStage kvEmptyPhase
    loaderPipelineStepShape pipelineAtCut ringShapeOfAt recurringReadyArrivalCut)

noncomputable section

/-- The stage, empty parity, and shared-memory base of an upcoming packet. -/
def emptyCursorFrame (l : Launch) (site : Fin 4) (use : Nat) : List (Nat × Value) :=
  (2535, b32 l.sharedBase) :: reuseCursorWords site use

/-- A recurring packet publication in the actual loader event stream. -/
def recurringPublicationEvent (e : Event) : Prop :=
  ∃ (site : Fin 4) (loc : Loc), e = ⟨reuseArrival site, .asyncArrive loc true⟩

/-- The successful poll at a recurring packet's empty gate. -/
def recurringEmptyEvent (e : Event) : Prop :=
  ∃ (site : Fin 4) (loc : Loc) (parity : Nat),
    e = ⟨(recurringEmptyWait site).pc, .wait loc parity true true .cta⟩

private theorem eventVisit {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    {e : Event} (he : e ∈ es) : ∃ v ∈ vs, v.pc = e.pc := by
  induction hw with
  | stop => cases he
  | tau _ _ ih =>
    obtain ⟨v, hv, ht⟩ := ih he
    exact ⟨v, List.mem_cons_of_mem _ hv, ht⟩
  | ev h _ ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, List.mem_cons_self, (estep_source_pc h).symm⟩
    · obtain ⟨v, hv, ht⟩ := ih he
      exact ⟨v, List.mem_cons_of_mem _ hv, ht⟩
  | last h =>
    obtain rfl := List.mem_singleton.mp he
    exact ⟨_, List.mem_cons_self, (estep_source_pc h).symm⟩

private theorem notInsidePacket (site : Fin 4) {e : Event}
    (he : recurringPublicationEvent e) : (CursorRoute.packet site).inside e.pc = false := by
  obtain ⟨i, _, rfl⟩ := he
  fin_cases site <;> fin_cases i <;> rfl

private theorem advanceCode (site : Fin 4) :
    ∃ ins, kernel.code[reuseArrival site + 1]? = some ins ∧ ins.op.isLocal = true := by
  fin_cases site
  · exact ⟨_, Flow.code_1138, rfl⟩
  · exact ⟨_, Flow.code_1343, rfl⟩
  · exact ⟨_, Flow.code_1603, rfl⟩
  · exact ⟨_, Flow.code_1736, rfl⟩

/-- Truncate an actual walk at an exact visit count. -/
theorem takeLoaderVisits {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs) (n : Nat) :
    Walk kernel Assumptions.all l g s ((vs.take n).filterMap Visit.ev) (vs.take n) := by
  induction hw generalizing n with
  | stop => cases n <;> exact .stop _
  | tau h _ ih =>
    cases n with
    | zero => exact .stop _
    | succ n => exact .tau h (ih n)
  | ev h _ ih =>
    cases n with
    | zero => exact .stop _
    | succ n => exact .ev h (ih n)
  | last h =>
    cases n with
    | zero => exact .stop _
    | succ n =>
      simp only [List.take_succ_cons, List.take_nil, List.filterMap_cons, visit_ev,
        List.filterMap_nil]
      exact .last h

private theorem packetStartsInside (site : Fin 4) :
    (CursorRoute.packet site).inside (reuseEntry site) = true := by
  fin_cases site <;> decide

/-- If its actual suffix reaches a recurring publication, the current packet closes
with a publication in its own slot and retains the cursor for the subsequent advance. -/
theorem completeEmptyPacket {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use : Nat} (site : Fin 4) {s : TState}
    {es : List Event} {vs : List Visit}
    (hs : At s (reuseEntry site) (emptyCursorFrame l site use))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSeen : ∃ e ∈ es, recurringPublicationEvent e) :
    let ready := Prologue.initObject l (g / l.block) (readySlot (kvUseStage use))
    let empty := Prologue.initObject l (g / l.block) (emptySlot (kvUseStage use))
    let parity := if kvEmptyPhase use then 1 else 0
    let poll := fun ok => (⟨(recurringEmptyWait site).pc, .wait empty parity ok true .cta⟩ : Event)
    let arrival : Event := ⟨reuseArrival site, .asyncArrive ready true⟩
    ∃ (n : Nat) (pre tail : List Event) (u : TState) (post : List Visit),
      es = List.replicate n (poll false) ++ poll true :: pre ++ arrival :: tail ∧
      post.length < vs.length ∧ post <:+ vs ∧
      (∀ e ∈ pre, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e) ∧
      At u (reuseArrival site + 1) (emptyCursorFrame l site use) ∧
      Walk kernel Assumptions.all l g u tail post := by
  dsimp only
  obtain ⟨seen, hSeen, hPub⟩ := hSeen
  let r := CursorRoute.packet site
  have hIn : r.inside s.pc = true := hs.1.symm ▸ packetStartsInside site
  rcases r.cutWalk hw hIn (ringShapeOfAt hs) with hAll |
    ⟨t, pre, rest, front, trail, hEs, hVs, hFront, hPc, hShape, hRegs, hPre, hTail⟩
  · obtain ⟨v, hv, hEq⟩ := eventVisit hw hSeen
    have hBad := hAll v hv
    rw [hEq, notInsidePacket site hPub] at hBad
    cases hBad
  have ht : t.pc = reuseArrival site := by simpa [r, CursorRoute.stops] using hPc
  have hFound : seen ∈ rest := by
    rw [hEs] at hSeen
    rcases List.mem_append.mp hSeen with h | h
    · obtain ⟨v, hv, hEq⟩ := eventVisit hPre h
      have hBad := hFront v hv
      rw [hEq, notInsidePacket site hPub] at hBad
      cases hBad
    · exact h
  have hBounds : 174 ≤ reuseArrival site ∧ reuseArrival site < 1901 := by
    fin_cases site <;> decide
  cases hTail with
  | stop => cases hFound
  | @tau _ u _ _ h _ =>
    have hCode := (copyCommitCode (recurringPacketSite site)).2
    change kernel.code[reuseArrival site]? = _ at hCode
    rw [← ht] at hCode
    have hCore : Tau kernel [] l g t u := by
      unfold Tau at *
      rwa [← loaderOutCore (by omega) (by omega)]
    exact (tau_core_not_event hCode rfl hCore).elim
  | last h =>
    obtain rfl := List.mem_singleton.mp hFound
    obtain ⟨_, _, hFire⟩ := h
    have hEnd := fires_none_ends hFire
    obtain ⟨_, _, rfl⟩ := hPub
    simp [Ends] at hEnd
  | @ev _ u event suffix post hStep hWalk =>
    obtain ⟨target, hKind, rfl⟩ := packetArrivalStepFrame (recurringPacketSite site) ht hStep
    have hEvent : event = ⟨reuseArrival site, .asyncArrive target true⟩ := by
      cases event
      rw [Event.mk.injEq]
      exact ⟨(estep_source_pc hStep).trans ht, hKind⟩
    subst event
    have hClipVisits : vs.take (front.length + 1) =
        front ++ [visit kernel l g t (some ⟨reuseArrival site, .asyncArrive target true⟩)] := by
      rw [hVs, List.take_append]
      simp
    have hClip := takeLoaderVisits hw (front.length + 1)
    rw [hClipVisits, List.filterMap_append, ← hPre.events] at hClip
    simp only [List.filterMap_cons, visit_ev, List.filterMap_nil] at hClip
    have hElem : ∀ v ∈ front ++
        [visit kernel l g t (some ⟨reuseArrival site, .asyncArrive target true⟩)],
        (reuseEntry site ≤ v.pc && v.pc < reuseArrival site + 1) = true := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · have hP := hFront v hv
        simp only [r, CursorRoute.inside, decide_eq_true_eq] at hP
        exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hP.1, decide_eq_true (by omega)⟩
      · obtain rfl := List.mem_singleton.mp hv
        have hB : reuseEntry site ≤ reuseArrival site := by fin_cases site <;> decide
        simp [visit_pc, ht, hB]
    have hSlice : ⟨reuseArrival site, .asyncArrive target true⟩ ∈
      loaderSliceEvents (reuseEntry site)
        (reuseArrival site + 1)
        (front ++ [visit kernel l g t (some ⟨reuseArrival site, .asyncArrive target true⟩)]) := by
      unfold loaderSliceEvents
      have hKeep {xs : List Visit}
          (h : ∀ v ∈ xs, (reuseEntry site ≤ v.pc && v.pc < reuseArrival site + 1) = true) :
          xs.takeWhile (fun v => reuseEntry site ≤ v.pc && v.pc < reuseArrival site + 1) = xs :=
        by
          induction xs with
          | nil => rfl
          | cons x xs ih =>
            rw [List.takeWhile_cons_of_pos
              (p := fun v : Visit => reuseEntry site ≤ v.pc && v.pc < reuseArrival site + 1)
              (h x (by simp)), ih (fun v hv => h v (by simp [hv]))]
      rw [hKeep hElem, List.filterMap_append, ← hPre.events]
      simp [visit_ev]
    have hInput : At s (reuseEntry site)
        (recurringBarrierInput l site (kvUseStage use) (if kvEmptyPhase use then 1 else 0)) :=
      hs.mono ⟨hs.2.2.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.2.1, trivial⟩
    have hPar : (if kvEmptyPhase use then 1 else 0) < 2 := by split <;> decide
    obtain ⟨n, mid, trail, stops, hSplit, hLoc, hMid, hTrailWalk, hTrail⟩ :=
      recurringReadyArrivalCut hp site (kvUseStage use) hPar hInput hClip hSlice
    have hNonempty : trail ≠ [] := by
      rintro rfl
      cases hTrail
    have hLength : n + 1 ≤ pre.length := by
      have hEq := congrArg List.length hSplit
      have hPos := List.length_pos_iff.mpr hNonempty
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil] at hEq
      omega
    let empty := Prologue.initObject l (g / l.block) (emptySlot (kvUseStage use))
    let parity := if kvEmptyPhase use then 1 else 0
    let poll := fun ok => (⟨(recurringEmptyWait site).pc, .wait empty parity ok true .cta⟩ : Event)
    let warm := List.replicate n (poll false) ++ [poll true]
    have hSplit' : pre ++ [⟨reuseArrival site, .asyncArrive target true⟩] = warm ++ trail := by
      simpa only [warm, List.append_assoc, List.singleton_append] using hSplit
    have hWarm : warm.length = n + 1 := by simp [warm]
    have hTake := congrArg (List.take (n + 1)) hSplit'
    rw [List.take_append_of_le_length hLength, ← hWarm, List.take_left' rfl] at hTake
    have hPreEq : pre = warm ++ pre.drop (n + 1) := by
      rw [← hTake, hWarm, List.take_append_drop]
    have hTrailEq :
        trail = pre.drop (n + 1) ++ [⟨reuseArrival site, .asyncArrive target true⟩] := by
      apply List.append_cancel_left (as := warm)
      rw [← List.append_assoc, ← hPreEq, hSplit']
    have hNoPub : ∀ e ∈ pre.drop (n + 1), ¬ recurringPublicationEvent e := by
      intro event he hPub
      obtain ⟨v, hv, hp⟩ := eventVisit hPre (List.mem_of_mem_drop he)
      have hBad := hFront v hv
      rw [hp, notInsidePacket site hPub] at hBad
      cases hBad
    have hNoEmpty : ∀ e ∈ pre.drop (n + 1), ¬ recurringEmptyEvent e := by
      let rr := CursorRoute.packetAfterPoll site
      have hEntry : rr.inside mid.pc = true := by
        rw [hMid.1]
        fin_cases site <;> decide
      have hArr : (⟨reuseArrival site, .asyncArrive target true⟩ : Event) ∈ trail := by
        rw [hTrailEq]
        simp
      have hOut : rr.inside (reuseArrival site) = false := by
        fin_cases site <;> decide
      rcases rr.cutWalk hTrailWalk hEntry (ringShapeOfAt hMid) with hAll |
        ⟨lastState, leading, rest, before, after, hEvents, _, hBefore, hPc, _, _, hPrefix, hRest⟩
      · obtain ⟨v, hv, hSame⟩ := eventVisit hTrailWalk hArr
        have hBad := hAll v hv
        rw [hSame, hOut] at hBad
        cases hBad
      have hLast : lastState.pc = reuseArrival site := by
        simpa [rr, CursorRoute.stops] using hPc
      have hArrRest : (⟨reuseArrival site, .asyncArrive target true⟩ : Event) ∈ rest := by
        rw [hEvents] at hArr
        refine (List.mem_append.mp hArr).resolve_left (fun he => ?_)
        obtain ⟨v, hv, hSame⟩ := eventVisit hPrefix he
        have hBad := hBefore v hv
        rw [hSame, hOut] at hBad
        cases hBad
      have hHead : ∃ e tail, rest = e :: tail ∧ e.pc = reuseArrival site := by
        cases hRest with
        | stop => cases hArrRest
        | @tau _ u _ _ h _ =>
          have hCode := (copyCommitCode (recurringPacketSite site)).2
          change kernel.code[reuseArrival site]? = _ at hCode
          rw [← hLast] at hCode
          have hCore : Tau kernel [] l g lastState u := by
            unfold Tau at *
            rwa [← loaderOutCore (by omega) (by omega)]
          exact (tau_core_not_event hCode rfl hCore).elim
        | ev h _ => exact ⟨_, _, rfl, (estep_source_pc h).trans hLast⟩
        | last h => exact ⟨_, [], rfl, (estep_source_pc h).trans hLast⟩
      obtain ⟨e, endTail, heq, hep⟩ := hHead
      have hLen : leading.length = (pre.drop (n + 1)).length := by
        have hLengths := congrArg List.length (hEvents.symm.trans hTrailEq)
        rw [heq] at hLengths
        simp only [List.length_append, List.length_cons, List.length_nil] at hLengths
        by_contra hNe
        have hLt : leading.length < (pre.drop (n + 1)).length := by omega
        have hAtIndex := congrArg (fun xs : List Event => xs[leading.length]?)
          (hEvents.symm.trans hTrailEq)
        rw [heq, List.getElem?_append_right (by omega), Nat.sub_self,
          List.getElem?_cons_zero, List.getElem?_append_left hLt] at hAtIndex
        have hMem := List.mem_of_getElem? hAtIndex.symm
        obtain ⟨v, hv, hSame⟩ := eventVisit hPre (List.mem_of_mem_drop hMem)
        have hBad := hFront v hv
        rw [hSame, hep, notInsidePacket site (show recurringPublicationEvent
          ⟨reuseArrival site, .asyncArrive target true⟩ from ⟨site, target, rfl⟩)] at hBad
        cases hBad
      have hEq : pre.drop (n + 1) = leading := by
        have hTake := congrArg (List.take leading.length) (hEvents.symm.trans hTrailEq)
        rw [List.take_left' rfl, hLen, List.take_left' rfl] at hTake
        exact hTake.symm
      intro event he hSuc
      rw [hEq] at he
      obtain ⟨v, hv, hSame⟩ := eventVisit hPrefix he
      have hBad := hBefore v hv
      rw [hSame] at hBad
      obtain ⟨other, _, _, rfl⟩ := hSuc
      fin_cases site <;> fin_cases other <;> cases hBad
    have hClean : t.fault = none := by
      obtain ⟨tm, ho, hf⟩ := hStep
      cases h : t.fault
      · rfl
      · simp only [out, h, Out.ev.injEq] at ho
        subst tm
        cases hf.2
    have hU : (next t).pc = reuseArrival site + 1 := by simp [next, ht]
    have hShape' := loaderPipelineStepShape (by omega : 174 ≤ t.pc) (by omega : t.pc < 1901)
      hShape (.inr ⟨_, rfl, hStep⟩)
    have hFrame : Holds (next t).regs (emptyCursorFrame l site use) := by
      exact ⟨(hRegs 2535 (by simp [r, CursorRoute.registers])).trans hs.2.2.2.2.1,
        (hRegs (recurringStageInputs site).1 (by simp [r, CursorRoute.registers])).trans
          hs.2.2.2.2.2.1,
        (hRegs (recurringEmptyWait site).phase (by simp [r, CursorRoute.registers])).trans
          hs.2.2.2.2.2.2.1, trivial⟩
    have hAt := pipelineAtCut hU hShape' hFrame hClean (advanceCode site)
    refine ⟨n, pre.drop (n + 1), suffix, next t, post, ?_, ?_,
      ⟨front ++ [visit kernel l g t (some ⟨reuseArrival site, .asyncArrive target true⟩)],
        by rw [hVs, List.append_assoc]; rfl⟩,
      (fun e he => ⟨hNoPub e he, hNoEmpty e he⟩), hAt, hWalk⟩
    · rw [hEs, hLoc]
      calc
        _ = (warm ++ pre.drop (n + 1)) ++ _ :=
          congrArg (fun ys => ys ++ ⟨reuseArrival site, .asyncArrive _ true⟩ :: suffix) hPreEq
        _ = _ := by simp [warm, poll, empty, parity, List.append_assoc]
    · rw [hVs, List.length_append, List.length_cons]
      omega

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
