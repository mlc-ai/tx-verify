-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorPacket
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part018
import Kernels.TmlFa4Fwd.Flow.Code.Part021
import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Kernels.TmlFa4Fwd.Flow.Code.Part025

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader
  (reuseEntry reuseArrival recurringPacketSite copyCommitPc recurringStageInputs
    recurringEmptyWait loaderRingWrites loaderSegmentFrame ringShapeOfAt
    pipelineAtCut walkWithArrivalClean loaderSliceEvents actualEmptySeedPrefix)

noncomputable section

variable {l : Launch}

/-- An event-free local run has an exact visit suffix in a continuing actual walk. -/
theorem walkAfterLocalExact {g n : Nat} {s u : TState} {es : List Event} {vs : List Visit}
    (hr : run kernel Assumptions.all l g n s = some u)
    (hw : Walk kernel Assumptions.all l g s es vs) :
    es = [] ∨ Walk kernel Assumptions.all l g u es (vs.drop n) := by
  induction n generalizing s es vs with
  | zero =>
    obtain rfl := Option.some.inj hr
    exact .inr hw
  | succ n ih =>
    simp only [run] at hr
    cases ht : tauStep kernel Assumptions.all l g s with
    | none => simp [ht] at hr
    | some t =>
      rw [ht, Option.bind_some] at hr
      have hTau := tauStep_iff.mp ht
      cases hw with
      | stop => exact .inl rfl
      | tau he hw =>
        obtain rfl := Out.tau.inj (hTau.symm.trans he)
        exact ih hr hw
      | ev he _ => exact (not_tau_of_stops (stops_of_estep he) hTau).elim
      | last he => exact (not_tau_of_stops (stops_of_estep he) hTau).elim

/-- The arithmetic cursor advance also preserves the shared-memory base. -/
theorem advanceEmptyCursorFramed {g use : Nat} (site : Fin 4) :
    Seg kernel Assumptions.all l g 5 (reuseArrival site + 1) (emptyCursorFrame l site use)
      (reuseArrival site + 6) (emptyCursorFrame l (reuseCursorSuccessor site) (use + 1)) := by
  intro s hs
  obtain ⟨u, hr, hU⟩ := advanceEmptyCursor site use s (hs.mono hs.2.2.2.2.2)
  have hLo : 174 ≤ reuseArrival site + 1 := by fin_cases site <;> decide
  have hHi : reuseArrival site + 1 + 5 ≤ 1901 := by fin_cases site <;> decide
  have hCode : ((kernel.code.drop (reuseArrival site + 1)).take 5).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op &&
        [2535].all fun reg => !(loaderRingWrites ins.op).contains reg) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hStep : ((kernel.code.drop (reuseArrival site + 1)).take
      (reuseArrival site + 1 + 5 - (reuseArrival site + 1))).all
        (fun ins => Epilogue.schedulerFallsThrough ins.op &&
          [2535].all fun reg => !(loaderRingWrites ins.op).contains reg) = true := by
    simpa only [Nat.add_sub_cancel_left] using hCode
  obtain ⟨_, hRegs⟩ := loaderSegmentFrame (regs := [2535]) hLo hHi hStep hr
    (Nat.le_of_eq hs.1.symm) (by rw [hs.1])
  exact ⟨u, hr, hU.mono ⟨(hRegs 2535 (by simp)).trans hs.2.2.2.2.1, hU.2.2.2.2⟩⟩

private theorem gapNoPublication (r : CursorRoute) (hGap : r = .warmV ∨ r = .warmK ∨ r = .steadyK)
    {e : Event} (h : r.inside e.pc = true) : ¬ recurringPublicationEvent e := by
  rintro ⟨site, _, rfl⟩
  rcases hGap with rfl | rfl | rfl <;> fin_cases site <;> cases h

private theorem gapNoEmpty (r : CursorRoute) (hGap : r = .warmV ∨ r = .warmK ∨ r = .steadyK)
    {e : Event} (h : r.inside e.pc = true) : ¬ recurringEmptyEvent e := by
  rintro ⟨site, _, _, rfl⟩
  rcases hGap with rfl | rfl | rfl <;> fin_cases site <;> cases h

private theorem entryCode (site : Fin 4) :
    ∃ ins, kernel.code[reuseEntry site]? = some ins ∧ ins.op.isLocal = true := by
  fin_cases site
  · exact ⟨_, Flow.code_957, rfl⟩
  · exact ⟨_, Flow.code_1203, rfl⟩
  · exact ⟨_, Flow.code_1427, rfl⟩
  · exact ⟨_, Flow.code_1608, rfl⟩

/-- Every event in an audited walk comes from a visit in that route. -/
theorem eventInside {g : Nat} {s : TState} {es : List Event} {vs : List Visit} (r : CursorRoute)
    (hw : Walk kernel Assumptions.all l g s es vs) (hVisits : ∀ v ∈ vs, r.inside v.pc = true) :
    ∀ e ∈ es, r.inside e.pc = true := by
  induction hw with
  | stop => simp
  | tau _ _ ih =>
    exact ih (fun v hv => hVisits v (List.mem_cons_of_mem _ hv))
  | ev h _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · rw [estep_source_pc h]
      exact hVisits _ List.mem_cons_self
    · exact ih (fun v hv => hVisits v (List.mem_cons_of_mem _ hv)) e he
  | last h =>
    intro e he
    obtain rfl := List.mem_singleton.mp he
    rw [estep_source_pc h]
    exact hVisits _ List.mem_cons_self

/-- An actual issue of one of the recurring packet's vectors. -/
def recurringVectorEvent (event : Event) : Prop :=
  ∃ (site : Fin 4) (pair : Fin 16) (upper : Bool) (spec : AsyncCopy.Spec),
    event = ⟨Loader.packetPlanePc (recurringPacketSite site) pair upper, .copy spec⟩

/-- A recorded empty-slot poll, including an incomplete retry of a recurring packet. -/
def recurringPollAttempt (event : Event) : Prop :=
  ∃ (site : Fin 4) (loc : Loc) (parity : Nat) (ok acquire : Bool) (scope : MbarScope),
    event = ⟨(Loader.recurringEmptyWait site).pc, .wait loc parity ok acquire scope⟩

/-- The observed work inside a packet before its publication. -/
def recurringPacketWork (event : Event) : Prop :=
  recurringVectorEvent event ∨ recurringPollAttempt event

theorem recurringPacketWorkContinues {e : Event} (h : recurringPacketWork e) : ¬ Ends e := by
  rcases h with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;> simp [Ends]

/-- A boundary that reaches the recurring packet cursor. -/
def recurringCursorBoundary (event : Event) : Prop :=
  recurringPublicationEvent event ∨ recurringPacketWork event

private theorem boundaryContinues {e : Event} (h : recurringCursorBoundary e) : ¬ Ends e := by
  rcases h with ⟨_, _, rfl⟩ | h
  · simp [Ends]
  · exact recurringPacketWorkContinues h

private theorem gapNoPacketWork (r : CursorRoute)
    (hGap : r = .warmV ∨ r = .warmK ∨ r = .steadyK ∨ r = .seedDispatch)
    {e : Event} (h : r.inside e.pc = true) : ¬ recurringPacketWork e := by
  rintro (⟨site, pair, upper, _, rfl⟩ | ⟨site, loc, parity, ok, acq, scope, rfl⟩)
  · rcases hGap with rfl | rfl | rfl | rfl <;>
      fin_cases site <;> fin_cases pair <;> cases upper <;> cases h
  · rcases hGap with rfl | rfl | rfl | rfl <;> fin_cases site <;> cases h

private theorem nextOverGap {g use : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (r : CursorRoute) (f : Fin 4) (hGap : r = .warmV ∨ r = .warmK ∨ r = .steadyK)
    (hRegs : ∀ reg ∈ (emptyCursorFrame l f use).map Prod.fst, reg ∈ r.registers)
    (hTargets : ∀ pc ∈ r.stops, pc < 1744 →
      ∃ j : Fin 4, pc = reuseEntry j ∧ emptyCursorFrame l f use = emptyCursorFrame l j use ∧
        j.val % 2 = f.val % 2) (hs : At s s.pc (emptyCursorFrame l f use))
    (hw : Walk kernel Assumptions.all l g s es vs) (hIn : r.inside s.pc = true)
    (hScope : ∀ v ∈ vs, v.pc < 1744) (hSeen : ∃ e ∈ es, recurringCursorBoundary e) :
    ∃ (j : Fin 4) (t : TState) (pre tail : List Event) (post : List Visit),
      es = pre ++ tail ∧ post <:+ vs ∧ At t (reuseEntry j) (emptyCursorFrame l j use) ∧
      j.val % 2 = f.val % 2 ∧
      (∀ e ∈ pre, ¬ recurringPublicationEvent e ∧
          ¬ recurringEmptyEvent e ∧ ¬ recurringPacketWork e) ∧
      Walk kernel Assumptions.all l g t tail post := by
  obtain ⟨e, he, hBoundary⟩ := hSeen
  have hRoute : r = .warmV ∨ r = .warmK ∨ r = .steadyK ∨ r = .seedDispatch := by
    rcases hGap with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  rcases r.cutWalk hw hIn (ringShapeOfAt hs) with hStay |
      ⟨t, pre, tail, front, post, hEs, hVs, hFront, ht, hShape, hPres, hPre, hTail⟩
  · have hInside := eventInside r hw hStay e he
    exact (hBoundary.elim (gapNoPublication r hGap hInside) (gapNoPacketWork r hRoute hInside)).elim
  have hNo : ∀ e ∈ pre, ¬ recurringPublicationEvent e ∧
      ¬ recurringEmptyEvent e ∧ ¬ recurringPacketWork e := by
    intro ev hev
    have hv := eventInside r hPre hFront ev hev
    exact ⟨gapNoPublication r hGap hv, gapNoEmpty r hGap hv, gapNoPacketWork r hRoute hv⟩
  have hEvent : e ∈ tail := by
    rw [hEs] at he
    exact (List.mem_append.mp he).resolve_left (fun hm => hBoundary.elim (hNo e hm).1
      (hNo e hm).2.2)
  have hBefore : t.pc < 1744 := by
    cases post with
    | nil => rw [hTail.events] at hEvent; cases hEvent
    | cons v vs' =>
      have hP := hTail.zero_pc rfl
      rw [← hP]
      exact hScope v (by rw [hVs]; simp)
  obtain ⟨site, hPc, hWords, hPlane⟩ := hTargets t.pc ht hBefore
  have hShape' : Holds t.regs (emptyCursorFrame l f use) := by
    apply Epilogue.holdsSchedulerFrame hs.2.2.2.2
    · intro reg hr
      exact hPres reg (hRegs reg hr)
    · exact fun _ h => List.mem_map_of_mem h
  have hClean := PTX.Kernels.TmlFa4Fwd.Loader.walkWithContinuingEventClean hTail hEvent
    (boundaryContinues hBoundary)
  have hAt := pipelineAtCut hPc hShape hShape' hClean (entryCode site)
  rw [hWords] at hAt
  exact ⟨site, t, pre, tail, post, hEs, ⟨front, hVs.symm⟩, hAt, hPlane, hNo, hTail⟩

/-- Advance and cross the actual instructions between two publications, keeping the
next packet's cursor. The prefix considered here ends before the drain. -/
theorem nextEmptyPacketAtBoundary {g use : Nat} (site : Fin 4) {s : TState} {es : List Event}
    {vs : List Visit} (hs : At s (reuseArrival site + 1) (emptyCursorFrame l site use))
    (hw : Walk kernel Assumptions.all l g s es vs) (hScope : ∀ v ∈ vs, v.pc < 1744)
    (hSeen : ∃ e ∈ es, recurringCursorBoundary e) :
    ∃ (j : Fin 4) (t : TState) (pre tail : List Event) (post : List Visit),
      es = pre ++ tail ∧ post <:+ vs ∧ At t (reuseEntry j) (emptyCursorFrame l j (use + 1)) ∧
      j.val % 2 = (site.val + 1) % 2 ∧
      (∀ e ∈ pre, ¬ recurringPublicationEvent e ∧
          ¬ recurringEmptyEvent e ∧ ¬ recurringPacketWork e) ∧
      Walk kernel Assumptions.all l g t tail post := by
  obtain ⟨t, hr, ht⟩ := advanceEmptyCursorFramed site s hs
  rcases walkAfterLocalExact hr hw with hNil | hWalk
  · rw [hNil] at hSeen
    simp at hSeen
  have hSuffix : vs.drop 5 <:+ vs := ⟨vs.take 5, List.take_append_drop 5 vs⟩
  have hScope' : ∀ v ∈ vs.drop 5, v.pc < 1744 :=
    fun v hv => hScope v (hSuffix.sublist.subset hv)
  have done (r : CursorRoute)
      (hGap : r = .warmV ∨ r = .warmK ∨ r = .steadyK)
      (hRegs : ∀ reg ∈ (emptyCursorFrame l (reuseCursorSuccessor site) (use + 1)).map Prod.fst,
        reg ∈ r.registers)
      (hTargets : ∀ pc ∈ r.stops, pc < 1744 → ∃ j : Fin 4, pc = reuseEntry j ∧
        emptyCursorFrame l (reuseCursorSuccessor site) (use + 1) =
          emptyCursorFrame l j (use + 1) ∧ j.val % 2 = (reuseCursorSuccessor site).val % 2)
      (hRoute : r.inside t.pc = true) :
      ∃ (j : Fin 4) (t : TState) (pre tail : List Event) (post : List Visit),
        es = pre ++ tail ∧ post <:+ vs ∧ At t (reuseEntry j) (emptyCursorFrame l j (use + 1)) ∧
        j.val % 2 = (site.val + 1) % 2 ∧
        (∀ e ∈ pre, ¬ recurringPublicationEvent e ∧
          ¬ recurringEmptyEvent e ∧ ¬ recurringPacketWork e) ∧
        Walk kernel Assumptions.all l g t tail post := by
    obtain ⟨j, u, pre, tail, post, hEs, hPost, hu, hPlane, hNo, hTail⟩ :=
      nextOverGap r _ hGap hRegs hTargets ⟨rfl, ht.2⟩ hWalk hRoute hScope' hSeen
    have hSuccessor : (reuseCursorSuccessor site).val % 2 = (site.val + 1) % 2 := by
      fin_cases site <;> decide
    exact ⟨j, u, pre, tail, post, hEs, hPost.trans hSuffix, hu,
      hPlane.trans hSuccessor, hNo, hTail⟩
  fin_cases site
  · apply done .warmV (.inl rfl)
    · simp [emptyCursorFrame, reuseCursorWords, reuseCursorSuccessor, recurringStageInputs,
        recurringEmptyWait, CursorRoute.registers]
    · intro pc hm _
      have h : pc = 1203 := by simpa [CursorRoute.stops] using hm
      exact ⟨1, h, rfl, rfl⟩
    · rw [ht.1]; decide
  · apply done .warmK (.inr (.inl rfl))
    · simp [emptyCursorFrame, reuseCursorWords, reuseCursorSuccessor, recurringStageInputs,
        recurringEmptyWait, CursorRoute.registers]
    · intro pc hm hLt
      simp [CursorRoute.stops] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨0, rfl, rfl, rfl⟩
      · exact ⟨2, rfl, rfl, rfl⟩
      · omega
    · rw [ht.1]; decide
  · exact ⟨3, t, [], es, vs.drop 5, by simp, hSuffix, ht, rfl, by simp, hWalk⟩
  · apply done .steadyK (.inr (.inr rfl))
    · simp [emptyCursorFrame, reuseCursorWords, reuseCursorSuccessor, recurringStageInputs,
        recurringEmptyWait, CursorRoute.registers]
    · intro pc hm hLt
      simp [CursorRoute.stops] at hm
      rcases hm with rfl | rfl
      · exact ⟨2, rfl, rfl, rfl⟩
      · omega
    · rw [ht.1]; decide

private theorem seedEmptyCursorFramed {g : Nat} (seed : Fin 2) :
    Seg kernel Assumptions.all l g 2 (cursorSeedPc seed) [(2535, b32 l.sharedBase)]
      (cursorSeedPc seed + 2) (emptyCursorFrame l 0 2) := by
  intro s hs
  obtain ⟨u, hr, hu⟩ := seedEmptyCursor seed s (hs.mono trivial)
  have hLo : 174 ≤ cursorSeedPc seed := by fin_cases seed <;> decide
  have hHi : cursorSeedPc seed + 2 ≤ 1901 := by fin_cases seed <;> decide
  have hStep : ((kernel.code.drop (cursorSeedPc seed)).take
      (cursorSeedPc seed + 2 - cursorSeedPc seed)).all
        (fun ins => Epilogue.schedulerFallsThrough ins.op &&
          [2535].all fun reg => !(loaderRingWrites ins.op).contains reg) = true := by
    fin_cases seed <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨_, hRegs⟩ := loaderSegmentFrame (regs := [2535]) hLo hHi hStep hr
    (Nat.le_of_eq hs.1.symm) (by rw [hs.1])
  exact ⟨u, hr, hu.mono ⟨(hRegs 2535 (by simp)).trans hs.2.2.2.2.1, hu.2.2.2.2⟩⟩

/-- Follow the actual cursor initialization and dispatch to the first recurring packet. -/
theorem firstEmptyPacketAtBoundary {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 909 [(2535, b32 l.sharedBase)]) (hw : Walk kernel Assumptions.all l g s es vs)
    (hScope : ∀ v ∈ vs, v.pc < 1744) (hSeen : ∃ e ∈ es, recurringCursorBoundary e) :
    ∃ (j : Fin 4) (t : TState) (pre tail : List Event) (post : List Visit),
      es = pre ++ tail ∧ post <:+ vs ∧ At t (reuseEntry j) (emptyCursorFrame l j 2) ∧
      j.val % 2 = 0 ∧
      (∀ e ∈ pre, ¬ recurringPublicationEvent e ∧
          ¬ recurringEmptyEvent e ∧ ¬ recurringPacketWork e) ∧
      Walk kernel Assumptions.all l g t tail post := by
  obtain ⟨u, hr, hu⟩ := seedEmptyCursorFramed (0 : Fin 2) s hs
  rcases walkAfterLocalExact hr hw with hNil | hWalk
  · rw [hNil] at hSeen
    simp at hSeen
  have hScope' {xs : List Visit} (h : xs <:+ vs) : ∀ v ∈ xs, v.pc < 1744 :=
    fun v hv => hScope v (h.sublist.subset hv)
  have hSuffix (n : Nat) (xs : List Visit) : xs.drop n <:+ xs :=
    ⟨xs.take n, List.take_append_drop n xs⟩
  let r := CursorRoute.seedDispatch
  have hIn : r.inside u.pc = true := by rw [hu.1]; decide
  have hNoPub {e : Event} (he : r.inside e.pc = true) : ¬ recurringPublicationEvent e := by
    rintro ⟨i, loc, rfl⟩
    fin_cases i <;> cases he
  have hNoEmpty {e : Event} (he : r.inside e.pc = true) : ¬ recurringEmptyEvent e := by
    rintro ⟨i, loc, parity, rfl⟩
    fin_cases i <;> cases he
  obtain ⟨e, he, hBoundary⟩ := hSeen
  rcases r.cutWalk hWalk hIn (ringShapeOfAt hu) with hStay |
    ⟨t, left, rest, front, next, hEs, hVs, hFront, ht, hShape, hPres, hPre, hTail⟩
  · have hInside := eventInside r hWalk hStay e he
    exact (hBoundary.elim (hNoPub hInside)
      (gapNoPacketWork r (.inr (.inr (.inr rfl))) hInside)).elim
  have hNo : ∀ e ∈ left, ¬ recurringPublicationEvent e ∧
      ¬ recurringEmptyEvent e ∧ ¬ recurringPacketWork e := by
    intro value hm
    have hVal := eventInside r hPre hFront value hm
    exact ⟨hNoPub hVal, hNoEmpty hVal, gapNoPacketWork r (.inr (.inr (.inr rfl))) hVal⟩
  have hRest : e ∈ rest := by
    rw [hEs] at he
    exact (List.mem_append.mp he).resolve_left (fun hm => hBoundary.elim (hNo e hm).1
      (hNo e hm).2.2)
  have hSuf : next <:+ vs := (show next <:+ vs.drop 2 from ⟨front, hVs.symm⟩).trans (hSuffix 2 vs)
  have hF : Holds t.regs (emptyCursorFrame l 0 2) := by
    refine ⟨(hPres 2535 (by decide)).trans hu.2.2.2.2.1, ?_, ?_, trivial⟩
    · exact (hPres 7179 (by decide)).trans hu.2.2.2.2.2.1
    · exact (hPres 7180 (by decide)).trans hu.2.2.2.2.2.2.1
  have hClean := PTX.Kernels.TmlFa4Fwd.Loader.walkWithContinuingEventClean hTail hRest
    (boundaryContinues hBoundary)
  have finish {a : TState} {visits : List Visit}
      (ha : At a a.pc (emptyCursorFrame l 0 2))
      (hA : Walk kernel Assumptions.all l g a rest visits)
      (hVisits : visits <:+ vs) (hRoute : CursorRoute.warmK.inside a.pc = true) :
      ∃ (j : Fin 4) (t : TState) (pre tail : List Event) (post : List Visit),
        es = pre ++ tail ∧ post <:+ vs ∧ At t (reuseEntry j) (emptyCursorFrame l j 2) ∧
        j.val % 2 = 0 ∧
        (∀ e ∈ pre, ¬ recurringPublicationEvent e ∧
          ¬ recurringEmptyEvent e ∧ ¬ recurringPacketWork e) ∧
        Walk kernel Assumptions.all l g t tail post := by
    have hRegs : ∀ reg ∈ (emptyCursorFrame l 0 2).map Prod.fst,
        reg ∈ CursorRoute.warmK.registers := by
      simp [emptyCursorFrame, reuseCursorWords, recurringStageInputs,
        recurringEmptyWait, CursorRoute.registers]
    have hTargets : ∀ pc ∈ CursorRoute.warmK.stops, pc < 1744 →
        ∃ j : Fin 4, pc = reuseEntry j ∧ emptyCursorFrame l 0 2 = emptyCursorFrame l j 2 ∧
          j.val % 2 = 0 := by
      intro pc hm hLt
      simp [CursorRoute.stops] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨0, rfl, rfl, rfl⟩
      · exact ⟨2, rfl, rfl, rfl⟩
      · omega
    obtain ⟨j, b, pre, tail, post, hSplit, hPost, hb, hPlane, hNone, hNext⟩ :=
      nextOverGap .warmK 0 (.inr (.inl rfl)) hRegs hTargets ha hA hRoute
        (hScope' hVisits) ⟨e, hRest, hBoundary⟩
    refine ⟨j, b, left ++ pre, tail, post, by rw [hEs, hSplit, List.append_assoc],
      hPost.trans hVisits, hb, hPlane, ?_, hNext⟩
    intro value hMem
    exact (List.mem_append.mp hMem).elim (hNo value) (hNone value)
  have hDest : t.pc = 914 ∨ t.pc = 1353 := by simpa [r, CursorRoute.stops] using ht
  rcases hDest with hPc | hPc
  · have hAt := pipelineAtCut hPc hShape hF hClean ⟨_, Flow.code_914, rfl⟩
    obtain ⟨a, hRun, ha⟩ := seedEmptyCursorFramed (1 : Fin 2) t
      (hAt.mono ⟨hF.1, trivial⟩)
    rcases walkAfterLocalExact hRun hTail with hNil | hA
    · rw [hNil] at hRest
      cases hRest
    · exact finish ⟨rfl, ha.2⟩ hA ((hSuffix 2 next).trans hSuf) (by rw [ha.1]; decide)
  · have hAt := pipelineAtCut hPc hShape hF hClean ⟨_, Flow.code_1353, rfl⟩
    exact finish ⟨rfl, hAt.2⟩ hTail hSuf (by rw [hPc]; decide)

end
variable {l : Launch}

theorem nextEmptyPacket {g use : Nat} (site : Fin 4) {s : TState} {es : List Event}
    {vs : List Visit} (hs : At s (reuseArrival site + 1) (emptyCursorFrame l site use))
    (hw : Walk kernel Assumptions.all l g s es vs) (hScope : ∀ v ∈ vs, v.pc < 1744)
    (hSeen : ∃ e ∈ es, recurringPublicationEvent e) :
    ∃ (j : Fin 4) (t : TState) (pre tail : List Event) (post : List Visit),
      es = pre ++ tail ∧ post <:+ vs ∧ At t (reuseEntry j) (emptyCursorFrame l j (use + 1)) ∧
      j.val % 2 = (site.val + 1) % 2 ∧
      (∀ e ∈ pre, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e) ∧
      Walk kernel Assumptions.all l g t tail post := by
  obtain ⟨e, he, hPub⟩ := hSeen
  obtain ⟨j, t, pre, tail, post, hSplit, hPost, ht, hPlane, hQuiet, hWalk⟩ :=
    nextEmptyPacketAtBoundary site hs hw hScope ⟨e, he, .inl hPub⟩
  exact ⟨j, t, pre, tail, post, hSplit, hPost, ht, hPlane,
    fun ev hm => ⟨(hQuiet ev hm).1, (hQuiet ev hm).2.1⟩, hWalk⟩

theorem firstEmptyPacket {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 909 [(2535, b32 l.sharedBase)]) (hw : Walk kernel Assumptions.all l g s es vs)
    (hScope : ∀ v ∈ vs, v.pc < 1744) (hSeen : ∃ e ∈ es, recurringPublicationEvent e) :
    ∃ (j : Fin 4) (t : TState) (pre tail : List Event) (post : List Visit),
      es = pre ++ tail ∧ post <:+ vs ∧ At t (reuseEntry j) (emptyCursorFrame l j 2) ∧
      j.val % 2 = 0 ∧
      (∀ e ∈ pre, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e) ∧
      Walk kernel Assumptions.all l g t tail post := by
  obtain ⟨e, he, hPub⟩ := hSeen
  obtain ⟨j, t, pre, tail, post, hSplit, hPost, ht, hPlane, hQuiet, hWalk⟩ :=
    firstEmptyPacketAtBoundary hs hw hScope ⟨e, he, .inl hPub⟩
  exact ⟨j, t, pre, tail, post, hSplit, hPost, ht, hPlane,
    fun ev hm => ⟨(hQuiet ev hm).1, (hQuiet ev hm).2.1⟩, hWalk⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
