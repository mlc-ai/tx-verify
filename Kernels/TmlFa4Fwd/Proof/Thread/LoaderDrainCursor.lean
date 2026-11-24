-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRingDrain
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyExit
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part021
import Kernels.TmlFa4Fwd.Flow.Code.Part025
import Kernels.TmlFa4Fwd.Flow.Code.Part027
import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader
  (reuseArrival reuseEntry recurringPacketSite recurringStageInputs recurringEmptyWait
    ringShapeOfAt pipelineAtCut
    RingShape loaderLinear loaderRingWrites loaderSegmentFrame)

noncomputable section

/-- A loader state with a continuing normal exit has no pending fault. -/
private theorem cleanBeforeLoaderExit {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hExit : (⟨9205, .exit⟩ : Event) ∈ es) : s.fault = none := by
  cases hF : s.fault with
  | none => rfl
  | some fault =>
    cases hw with
    | stop => cases hExit
    | tau ht _ => simp [Tau, out, hF] at ht
    | ev he _ =>
      obtain ⟨_, hOut, hFire⟩ := he
      simp only [out, hF, Out.ev.injEq] at hOut
      subst_vars
      exact (by cases hFire.2)
    | last he =>
      obtain rfl := List.mem_singleton.mp hExit
      obtain ⟨_, hOut, hFire⟩ := he
      simp only [out, hF, Out.ev.injEq] at hOut
      subst_vars
      have hKind := congrArg Event.kind hFire.1
      cases hKind

/-- A terminating run through a packet issues its publication. -/
private theorem exitForcesPacketPublication {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (site : Fin 4) (hs : s.pc = reuseEntry site)
    (hShape : RingShape s) (hw : Walk kernel Assumptions.all l g s es vs)
    (hExit : (⟨9205, .exit⟩ : Event) ∈ es) :
    ∃ e ∈ es, recurringPublicationEvent e := by
  let r := CursorRoute.packet site
  have hIn : r.inside s.pc = true := by rw [hs]; fin_cases site <;> decide
  have hOut : r.inside 9205 = false := by fin_cases site <;> rfl
  rcases r.cutWalk hw hIn hShape with hAll |
    ⟨u, pre, tail, _, post, hEs, _, hFront, hu, _, _, hPre, hTail⟩
  · exact (Bool.false_ne_true (hOut.symm.trans (eventInside r hw hAll _ hExit))).elim
  have hExitTail : (⟨9205, .exit⟩ : Event) ∈ tail := by
    rw [hEs] at hExit
    refine (List.mem_append.mp hExit).resolve_left fun h => ?_
    exact Bool.false_ne_true (hOut.symm.trans (eventInside r hPre hFront _ h))
  have hArrival : u.pc = reuseArrival site := by simpa [r, CursorRoute.stops] using hu
  obtain ⟨loc, hSeen⟩ := packetArrivalAtExit (recurringPacketSite site) hArrival hTail hExitTail
  exact ⟨_, hEs.symm ▸ List.mem_append_right pre (List.mem_of_getElem? hSeen), ⟨site, loc, rfl⟩⟩

/-- The continuing lane either enters the next copy packet or begins the drain. -/
inductive DrainFrontier (l : Launch) (use : Nat) (t : TState) : Prop
  | packet (site : Fin 4) (ready : At t (reuseEntry site) (emptyCursorFrame l site use))
  | drain (ready : At t 1744 (drainCarry l use))

private theorem entryLocal (site : Fin 4) :
    ∃ ins, kernel.code[reuseEntry site]? = some ins ∧ ins.op.isLocal = true := by
  fin_cases site
  · exact ⟨_, Flow.code_957, rfl⟩
  · exact ⟨_, Flow.code_1203, rfl⟩
  · exact ⟨_, Flow.code_1427, rfl⟩
  · exact ⟨_, Flow.code_1608, rfl⟩

private theorem gapToFrontier {l : Launch} {g use : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (route : CursorRoute) (frame : List (Nat × Value))
    (hs : At s s.pc frame) (hw : Walk kernel Assumptions.all l g s es vs)
    (hIn : route.inside s.pc = true) (hOut : route.inside 9205 = false)
    (hRegs : frame.map Prod.fst ⊆ route.registers)
    (hTarget : ∀ pc ∈ route.stops, (pc = 1744 ∧ frame = drainCarry l use) ∨
      ∃ j : Fin 4, pc = reuseEntry j ∧ frame = emptyCursorFrame l j use)
    (hQuiet : ∀ e, route.inside e.pc = true →
      ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e)
    (hExit : (⟨9205, .exit⟩ : Event) ∈ es) :
    ∃ u pre tail post, es = pre ++ tail ∧ post <:+ vs ∧
      DrainFrontier l use u ∧ Walk kernel Assumptions.all l g u tail post ∧
      (∀ e ∈ pre, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e) ∧
      (⟨9205, .exit⟩ : Event) ∈ tail := by
  rcases route.cutWalk hw hIn (ringShapeOfAt hs) with hAll |
    ⟨u, pre, tail, front, post, hEs, hVs, hFront, hu, hShape, hKeep, hPre, hTail⟩
  · exact (Bool.false_ne_true (hOut.symm.trans (eventInside route hw hAll _ hExit))).elim
  have hExitTail : (⟨9205, .exit⟩ : Event) ∈ tail := by
    rw [hEs] at hExit
    refine (List.mem_append.mp hExit).resolve_left fun h => ?_
    exact Bool.false_ne_true (hOut.symm.trans (eventInside route hPre hFront _ h))
  have hClean := cleanBeforeLoaderExit hTail hExitTail
  have hf : Holds u.regs frame :=
    Epilogue.holdsSchedulerFrame hs.2.2.2.2 (fun r h => hKeep r (hRegs h))
      (fun pair h => List.mem_map_of_mem h)
  have hFound : DrainFrontier l use u := by
    rcases hTarget u.pc hu with ⟨hDrain, hEq⟩ | ⟨j, hPc, hEq⟩
    · exact .drain (pipelineAtCut hDrain hShape (hEq ▸ hf) hClean ⟨_, Flow.code_1744, rfl⟩)
    · exact .packet j (pipelineAtCut hPc hShape (hEq ▸ hf) hClean (entryLocal j))
  exact ⟨u, pre, tail, post, hEs, ⟨front, hVs.symm⟩, hFound, hTail,
    fun e he => hQuiet e (eventInside route hPre hFront e he), hExitTail⟩

private theorem gapQuiet {route : CursorRoute}
    (hRoute : route = .warmV ∨ route = .warmK ∨ route = .steadyK)
    (e : Event) (hIn : route.inside e.pc = true) :
    ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e := by
  constructor
  · rintro ⟨site, _, rfl⟩
    rcases hRoute with rfl | rfl | rfl <;> fin_cases site <;> cases hIn
  · rintro ⟨site, _, _, rfl⟩
    rcases hRoute with rfl | rfl | rfl <;> fin_cases site <;> cases hIn

/-- Advance a finished recurring packet and follow its actual continuation to the
next packet or the start of the drain. -/
theorem packetAdvanceToDrainFrontier {l : Launch} {g use : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (site : Fin 4)
    (hs : At s (reuseArrival site + 1) (emptyCursorFrame l site use))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hExit : (⟨9205, .exit⟩ : Event) ∈ es) :
    ∃ u pre tail post, es = pre ++ tail ∧ post <:+ vs ∧
      DrainFrontier l (use + 1) u ∧ Walk kernel Assumptions.all l g u tail post ∧
      (∀ e ∈ pre, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e) ∧
      (⟨9205, .exit⟩ : Event) ∈ tail := by
  obtain ⟨t, hr, ht⟩ := advanceEmptyCursorFramed site s hs
  rcases walkAfterLocalExact hr hw with hNil | hWalk
  · rw [hNil] at hExit
    cases hExit
  have hDrop : vs.drop 5 <:+ vs := ⟨vs.take 5, List.take_append_drop 5 vs⟩
  let frame := emptyCursorFrame l (reuseCursorSuccessor site) (use + 1)
  have step (route : CursorRoute) (hIn : route.inside t.pc = true)
      (hOut : route.inside 9205 = false) (hRegs : frame.map Prod.fst ⊆ route.registers)
      (hTarget : ∀ pc ∈ route.stops, (pc = 1744 ∧ frame = drainCarry l (use + 1)) ∨
        ∃ j : Fin 4, pc = reuseEntry j ∧ frame = emptyCursorFrame l j (use + 1))
      (hQuiet : ∀ e, route.inside e.pc = true →
        ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e) :
      ∃ u pre tail post, es = pre ++ tail ∧ post <:+ vs ∧
        DrainFrontier l (use + 1) u ∧ Walk kernel Assumptions.all l g u tail post ∧
        (∀ e ∈ pre, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e) ∧
        (⟨9205, .exit⟩ : Event) ∈ tail := by
    obtain ⟨u, pre, tail, post, hEs, hVisits, hAt, hTail, hQuiet, hExit⟩ :=
      gapToFrontier route frame ⟨rfl, ht.2⟩ hWalk hIn hOut hRegs hTarget hQuiet hExit
    exact ⟨u, pre, tail, post, hEs, hVisits.trans hDrop, hAt, hTail, hQuiet, hExit⟩
  fin_cases site
  · refine step .warmV ?_ (by decide) ?_ ?_ (gapQuiet (.inl rfl))
    · rw [ht.1]; decide
    · simp [frame, emptyCursorFrame, reuseCursorWords, reuseCursorSuccessor, recurringStageInputs,
        recurringEmptyWait, CursorRoute.registers]
    · intro pc hPc
      have h : pc = 1203 := by simpa [CursorRoute.stops] using hPc
      exact .inr ⟨1,h,rfl⟩
  · refine step .warmK ?_ (by decide) ?_ ?_ (gapQuiet (.inr (.inl rfl)))
    · rw [ht.1]; decide
    · simp [frame, emptyCursorFrame, reuseCursorWords, reuseCursorSuccessor, recurringStageInputs,
        recurringEmptyWait, CursorRoute.registers]
    · intro pc hPc
      simp [CursorRoute.stops] at hPc
      rcases hPc with rfl | rfl | rfl
      · exact .inr ⟨0,rfl,rfl⟩
      · exact .inr ⟨2,rfl,rfl⟩
      · exact .inl ⟨rfl,rfl⟩
  · exact ⟨t, [], es, _, rfl, hDrop, .packet 3 ht, hWalk, by simp, hExit⟩
  · refine step .steadyK ?_ (by decide) ?_ ?_ (gapQuiet (.inr (.inr rfl)))
    · rw [ht.1]; decide
    · simp [frame, emptyCursorFrame, reuseCursorWords, reuseCursorSuccessor, recurringStageInputs,
        recurringEmptyWait, CursorRoute.registers]
    · intro pc hPc
      simp [CursorRoute.stops] at hPc
      rcases hPc with rfl | rfl
      · exact .inr ⟨2,rfl,rfl⟩
      · exact .inl ⟨rfl,rfl⟩

private theorem seedDrainCursor {l : Launch} {g : Nat} (seed : Fin 2) :
    Seg kernel Assumptions.all l g 2 (cursorSeedPc seed) [(2535, b32 l.sharedBase)]
      (cursorSeedPc seed + 2) (drainCarry l 2) := by
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

/-- Follow the actual cursor initialization to either the first recurring packet
or the drain of a lane with no recurring packets. -/
theorem seedToDrainFrontier {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hs : At s 909 [(2535, b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hExit : (⟨9205, .exit⟩ : Event) ∈ es) :
    ∃ u pre tail post, es = pre ++ tail ∧
      DrainFrontier l 2 u ∧ Walk kernel Assumptions.all l g u tail post ∧
      (∀ e ∈ pre, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e) ∧
      (⟨9205, .exit⟩ : Event) ∈ tail := by
  obtain ⟨t, hRun, ht⟩ := seedDrainCursor 0 s hs
  rcases walkAfterLocalExact hRun hw with hNil | hWalk
  · rw [hNil] at hExit
    cases hExit
  let route := CursorRoute.seedDispatch
  have hIn : route.inside t.pc = true := by rw [ht.1]; decide
  have hOut : route.inside 9205 = false := by decide
  let terminal : Event := ⟨9205, .exit⟩
  rcases route.cutWalk hWalk hIn (ringShapeOfAt ht) with hAll |
    ⟨a, pre, rest, _, trail, hEvents, _, hBefore, hDest, hShape, hRegs, hPre, hTail⟩
  · have hBad := eventInside route hWalk hAll terminal hExit
    rw [show route.inside terminal.pc = false from hOut] at hBad
    cases hBad
  have hExitTail : (⟨9205, .exit⟩ : Event) ∈ rest := by
    rw [hEvents] at hExit
    refine (List.mem_append.mp hExit).resolve_left fun h => ?_
    have hBad := eventInside route hPre hBefore terminal h
    rw [show route.inside terminal.pc = false from hOut] at hBad
    cases hBad
  have hClean := cleanBeforeLoaderExit hTail hExitTail
  have hf : Holds a.regs (drainCarry l 2) :=
    Epilogue.holdsSchedulerFrame ht.2.2.2.2 (fun r h => hRegs r (by
      simpa [route, drainCarry, CursorRoute.registers, or_left_comm, or_comm] using h))
      (fun pair h => List.mem_map_of_mem h)
  have hQuiet : ∀ e ∈ pre, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e := by
    intro e he
    have h := eventInside route hPre hBefore e he
    constructor
    · rintro ⟨site, _, rfl⟩
      fin_cases site <;> cases h
    · rintro ⟨site, _, _, rfl⟩
      fin_cases site <;> cases h
  have finish {b : TState} {visits : List Visit}
      (hb : At b b.pc (drainCarry l 2))
      (hSuffix : Walk kernel Assumptions.all l g b rest visits)
      (hRoute : CursorRoute.warmK.inside b.pc = true) :
      ∃ u front tail post, es = front ++ tail ∧
        DrainFrontier l 2 u ∧ Walk kernel Assumptions.all l g u tail post ∧
        (∀ e ∈ front, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e) ∧
        (⟨9205, .exit⟩ : Event) ∈ tail := by
    have hKeep : (drainCarry l 2).map Prod.fst ⊆ CursorRoute.warmK.registers := by
      intro r hr
      simpa [drainCarry, CursorRoute.registers, or_left_comm, or_comm] using hr
    have hTargets : ∀ pc ∈ CursorRoute.warmK.stops, (pc = 1744 ∧
        drainCarry l 2 = drainCarry l 2) ∨
        ∃ j : Fin 4, pc = reuseEntry j ∧ drainCarry l 2 = emptyCursorFrame l j 2 := by
      intro pc hPc
      simp [CursorRoute.stops] at hPc
      rcases hPc with rfl | rfl | rfl
      · exact .inr ⟨0,rfl,rfl⟩
      · exact .inr ⟨2,rfl,rfl⟩
      · exact .inl ⟨rfl,rfl⟩
    obtain ⟨u, front, tail, post, hEvents', _, hu, hTail, hNo, hExit⟩ :=
      gapToFrontier .warmK (drainCarry l 2) hb hSuffix hRoute (by decide)
        hKeep hTargets (gapQuiet (.inr (.inl rfl))) hExitTail
    exact ⟨u, pre ++ front, tail, post, by rw [hEvents, hEvents', List.append_assoc], hu, hTail,
      fun e he => (List.mem_append.mp he).elim (hQuiet e) (hNo e), hExit⟩
  have hPc : a.pc = 914 ∨ a.pc = 1353 := by simpa [route, CursorRoute.stops] using hDest
  rcases hPc with hPc | hPc
  · have ha := pipelineAtCut hPc hShape hf hClean ⟨_, Flow.code_914, rfl⟩
    obtain ⟨b, hReset, hb⟩ := seedDrainCursor 1 a (ha.mono ⟨hf.1,trivial⟩)
    rcases walkAfterLocalExact hReset hTail with hNil | hNext
    · rw [hNil] at hExitTail
      cases hExitTail
    · exact finish ⟨rfl,hb.2⟩ hNext (by rw [hb.1]; decide)
  · have ha := pipelineAtCut hPc hShape hf hClean ⟨_, Flow.code_1353, rfl⟩
    exact finish ⟨rfl,ha.2⟩ hTail (by rw [hPc]; decide)

/-- The actual recurring uses before the drain, with the total number of uses at its entry. -/
inductive PacketsBeforeDrain (l : Launch) (g : Nat) : Nat → Nat → List Event → Prop
  | done (use : Nat) : PacketsBeforeDrain l g use use []
  | gap {use final : Nat} {pre tail : List Event}
      (quiet : ∀ e ∈ pre, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e)
      (next : PacketsBeforeDrain l g use final tail) :
      PacketsBeforeDrain l g use final (pre ++ tail)
  | packet {use final n : Nat} {site : Fin 4} {mid tail : List Event}
      (quiet : ∀ e ∈ mid, ¬ recurringPublicationEvent e ∧ ¬ recurringEmptyEvent e)
      (next : PacketsBeforeDrain l g (use + 1) final tail) :
      PacketsBeforeDrain l g use final
        (List.replicate n (cursorPoll l g use site false) ++
          cursorPoll l g use site true :: mid ++ cursorArrival l g use site :: tail)

private theorem normalExitLast {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hExit : (⟨9205,.exit⟩ : Event) ∈ es) : es.getLast? = some ⟨9205,.exit⟩ := by
  induction hw with
  | stop => cases hExit
  | tau _ _ ih => exact ih hExit
  | @ev _ _ e _ _ he _ ih =>
    obtain ⟨_, _, hFire⟩ := he
    have hTail := ih ((List.mem_cons.mp hExit).resolve_left (Ne.symm hFire.not_exit))
    simp [List.getLast?_cons, hTail]
  | last _ =>
    obtain rfl := List.mem_singleton.mp hExit
    rfl

private theorem normalExitInTail {head tail : List Event} {event : Event}
    (hKind : event.kind ≠ .exit)
    (h : (head ++ event :: tail).getLast? = some ⟨9205,.exit⟩) :
    (⟨9205,.exit⟩ : Event) ∈ tail := by
  rw [List.getLast?_append, List.getLast?_cons] at h
  cases he : tail.getLast? with
  | none =>
    have hEq : event = ⟨9205,.exit⟩ := by simpa [he] using h
    exact (hKind (congrArg Event.kind hEq)).elim
  | some e => exact List.mem_of_getLast? (by simpa [he] using h : tail.getLast? = _)

/-- Reconstruct the full recurring prefix of a terminating loader lane and carry its
actual ring cursor into the drain. -/
theorem packetsToDrain {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : DrainFrontier l use s) (hw : Walk kernel Assumptions.all l g s es vs)
    (hExit : (⟨9205, .exit⟩ : Event) ∈ es) :
    ∃ final u pre tail post, es = pre ++ tail ∧ PacketsBeforeDrain l g use final pre ∧
      At u 1744 (drainCarry l final) ∧ Walk kernel Assumptions.all l g u tail post ∧
      (⟨9205, .exit⟩ : Event) ∈ tail := by
  generalize hLength : vs.length = n
  induction n using Nat.strong_induction_on generalizing use s es vs with
  | h n ih =>
    cases hs with
    | drain hs => exact ⟨use, s, [], es, vs, rfl, .done _, hs, hw, hExit⟩
    | packet site hs =>
      have hPub := exitForcesPacketPublication site hs.1 (ringShapeOfAt hs) hw hExit
      obtain ⟨retry, mid, remaining, t, suffix, hEvents, hLt, _, hMid, ht, hRun⟩ :=
        completeEmptyPacket hp site hs hw hPub
      have hEvents' : es = List.replicate retry (cursorPoll l g use site false) ++
          cursorPoll l g use site true :: mid ++ cursorArrival l g use site :: remaining :=
        hEvents
      have hLast := normalExitLast hw hExit
      rw [hEvents'] at hLast
      have hUnsupported : (cursorArrival l g use site).kind ≠ .exit := by
        intro he
        cases he
      have hRest : (⟨9205, .exit⟩ : Event) ∈ remaining :=
        normalExitInTail (head := List.replicate retry (cursorPoll l g use site false) ++
          cursorPoll l g use site true :: mid) hUnsupported (by
            simpa only [List.append_assoc, List.cons_append] using hLast)
      obtain ⟨v, gap, after, post, hSplit, hPost, hv, hWalk, hGap, hEnd⟩ :=
        packetAdvanceToDrainFrontier site ht hRun hRest
      have hSmaller : post.length < n := by
        have h := hPost.length_le
        omega
      obtain ⟨final, u, packets, tail, visits, hAll, hRunPackets, hu, hTail, hExit⟩ :=
        ih post.length hSmaller hv hWalk hEnd rfl
      refine ⟨final, u, List.replicate retry (cursorPoll l g use site false) ++
        cursorPoll l g use site true :: mid ++ cursorArrival l g use site :: (gap ++ packets),
        tail, visits, ?_, .packet hMid (.gap hGap hRunPackets), hu, hTail, hExit⟩
      simp only [hEvents', hSplit, hAll, List.append_assoc, List.cons_append]

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
