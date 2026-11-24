-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstCounterTrace
public import Kernels.TmlFa4Fwd.Proof.Thread.Softmax
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Flow.Code.Part053
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
import Kernels.TmlFa4Fwd.Flow.Code.Part055
import Kernels.TmlFa4Fwd.Flow.Code.Part068

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

private def staysBefore (cut : Nat) : Op → Bool
  | .bra dst _ => (3418 ≤ dst && dst ≤ cut)
  | .brx .. => false
  | _ => true

private theorem firstFenceControl (cut : Nat) (hc : cut = 3424 ∨ cut = 3581 ∨ cut = 4397) :
    ((kernel.code.drop 3418).take (cut - 3418)).all (fun i => staysBefore cut i.op) = true := by
  rcases hc with rfl | rfl | rfl <;> decide +kernel

private theorem beforeFirstFenceEvent :
    ((kernel.code.drop 3418).take (4397 - 3418)).all
      (fun i => i.op.isLocal || Epilogue.ordinaryEvent i.op) = true := by decide +kernel

private theorem codeInWindow {pc cut : Nat} {ins : Instr} (hLo : 3418 ≤ pc) (hHi : pc < cut)
    (hGet : kernel.code[pc]? = some ins) :
    ins ∈ (kernel.code.drop 3418).take (cut - 3418) := by
  apply List.mem_of_getElem? (i := pc - 3418)
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
  exact hGet

section
variable {l : Launch}

private theorem stepBeforeFirstFence {g cut : Nat} {s u : TState} {event : Option Event}
    (hCut : cut = 3424 ∨ cut = 3581 ∨ cut = 4397) (hLo : 3418 ≤ s.pc) (hHi : s.pc < cut)
    (he : WStep kernel Assumptions.all l g s event u) :
    3418 ≤ u.pc ∧ u.pc ≤ cut := by
  have hUpper : cut ≤ 4397 := by omega
  rcases he with ⟨rfl, ht⟩ | ⟨e, rfl, hEvent⟩
  · obtain ⟨ins, hGet, _, hExec⟩ := Softmax.tauScoreSource ht
    rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · change 3418 ≤ s.pc + 1 ∧ s.pc + 1 ≤ cut
      omega
    · rcases Softmax.scoreExecLocal hLocal with hFrame | ⟨seg,hSite,hMatch,hSeg⟩
      · have hPc := hFrame.pc
        have hOp := List.all_eq_true.mp (firstFenceControl cut hCut) ins (codeInWindow hLo hHi hGet)
        cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc
        case bra dst uni => simpa only [staysBefore, hop, Bool.and_eq_true, decide_eq_true_eq,
            hPc] using hOp
        case brx => simp [hop, staysBefore] at hOp
        all_goals omega
      · have hAudit : Assumptions.swExp2Sites.all (fun pc =>
            if 3418 ≤ pc ∧ pc < cut then
              match cuteExp2.matchAt kernel pc with
              | none => false
              | some seg => decide (3418 ≤ seg.stop ∧ seg.stop ≤ cut)
            else true) = true := by rcases hCut with rfl | rfl | rfl <;> decide +kernel
        have hStop := List.all_eq_true.mp hAudit s.pc hSite
        rw [ite_eq_left ⟨hLo,hHi⟩, hMatch, decide_eq_true_eq] at hStop
        rw [(Softmax.scoreSegmentFrame hSeg).1]
        exact hStop
  · obtain ⟨ins, hGet, hNonlocal, hFire⟩ := estep_event_source hEvent
    have hOp := List.all_eq_true.mp beforeFirstFenceEvent ins
      (codeInWindow hLo (by omega : s.pc < 4397) hGet)
    have hFrame := Epilogue.ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g) (s := s)
      (by simpa only [hNonlocal, Bool.false_or] using hOp)
    rcases callbackFrame_fires hFrame hFire with hNext | hSame <;> omega

private theorem cutBeforeFirstFence {g cut : Nat} {s : TState} {events : List Event}
    {visits : List Visit} {target : Event} (hCut : cut = 3424 ∨ cut = 3581 ∨ cut = 4397)
    (hLo : 3418 ≤ s.pc) (hHi : s.pc ≤ cut) (hTarget : cut < target.pc)
    (hw : Walk kernel Assumptions.all l g s events visits) (hFound : target ∈ events) :
    ∃ u before rest tail, events = before ++ rest ∧ target ∈ rest ∧ u.pc = cut ∧
      Walk kernel Assumptions.all l g u rest tail := by
  obtain ⟨u, before, rest, tail, hEs, hRest, _, hPc, _, hWalk⟩ :=
    hw.cut_marked (P := fun t => 3418 ≤ t.pc ∧ t.pc ≤ cut) (cut := fun t => t.pc = cut)
      (fun _ => 0) (fun _ => false) (by intros; rfl)
      (fun {t u event} ht hn he =>
        ⟨stepBeforeFirstFence hCut ht.1 (lt_of_le_of_ne ht.2 hn) he, by cases event <;> rfl⟩)
      ⟨hLo, hHi⟩ hFound (fun t ht _ h => by have := ht.2; omega)
  exact ⟨u, before, rest, tail, hEs, hRest, hPc, hWalk⟩

private theorem firstFenceEvent {g : Nat} {s u : TState} {e : Event} (hp : s.pc = 3581)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    e = ⟨3581, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  obtain ⟨ins, hCode, _, hFire⟩ := estep_event_source he
  rw [hp, Flow.code_3581] at hCode
  obtain rfl := Option.some.inj hCode
  rw [← hp]
  exact hFire.1

/-- The first bias proxy fence is an actual event in the same suffix before a later event
in that round. The checked branch interval also covers unsuccessful polls. -/
theorem firstBiasFenceBeforeNotice {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} {notice : Event} (hLo : 3418 ≤ s.pc) (hHi : s.pc ≤ 3581)
    (hNotice : 3581 < notice.pc) (hw : Walk kernel Assumptions.all l g s events visits)
    (hFound : notice ∈ events) :
    ∃ before after, events = before ++
      ⟨3581, .fenceProxy (.async (some (.shared .cta))) none⟩ :: after ∧ notice ∈ after := by
  obtain ⟨u, before, rest, tail, hEs, hRest, hPc, hWalk⟩ :=
    cutBeforeFirstFence (.inr (.inl rfl)) hLo hHi hNotice hw hFound
  have hCode : kernel.code[u.pc]? = _ := hPc.symm ▸ Flow.code_3581
  have hNe : ∀ e, e.pc = u.pc → e ≠ notice := by
    rintro e h rfl
    omega
  cases hWalk with
  | stop => simp at hRest
  | tau ht _ =>
    obtain ⟨ins, hGet, _, hExec⟩ := Softmax.tauScoreSource ht
    obtain rfl := Option.some.inj (hGet.symm.trans hCode)
    rcases hExec with ⟨_, hSkip⟩ | ⟨_, hLocal, _⟩
    · cases hSkip
    · cases hLocal
  | last h =>
    obtain rfl := List.mem_singleton.mp hRest
    exact (hNe _ (estep_source_pc h) rfl).elim
  | ev he hw =>
    have hRest' := List.mem_cons.mp hRest
    refine ⟨before, _, ?_, hRest'.resolve_left (fun hr => hNe _ (estep_source_pc he) hr.symm)⟩
    rwa [firstFenceEvent hPc he] at hEs

private theorem firstScorePollReturn {g : Nat} {s u : TState} {e : Event} (hp : s.pc = 3425)
    (hReg : s.regs 2770 = some (b32 0)) (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ m ok, s.fault = none ∧ e = ⟨3425, .wait m 0 ok true .cta⟩ ∧
      u = next (setReg s 9751 (.pred ok)) := by
  have hFault : s.fault = none := by
    obtain ⟨m, ho, hf⟩ := he
    cases h : s.fault with
    | none => rfl
    | some bad =>
      simp only [out, h, Out.ev.injEq] at ho
      subst m
      cases hf.2
  obtain ⟨ins, hCode, _, hFire⟩ := estep_event_source he
  rw [hp, Flow.code_3425] at hCode
  obtain rfl := Option.some.inj hCode
  have hBits := readBits_b32 (L := l) (g := g) hReg (by decide : 0 < 2 ^ 32)
  have hScope : (Assumptions.all.any (·.clusterScopeMbar s.pc)) = false := by rw [hp]; rfl
  change Fires s.pc (eventTmpl Assumptions.all l g s
    (.mbarWait 9751 2769 0 (.reg 2770) true .cta)) e (some u) at hFire
  cases hLoc : mbarLoc l g s 2769 0 with
  | error f =>
    simp [eventTmpl, tmaTmpl, hLoc, hScope, widenMbarScope, bind, Except.bind, ofExec] at hFire
    cases hFire.2
  | ok obj =>
    simp only [eventTmpl, tmaTmpl, hLoc, hBits, hScope, widenMbarScope, bind, Except.bind,
      pure, Except.pure, ofExec, Bool.false_eq_true, ↓reduceIte] at hFire
    obtain ⟨ok, hE, hU⟩ := hFire
    exact ⟨obj, ok, hFault, by simpa [hp] using hE, Option.some.inj hU⟩

private theorem firstPollRetry {g : Nat} {s : TState} (hp : s.pc = 3425) (hf : s.fault = none) :
    let u := next (setReg s 9751 (.pred false))
    let v := skip u
    Tau kernel Assumptions.all l g u v ∧
      Tau kernel Assumptions.all l g v {v with pc := 3425} := by
  dsimp only
  constructor
  · unfold Tau out
    simp [next, setReg, hp, hf, Flow.code_3426, guardHolds, readReg, bind, Except.bind, pure,
      Except.pure]
  · let v := skip (next (setReg s 9751 (.pred false)))
    change Tau kernel Assumptions.all l g v {v with pc := 3425}
    have hv : v.pc = 3427 := by simp [v, skip, next, setReg, hp]
    have hFault : v.fault = none := by simpa [v, skip, next, setReg] using hf
    have hc : kernel.code[v.pc]? = _ := hv.symm ▸ Flow.code_3427
    have hOff : v.pc ∉ Assumptions.swExp2Sites := by rw [hv]; decide
    apply tauStep_iff.mp
    rw [Assumptions.tauStep_all_eq_nil hOff hc rfl]
    simp [tauStep, out, hc, hFault, guardHolds, Op.isLocal, execLocalA,
      execLocalRule, execLocal, Op.rule, execBranch, pure, Except.pure]

private theorem scoreWaitBeforeLaterEvent {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} {target : Event} (hp : s.pc = 3425) (hReg : s.regs 2770 = some (b32 0))
    (hLater : 3425 < target.pc) (hw : Walk kernel Assumptions.all l g s events visits)
    (hFound : target ∈ events) :
    ∃ before after m u tail,
      events = before ++ ⟨3425, .wait m 0 true true .cta⟩ :: after ∧
      target ∈ after ∧ u.pc = 3426 ∧ Walk kernel Assumptions.all l g u after tail := by
  induction events generalizing s visits with
  | nil => simp at hFound
  | cons first rest ih =>
    cases hw with
    | tau ht _ =>
      obtain ⟨ins, hGet, _, hExec⟩ := Softmax.tauScoreSource ht
      rw [hp, Flow.code_3425] at hGet
      obtain rfl := Option.some.inj hGet
      rcases hExec with ⟨_, hSkip⟩ | ⟨_, hLocal, _⟩
      · cases hSkip
      · cases hLocal
    | last he =>
      obtain rfl := List.mem_singleton.mp hFound
      have := estep_source_pc he
      omega
    | ev he hw =>
      have hRest : target ∈ rest := (List.mem_cons.mp hFound).resolve_left (fun h => by
        rw [h, estep_source_pc he, hp] at hLater
        omega)
      obtain ⟨m, ok, hf, rfl, rfl⟩ := firstScorePollReturn hp hReg he
      cases ok
      · obtain ⟨hFirst, hSecond⟩ := firstPollRetry (l := l) (g := g) hp hf
        cases hw with
        | stop => simp at hRest
        | tau ht hw' =>
          obtain rfl := Out.tau.inj (hFirst.symm.trans ht)
          cases hw' with
          | stop => simp at hRest
          | tau ht hw'' =>
            obtain rfl := Out.tau.inj (hSecond.symm.trans ht)
            let retry := {(skip (next (setReg s 9751 (.pred false)))) with pc := 3425}
            have hKept : retry.regs 2770 = some (b32 0) := by
              simpa [retry, skip, next, setReg] using hReg
            obtain ⟨before, after, loc, u, tail, hEs, hAfter, hU, hWalk⟩ :=
              ih rfl hKept hw'' hRest
            exact ⟨_ :: before, after, loc, u, tail,
              by rw [List.cons_append, hEs], hAfter, hU, hWalk⟩
          | ev he _ => exact (by obtain ⟨m, hOut, _⟩ := he; rw [hSecond] at hOut; cases hOut)
          | last he => exact (by obtain ⟨m, hOut, _⟩ := he; rw [hSecond] at hOut; cases hOut)
        | ev he _ => exact (by obtain ⟨m, hOut, _⟩ := he; rw [hFirst] at hOut; cases hOut)
        | last he => exact (by obtain ⟨m, hOut, _⟩ := he; rw [hFirst] at hOut; cases hOut)
      · exact ⟨[], rest, m, _, _, rfl, hRest, by simp [next, setReg, hp], hw⟩

private theorem firstScorePhaseInit {g : Nat} {s u : TState} (hp : s.pc = 3424)
    (ht : Tau kernel Assumptions.all l g s u) :
    u.pc = 3425 ∧ u.regs 2770 = some (b32 0) := by
  obtain ⟨_, _, hf, _⟩ := Softmax.tauScoreSource ht
  have hc : kernel.code[s.pc]? = _ := hp.symm ▸ Flow.code_3424
  have hNone : s.pc ∉ Assumptions.swExp2Sites := by rw [hp]; decide
  have hTau := tauStep_iff.mpr ht
  rw [Assumptions.tauStep_all_eq_nil hNone hc rfl] at hTau
  have hNext : tauStep kernel [] l g s = some (next (setReg s 2770 (b32 0))) := by
    simp only [tauStep, out, hf, hc]
    rfl
  obtain rfl := Option.some.inj (hTau.symm.trans hNext)
  simp [hp, next, setReg]

private theorem scoreWaitAfterPhaseInit {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} {target : Event} (hp : s.pc = 3424) (hLater : 3425 < target.pc)
    (hw : Walk kernel Assumptions.all l g s events visits) (hFound : target ∈ events) :
    ∃ before after m u tail,
      events = before ++ ⟨3425, .wait m 0 true true .cta⟩ :: after ∧
      target ∈ after ∧ u.pc = 3426 ∧ Walk kernel Assumptions.all l g u after tail := by
  cases hw with
  | stop => simp at hFound
  | tau ht hw =>
    obtain ⟨hPc, hReg⟩ := firstScorePhaseInit hp ht
    exact scoreWaitBeforeLaterEvent hPc hReg hLater hw hFound
  | ev he _ =>
    exact (Softmax.noLocalEvent (hp.symm ▸ Flow.code_3424) rfl he).elim
  | last he =>
    obtain rfl := List.mem_singleton.mp hFound
    have := estep_source_pc he
    omega

/-- Before a later first-round event, the actual suffix contains a successful score
poll and then the actual bias proxy fence. Both are extracted from the same walk. -/
theorem firstScoreFenceTrace {g : Nat} {s : TState} {events : List Event} {visits : List Visit}
    {notice : Event} (hPc : s.pc = 3418) (hNotice : 3581 < notice.pc)
    (hw : Walk kernel Assumptions.all l g s events visits) (hFound : notice ∈ events) :
    ∃ before gap suffix m,
      events = before ++ ⟨3425, .wait m 0 true true .cta⟩ ::
        (gap ++ ⟨3581, .fenceProxy (.async (some (.shared .cta))) none⟩ :: suffix) ∧
      notice ∈ suffix := by
  obtain ⟨u, pre, rest, tail, hEs, hRest, hU, hWalk⟩ :=
    cutBeforeFirstFence (.inl rfl) hPc.ge (by omega) (by omega) hw hFound
  obtain ⟨pre', after, m, v, tail', hPoll, hAfter, hV, hWalk'⟩ :=
    scoreWaitAfterPhaseInit hU (by omega) hWalk hRest
  obtain ⟨gap, suffix, hFence, hSuffix⟩ :=
    firstBiasFenceBeforeNotice (by omega) (by omega) hNotice hWalk' hAfter
  exact ⟨pre ++ pre', gap, suffix, m,
    by rw [hEs, hPoll, hFence, List.append_assoc], hSuffix⟩

private theorem firstNoticeFromMark {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} (hw : Walk kernel Assumptions.all l g s events visits)
    (hExit : (⟨9205, .exit⟩ : Event) ∈ events) {e : Event} (hIn : e ∈ events) (hPc : e.pc = 4397) :
    Scores.notice e = some .first := by
  induction hw with
  | stop => cases hIn
  | tau _ _ ih => exact ih hExit hIn
  | ev he _ ih =>
    rcases List.mem_cons.mp hIn with rfl | hLater
    · obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
      rw [← estep_source_pc he, hPc, Flow.code_4397] at hc
      obtain rfl := Option.some.inj hc
      simp only [eventTmpl] at hf
      unfold barTmpl at hf
      repeat' split at hf
      all_goals solve
        | simp [Scores.notice, Scores.noticeRound, hPc, congrArg Event.kind hf.1]
        | cases hf.2
    · exact ih ((List.mem_cons.mp hExit).resolve_left (by
        intro h
        obtain ⟨_, _, hf⟩ := he
        rw [← h] at hf
        cases fires_end_none hf (.inr rfl))) hLater
  | last _ =>
    obtain rfl := List.mem_singleton.mp hIn
    obtain rfl := List.mem_singleton.mp hExit
    cases hPc

private theorem firstScoreStatisticsFromNotice {X : Execution} {g start : Nat} {state : TState}
    {visits : List Visit} {e : Event} (hState : state.pc = 3418)
    (hw : Walk kernel Assumptions.all l g state ((X.tr g).drop (start+3)) visits)
    (hIn' : e ∈ (X.tr g).drop (start+3)) (hLate : 3581 < e.pc)
    (hNotice : Scores.notice e = some .first) :
    ∃ wait fence notice obj,
      X.get (g,wait) = some ⟨3425,.wait obj 0 true true .cta⟩ ∧
      X.get (g,fence) = some ⟨3581,.fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      Scores.Publishes X (g,notice) .first ∧ wait < fence ∧ fence < notice := by
  obtain ⟨before, gap, after, obj, hSplit, hAfter⟩ :=
    firstScoreFenceTrace hState hLate hw hIn'
  obtain ⟨index, hGet⟩ := List.mem_iff_getElem?.mp hAfter
  let wait := start + 3 + before.length
  let fence := wait + 1 + gap.length
  let notice := fence + 1 + index
  have hWait : X.get (g, wait) = some ⟨3425, .wait obj 0 true true .cta⟩ := by
    change (X.tr g)[start + 3 + before.length]? = _
    rw [← List.getElem?_drop, hSplit, List.getElem?_append_right le_rfl]
    simp
  have hFence : X.get (g, fence) =
      some ⟨3581, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
    change (X.tr g)[(start + 3 + before.length) + 1 + gap.length]? = _
    rw [Nat.add_assoc (start + 3) before.length 1,
      Nat.add_assoc (start + 3) (before.length + 1) gap.length]
    rw [← List.getElem?_drop, hSplit, List.getElem?_append_right (by omega)]
    rw [show before.length + 1 + gap.length - before.length = gap.length + 1 by omega]
    rw [List.getElem?_cons_succ, List.getElem?_append_right le_rfl]
    simp
  have hPublish : X.get (g, notice) = some e := by
    change (X.tr g)[(start + 3 + before.length) + 1 + gap.length + 1 + index]? = _
    rw [Nat.add_assoc (start + 3) before.length 1,
      Nat.add_assoc (start + 3) (before.length + 1) gap.length,
      Nat.add_assoc (start + 3) (before.length + 1 + gap.length) 1,
      Nat.add_assoc (start + 3) (before.length + 1 + gap.length + 1) index]
    rw [← List.getElem?_drop, hSplit, List.getElem?_append_right (by omega)]
    rw [show before.length + 1 + gap.length + 1 + index - before.length =
      gap.length + 1 + (index + 1) by omega]
    rw [show gap.length + 1 + (index + 1) = (gap.length + (index + 1)) + 1 by omega]
    simp only [List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by omega)]
    simpa using hGet
  exact ⟨wait, fence, notice, obj, hWait, hFence, ⟨e, hPublish, hNotice⟩,
    by dsimp [fence]; omega, by dsimp [notice]; omega⟩
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A later actual numerical event has the first statistics notice in its trace prefix. -/
theorem firstStatisticsOfLaterBodyEvent {g position : Nat} (hWarp : Prologue.warpIndex l g < 8)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads) (hCuQ : Epilogue.DrainCuQProtected p X)
    (hUsedK : UsedKProtected p X) {e : Event} (he : X.get (g,position) = some e) (hPc : 4397 < e.pc)
    :
    ∃ first < position, Scores.Publishes X (g,first) .first := by
  let lane := laneOf l g
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel
    ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨_,_,_,_,start,state,_,_,hState,hRun,hBefore,hSuffix⟩ :=
    Softmax.activeGeometryOfEventPastReads hp hX hg hWarp hl hWork hCuQ hUsedK
      (hLane.symm ▸ he) (by omega)
  rw [hLane] at hRun hSuffix
  obtain ⟨_,hw⟩ := Mma.walkFromRun hRun
  obtain ⟨s, pre, after, _, hTrace, hAfter, hAt, hw'⟩ :=
    cutBeforeFirstFence (.inr (.inr rfl)) hState.1.ge (by rw [hState.1]; decide) hPc hw hSuffix
  have hCut : ∃ bar rest, after = bar::rest ∧ bar.pc = 4397 ∧
      Scores.notice bar = some .first := by
    cases hw' with
    | stop => cases hAfter
    | tau ht _ =>
      obtain ⟨ins,hGet,_,hExec⟩ := Softmax.tauScoreSource ht
      rw [hAt,Flow.code_4397] at hGet
      obtain rfl := Option.some.inj hGet
      rcases hExec with ⟨_,hSkip⟩ | ⟨_,hLocal,_⟩
      · cases hSkip
      · cases hLocal
    | last hLast =>
      obtain rfl := List.mem_singleton.mp hAfter
      have hEq := estep_source_pc hLast
      omega
    | ev hStep _ =>
      obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source hStep
      rw [hAt,Flow.code_4397] at hCode
      obtain rfl := Option.some.inj hCode
      refine ⟨_,_,rfl,(estep_source_pc hStep).trans hAt,?_⟩
      simp only [eventTmpl] at hFire
      unfold barTmpl at hFire
      repeat' split at hFire
      all_goals solve
        | simp [Scores.notice, Scores.noticeRound, (estep_source_pc hStep).trans hAt,
            congrArg Event.kind hFire.1]
        | cases hFire.2
  obtain ⟨bar,tail,hBars,hBarPc,hMark⟩ := hCut
  let first := start+3+pre.length
  have hGet : X.get (g,first) = some bar := by
    change (X.tr g)[start+3+pre.length]? = _
    rw [← List.getElem?_drop,hTrace,hBars,List.getElem?_append_right le_rfl]
    simp
  have hOrder := traceOrderOfPcFloor hX (floor := 4398)
    (by decide +kernel) (by decide +kernel) hGet he (by omega) (by omega)
  exact ⟨first,hOrder,bar,hGet,hMark⟩


/-- A later recorded statistics notification has the actual first one in its trace prefix. -/
theorem firstStatisticsOfLaterPublication {g position : Nat} (hWarp : Prologue.warpIndex l g < 8)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads) (hCuQ : Epilogue.DrainCuQProtected p X)
    (hUsedK : UsedKProtected p X) {round : Scores.Round} (hRound : round ≠ .first)
    (hPub : Scores.Publishes X (g,position) round) :
    ∃ first < position, Scores.Publishes X (g,first) .first := by
  obtain ⟨e, he, hNotice⟩ := hPub
  have hPc : 4397 < e.pc := by
    obtain ⟨site,kind⟩ := e
    cases kind <;> simp [Scores.notice] at hNotice
    rename_i id count mode
    cases mode <;> simp at hNotice
    unfold Scores.noticeRound at hNotice
    split at hNotice <;> simp_all
  exact firstStatisticsOfLaterBodyEvent hp hX hWarp hWork hCuQ hUsedK he hPc

/-- A recorded opening statistics publication already has its initial score acquire and
Bias proxy fence in the same lane, including when the prefix is incomplete. -/
theorem firstScoreStatisticsOfPublication {g position : Nat} (hWarp : Prologue.warpIndex l g < 8)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads) (hCuQ : Epilogue.DrainCuQProtected p X)
    (hUsedK : UsedKProtected p X) (hPub : Scores.Publishes X (g,position) .first) :
    ∃ wait fence notice obj,
      X.get (g,wait) = some ⟨3425,.wait obj 0 true true .cta⟩ ∧
      X.get (g,fence) = some ⟨3581,.fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      Scores.Publishes X (g,notice) .first ∧ wait < fence ∧ fence < notice := by
  obtain ⟨e,he,hNotice⟩ := hPub
  have hPc : e.pc = 4397 := by
    obtain ⟨site,kind⟩ := e
    cases kind <;> simp [Scores.notice] at hNotice
    rename_i id count mode
    cases mode <;> simp at hNotice
    unfold Scores.noticeRound at hNotice
    split at hNotice <;> simp_all
  let lane := laneOf l g
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel
    ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨_,_,_,_,start,state,_,_,hState,hRun,_,hSuffix⟩ :=
    Softmax.activeGeometryOfEventPastReads hp hX hg hWarp hl hWork hCuQ hUsedK
      (hLane.symm ▸ he) (by omega)
  rw [hLane] at hRun hSuffix
  obtain ⟨_,hw⟩ := Mma.walkFromRun hRun
  exact firstScoreStatisticsFromNotice hState.1 hw hSuffix (by omega) hNotice

/-- An exited active softmax lane supplies the successful first score wait, bias proxy
fence and first statistics arrival, in that order in its actual execution. -/
theorem firstScoreStatisticsOfExit {g exit : Nat} (hWarp : Prologue.warpIndex l g < 8)
    (hWork : g / l.block < tilePrefix p p.batch * p.heads) (hCuQ : Epilogue.DrainCuQProtected p X)
    (hUsedK : UsedKProtected p X) (he : X.get (g, exit) = some ⟨9205, .exit⟩) :
    ∃ wait fence notice obj,
      X.get (g, wait) = some ⟨3425, .wait obj 0 true true .cta⟩ ∧
      X.get (g, fence) = some ⟨3581, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      Scores.Publishes X (g, notice) .first ∧ wait < fence ∧ fence < notice := by
  let lane := laneOf l g
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel
    ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨batch, hb, hlo, hhi, start, state, hReads, hState, hRun⟩ :=
    Softmax.activeGeometryOfExit hp hX hg hWarp hl hWork hCuQ hUsedK (hLane.symm ▸ he)
  rw [hLane] at hRun hReads
  have hLen := Execution.exit_last hX hg he
  have hUsed := hReads.2.2
  have hBound := (List.getElem?_eq_some_iff.mp hUsed).1
  change start + 2 < (X.tr g).length at hBound
  change exit + 1 = (X.tr g).length at hLen
  have hNe : start + 2 ≠ exit := by
    intro hi
    rw [hi, he] at hUsed
    cases hUsed
  have hJ : start + 3 ≤ exit := by omega
  have hExit : (⟨9205, .exit⟩ : Event) ∈ (X.tr g).drop (start + 3) := by
    apply List.mem_of_getElem? (i := exit - (start + 3))
    rwa [List.getElem?_drop, Nat.add_sub_of_le hJ]
  obtain ⟨visits, hw⟩ := Mma.walkFromRun hRun
  have hTile := (Epilogue.assignedCoordinates_valid hp hlo hhi).1
  obtain ⟨_, pre, first, rest, _, hLists, _, hCount, _, _, _⟩ :=
    Softmax.firstGeometryCounterWalk hp (Softmax.stageOf ⟨Prologue.warpIndex l g, hWarp⟩)
      hb hTile hState hw hExit
  obtain ⟨e, hIn, hMark⟩ := List.countP_pos_iff.mp (by omega : 0 < first.countP (barrierMark 4397))
  have hPc : e.pc = 4397 := beq_iff_eq.mp hMark
  have hIn' : e ∈ (X.tr g).drop (start + 3) := by
    rw [hLists]
    exact List.mem_append_left _ (List.mem_append_right _ hIn)
  have hNotice := firstNoticeFromMark hw hExit hIn' hPc
  exact firstScoreStatisticsFromNotice hState.1 hw hIn' (by omega) hNotice

end PTX.Kernels.TmlFa4Fwd.Thread
