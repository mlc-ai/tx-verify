-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStaging
import Kernels.TmlFa4Fwd.Proof.CorrectionOutputStores
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Proof.CorrectionPollPrefix
import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixEvents
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Order.OrderWaits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Softmax
open PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

private inductive AcquireWindow
  | before | exit

private def AcquireWindow.lower : AcquireWindow → Nat
  | .before => 7745
  | .exit => 9201

private def AcquireWindow.upper : AcquireWindow → Nat
  | .before => 8472
  | .exit => 9205

private def AcquireWindow.allows (w : AcquireWindow) (pc : Nat) : Prop :=
  w.lower ≤ pc ∧ (pc ≤ w.upper ∨ pc = 9201)

private def AcquireWindow.checked (w : AcquireWindow) (op : Op) : Bool :=
  (op.isLocal || correctionReturningOp op) && !(scoreEventWrites op).contains 0 &&
    match op with
    | .bra dest _ => decide (w.lower ≤ dest ∧ (dest ≤ w.upper ∨ dest = 9201))
    | .brx .. => false
    | _ => true

private theorem checkedWindow (w : AcquireWindow) {pc : Nat} {i : Instr}
    (hLo : w.lower ≤ pc) (hHi : pc < w.upper) (hc : kernel.code[pc]? = some i) :
    w.checked i.op = true := by
  let code := (kernel.code.drop w.lower).take (w.upper - w.lower)
  have hCode : code.all (fun ins => w.checked ins.op) = true := by
    cases w <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hCode i
  apply List.mem_of_getElem? (i := pc - w.lower)
  dsimp only [code]
  rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]

private theorem acquireWindowStep (w : AcquireWindow) {l : Launch} {g : Nat} {s u : TState}
    {event : Option Event} (hLo : w.lower ≤ s.pc) (hHi : s.pc < w.upper) (hSub : s.sub ≤ 3)
    (hStep : WStep kernel Assumptions.all l g s event u) :
    w.allows u.pc ∧ u.sub ≤ 3 := by
  have hFall : w.allows (s.pc + 1) := ⟨by omega, .inl (by omega)⟩
  have hStay : w.allows s.pc := ⟨hLo, .inl hHi.le⟩
  rcases hStep with ⟨_, ht⟩ | ⟨ev, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      have hMin : 7745 ≤ w.lower := by cases w <;> decide
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, hClean, hTau⟩ := correctionTauFrame hOff ht
    rcases hTau with ⟨rfl, _⟩ | ⟨_, _, hFrame⟩
    · exact ⟨hFall, Nat.zero_le _⟩
    have hp := hFrame.pc
    have hCode := (Bool.and_eq_true_iff.mp (checkedWindow w hLo hHi hc)).2
    refine ⟨?_, hFrame.sub.symm ▸ hSub⟩
    cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hp
    case bra dest uni =>
      rw [hp]
      change w.lower ≤ dest ∧ (dest ≤ w.upper ∨ dest = 9201)
      exact of_decide_eq_true (by simpa only [ho] using hCode)
    case brx => simp [ho] at hCode
    all_goals exact hp.symm ▸ hFall
  · obtain ⟨i, hc, hNonlocal, _⟩ := estep_event_source he
    have hChecked := (Bool.and_eq_true_iff.mp (checkedWindow w hLo hHi hc)).1
    have hOp : correctionReturningOp i.op = true := by
      simpa only [hNonlocal, Bool.false_or] using (Bool.and_eq_true_iff.mp hChecked).1
    have hh : 0 ∉ scoreEventWrites i.op := by simpa using (Bool.and_eq_true_iff.mp hChecked).2
    obtain ⟨hFrame, _⟩ := correctionEventProgress hc hOp hSub hh he
    exact ⟨hFrame.pc.elim (fun h => h.1.symm ▸ hFall) (fun h => h.1.symm ▸ hStay), hFrame.sub⟩

private theorem noStagingAfterExitJump {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {target : Event}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : 9201 ≤ s.pc) (hHi : s.pc ≤ 9205) (hSub : s.sub ≤ 3)
    (hm : target ∈ events) (hEarly : target.pc < 9201) : False := by
  induction hw with
  | stop => cases hm
  | last h =>
    obtain rfl := List.mem_singleton.mp hm
    have := estep_source_pc h
    omega
  | @tau s u events visits hTau hTail ih =>
    by_cases hEq : s.pc = 9205
    · exact (by
        cases hFault : s.fault <;> simp [Tau, out, hEq, hFault, Flow.code_9205,
          guardHolds, pure, Except.pure, Op.isLocal] at hTau)
    have hUpper : s.pc < 9205 := by omega
    obtain ⟨hNext, hSmall⟩ := acquireWindowStep .exit hLo hUpper hSub (.inl ⟨rfl, hTau⟩)
    have hUpper' : u.pc ≤ 9205 := by
      have h := hNext.2
      change u.pc ≤ 9205 ∨ u.pc = 9201 at h
      omega
    exact ih hNext.1 hUpper' hSmall hm
  | @ev s u e events visits hEvent hTail ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · have := estep_source_pc hEvent
      omega
    by_cases hEq : s.pc = 9205
    · obtain ⟨m, hOut, hFire⟩ := hEvent
      cases hFault : s.fault with
      | none =>
        have hTemplate : out kernel Assumptions.all l g s = .ev .exit := by
          rw [out_event hFault (hEq.symm ▸ Flow.code_9205) rfl rfl]
          rfl
        obtain rfl := Out.ev.inj (hOut.symm.trans hTemplate)
        cases hFire.2
      | some fault =>
        simp only [out, hFault, Out.ev.injEq] at hOut
        subst m
        cases hFire.2
    have hUpper : s.pc < 9205 := by omega
    obtain ⟨hNext, hSmall⟩ := acquireWindowStep .exit hLo hUpper hSub (.inr ⟨_, rfl, hEvent⟩)
    have hUpper' : u.pc ≤ 9205 := by
      have h := hNext.2
      change u.pc ≤ 9205 ∨ u.pc = 9201 at h
      omega
    exact ih hNext.1 hUpper' hSmall hm

private theorem cutAtOutputAcquireSetup {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {target : Event}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : 7745 ≤ s.pc) (hHi : s.pc ≤ 8472) (hSub : s.sub ≤ 3)
    (hLow : 8472 < target.pc) (hHigh : target.pc < 9201) (hm : target ∈ events) :
    ∃ u before tail marks, events = before ++ tail ∧ u.pc = 8472 ∧ u.fault = none ∧
      Walk kernel Assumptions.all l g u tail marks ∧ target ∈ tail ∧
      ∀ e ∈ before, e.pc < 8472 := by
  have cleanAt {s : TState} {events : List Event} {visits : List Visit}
      (hPc : s.pc = 8472) (hWalk : Walk kernel Assumptions.all l g s events visits)
      (hm : target ∈ events) : s.fault = none := by
    cases hf : s.fault with
    | none => rfl
    | some fault =>
      cases hWalk with
      | stop => simp at hm
      | tau ht _ => simp [Tau, out, hf] at ht
      | ev h _ =>
        obtain ⟨m, hOut, hFire⟩ := h
        simp only [out, hf, Out.ev.injEq] at hOut
        subst m
        cases hFire.2
      | last h =>
        obtain rfl := List.mem_singleton.mp hm
        have := estep_source_pc h
        omega
  have hCut {s : TState} {events : List Event} {visits : List Visit}
      (hPc : s.pc = 8472) (hWalk : Walk kernel Assumptions.all l g s events visits)
      (hm : target ∈ events) : ∃ u before tail marks, events = before ++ tail ∧ u.pc = 8472 ∧
        u.fault = none ∧ Walk kernel Assumptions.all l g u tail marks ∧ target ∈ tail ∧
        ∀ e ∈ before, e.pc < 8472 :=
    ⟨s, [], events, visits, rfl, hPc, cleanAt hPc hWalk hm, hWalk, hm, by simp⟩
  induction hw with
  | stop => cases hm
  | last h =>
    obtain rfl := List.mem_singleton.mp hm
    have := estep_source_pc h
    omega
  | @tau s u events visits hTau hTail ih =>
    by_cases hPc : s.pc = 8472
    · exact hCut hPc (.tau hTau hTail) hm
    have hUpper : s.pc < 8472 := by omega
    obtain ⟨hNext, hSmall⟩ := acquireWindowStep .before hLo hUpper hSub (.inl ⟨rfl, hTau⟩)
    rcases hNext.2 with h | h
    · exact ih hNext.1 h hSmall hm
    · exact (noStagingAfterExitJump hTail (by omega) (by omega) hSmall hm hHigh).elim
  | @ev s u e events visits hEvent hTail ih =>
    by_cases hPc : s.pc = 8472
    · exact hCut hPc (.ev hEvent hTail) hm
    have hUpper : s.pc < 8472 := by omega
    have hEventPc := estep_source_pc hEvent
    have hSuffix := (List.mem_cons.mp hm).resolve_left (fun eq => by rw [eq] at hLow; omega)
    obtain ⟨hNext, hSmall⟩ := acquireWindowStep .before hLo hUpper hSub (.inr ⟨_, rfl, hEvent⟩)
    rcases hNext.2 with h | h
    · obtain ⟨v, pre, tail, post, hSplit, hv, hf, hTail, hm, hEarly⟩ := ih hNext.1 h hSmall hSuffix
      exact ⟨v, e :: pre, tail, post, by rw [hSplit, List.cons_append], hv, hf, hTail, hm,
        fun a ha => (List.mem_cons.mp ha).elim (fun h => by rw [h]; omega) (hEarly _)⟩
    · exact (noStagingAfterExitJump hTail (by omega) (by omega) hSmall hSuffix hHigh).elim

private theorem parityAfterSetup {l : Launch} {g : Nat} {s : TState}
    (hPc : s.pc = 8472) (hClean : s.fault = none) :
    run kernel Assumptions.all l g 1 s = some (next (setReg s 6496 (b32 0))) := by
  have hCode : kernel.code[s.pc]? = some ⟨none,
      .move ⟨.scalar, .int .b 32, [some 6496], [.imm 0]⟩⟩ := hPc.symm ▸ Flow.code_8472
  simp only [run, Option.bind_eq_some_iff, Option.some.injEq, exists_eq_right]
  rw [Assumptions.tauStep_all_eq_nil (by rw [hPc]; decide) hCode rfl]
  unfold tauStep
  simp only [out, hClean, hCode, guardHolds, pure, Except.pure, Op.isLocal]
  rw [execLocalA_nil, execLocal_move rfl]
  simp [execMove, readValue, readBits, DType.width, Value.bytes,
    b32, bind, Except.bind, pure, Except.pure]
  rfl

private theorem outputPollParity {l : Launch} {g : Nat} {s u : TState} {loc : Loc}
    {parity : Nat} {ok : Bool} {scope : MbarScope}
    (hPc : s.pc = 8473) (hZero : s.regs 6496 = some (b32 0))
    (he : EStep kernel Assumptions.all l g s ⟨8473, .wait loc parity ok true scope⟩ (some u)) :
    parity = 0 := by
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  rw [hPc, Flow.code_8473] at hc
  obtain rfl := Option.some.inj hc
  have hBits := readBits_b32 (L := l) (g := g) hZero (by decide : 0 < 2 ^ 32)
  have hWide : (Assumptions.all.any (·.clusterScopeMbar s.pc)) = false := rfl
  change Fires s.pc (eventTmpl Assumptions.all l g s
    (.mbarWait 9888 6495 0 (.reg 6496) true .cta)) _ _ at hf
  cases hLoc : mbarLoc l g s 6495 0 with
  | error f =>
    simp [eventTmpl, tmaTmpl, hLoc, hWide, widenMbarScope, bind, Except.bind, ofExec] at hf
    cases hf.2
  | ok m =>
    simp only [eventTmpl, tmaTmpl, hLoc, hBits, hWide, widenMbarScope, bind,
      Except.bind, pure, Except.pure, ofExec, Bool.false_eq_true, ↓reduceIte] at hf
    obtain ⟨_, hF, _⟩ := hf
    exact (Kind.wait.inj (congrArg Event.kind hF)).2.1

private theorem observedOutputPoll {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {target : Event}
    (hp : s.pc = 8473) (hf : s.fault = none) (hZero : s.regs 6496 = some (b32 0))
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hTarget : target ∈ events) (hLate : 8473 < target.pc) :
    ∃ (failed : List Event) (loc : Loc) (scope : MbarScope) (rest : List Event),
      events = failed ++ ⟨8473, .wait loc 0 true true scope⟩ :: rest ∧ target ∈ rest ∧
      ∀ e ∈ failed, e.pc = 8473 := by
  generalize hLen : visits.length = fuel
  induction fuel using Nat.strong_induction_on generalizing s events visits with
  | h fuel ih =>
    cases hw with
    | stop => cases hTarget
    | tau ht _ =>
      exact (by simp [Tau, out, hf, hp, Flow.code_8473, guardHolds, pure, Except.pure,
        Op.isLocal] at ht)
    | last he =>
      obtain rfl := List.mem_singleton.mp hTarget
      have := estep_source_pc he
      omega
    | @ev s v e events visits he hw =>
      obtain ⟨ok, rfl, _, _, loc, parity, scope, rfl⟩ := correctionWait_step 0 hp he
      rw [hp] at he hTarget ⊢
      have hParity := outputPollParity hp hZero he
      subst parity
      have hTail : target ∈ events :=
        (List.mem_cons.mp hTarget).resolve_left (fun h => by
          have hPc := congrArg Event.pc h
          change target.pc = 8473 at hPc
          omega)
      cases ok with
      | true => exact ⟨[], loc, scope, events, rfl, hTail, by simp⟩
      | false =>
        obtain ⟨u, hRun, hu, _, hClean, hRegs, _, _⟩ := correctionPollLocals
          (l := l) (g := g) 0 hp hf false
        obtain hEmpty | ⟨post, hLength, _, hWalk⟩ := Mma.advanceWalkLocals hRun hw
        · subst events
          cases hTail
        have hLess : post.length < fuel := by simp at hLen; omega
        have hR : u.regs 6496 = some (b32 0) := by
          rw [hRegs]
          simpa [next, setReg, correctionPoll] using hZero
        obtain ⟨failed, loc', scope', rest, hSplit, hm, hBefore⟩ :=
          ih post.length hLess hu hClean hR hWalk hTail rfl
        refine ⟨_ :: failed, loc', scope', rest, by rw [List.cons_append, hSplit], hm, ?_⟩
        intro e hm
        rcases List.mem_cons.mp hm with rfl | hh
        · rfl
        · exact hBefore e hh

variable {p : Params}

private theorem stagesFollowFirstOutputPoll {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e) (hLo : 8480 ≤ e.pc) (hHi : e.pc < 9201) :
    ∃ wait, FirstOutputAcquire l X (g, wait) ∧ po X (g, wait) (g, index) := by
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hHint
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  have hg : g < l.threads := event_thread_lt hX he
  have hNonzero : 0 < warpIndex l g := by omega
  obtain ⟨_, _, hIndex, _, _⟩ := nonzeroCommonPrefixOfLateEvent hp hX hg hNonzero he (by omega)
  have hLen : index < (X.tr g).length := len_of_get he
  obtain ⟨s, o, hs, hr⟩ := nonzeroRoleEntryPrefix hp hX (g := g) hg hNonzero (by omega)
  have hPc : dispatchParamPc ⟨warpIndex l g, warpIndex_lt hp g⟩ = 7745 := by
    simp only [dispatchParamPc]
    split_ifs <;> omega
  rw [hPc] at hs
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hr
  have hMem : e ∈ (X.tr g).drop 5 := by
    apply List.mem_of_getElem? (i := index - 5)
    rwa [List.getElem?_drop, Nat.add_sub_of_le hIndex]
  obtain ⟨u, before, tail, visits, hSplit, hu, hClean, hTail, hm, hBefore⟩ :=
    cutAtOutputAcquireSetup hWalk hs.1.ge (by rw [hs.1]; decide) (by rw [hs.2.1]; decide)
      (by omega) hHi hMem
  obtain hEmpty | ⟨_, _, _, hPoll⟩ := Mma.advanceWalkLocals (parityAfterSetup hu hClean) hTail
  · rw [hEmpty] at hm
    cases hm
  have hNext : (next (setReg u 6496 (b32 0))).pc = 8473 := by simp [next, setReg, hu]
  have hf : (next (setReg u 6496 (b32 0))).fault = none := hClean
  have hReg : (next (setReg u 6496 (b32 0))).regs 6496 = some (b32 0) := by simp [next, setReg]
  obtain ⟨failed, loc, scope, rest, hTrace, hRest, hFailed⟩ :=
    observedOutputPoll hNext hf hReg hPoll hm (by omega)
  let prev := before ++ failed
  let wait := 5 + prev.length
  let poll : Event := ⟨8473, .wait loc 0 true true scope⟩
  have hFull : (X.tr g).drop 5 = prev ++ poll :: rest := by
    rw [hSplit, hTrace]
    simp [prev, poll, List.append_assoc]
  have hWait : X.get (g, wait) = some poll := by
    unfold Execution.get
    rw [show wait = 5 + prev.length from rfl, ← List.getElem?_drop, hFull,
      List.getElem?_append_right (by rfl)]
    simp
  have hLt : wait < index := by
    have hGet : ((X.tr g).drop 5)[index - 5]? = some e := by
      rwa [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    rw [hFull] at hGet
    by_contra! hEq
    rcases Nat.eq_or_lt_of_le hEq with hEq | hLt
    · rw [hEq, hWait] at he
      have h := congrArg Event.pc (Option.some.inj he)
      change 8473 = e.pc at h
      omega
    · rw [List.getElem?_append_left (by dsimp [wait] at hLt; omega)] at hGet
      rcases List.mem_append.mp (List.mem_of_getElem? hGet : e ∈ prev) with h | h
      · have := hBefore e h
        omega
      · have := hFailed e h
        omega
  have hObject := firstCorrectionWaitAddress hp hX hWait
  exact ⟨wait, ⟨poll, scope, hWait, by rw [← hObject]⟩,
    po_of_source_not_access rfl hLt hLen (by rw [hWait]; rfl)⟩

/-- An actual ordinary staging store of the first output stage. -/
@[no_expose] def StageZeroStagingWrites (X : Execution) (writer : EvId) (a : Acc)
    (bytes : List Byte) : Prop :=
  ∃ (subbox : Fin 4) (chunk : Fin 8),
    X.get writer = some ⟨outputStorePc 0 subbox chunk, .wr a bytes⟩

/-- The decoded stage-zero store denotes a staging occurrence. -/
theorem StageZeroStagingWrites.of_event {X : Execution} {writer : EvId} {a : Acc}
    {bytes : List Byte} (subbox : Fin 4) (chunk : Fin 8)
    (h : X.get writer = some ⟨outputStorePc 0 subbox chunk, .wr a bytes⟩) :
    StageZeroStagingWrites X writer a bytes := ⟨subbox, chunk, h⟩

/-- Every actual stage-zero correction element store follows its lane's first O0 acquire.
This also applies when the CTA or its peer warps are still suspended. -/
theorem StageZeroStagingWrites.firstAcquire {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {writer : EvId} {a : Acc} {bytes : List Byte}
    (h : StageZeroStagingWrites X writer a bytes) :
    ∃ wait, FirstOutputAcquire l X wait ∧ po X wait writer := by
  obtain ⟨g, index⟩ := writer
  obtain ⟨subbox, chunk, he⟩ := h
  have hBounds : 8492 ≤ outputStorePc 0 subbox chunk ∧ outputStorePc 0 subbox chunk < 9201 := by
    fin_cases subbox <;> fin_cases chunk <;> decide
  obtain ⟨wait, hAcquire, hBefore⟩ := stagesFollowFirstOutputPoll hp hX he
    ((show 8480 ≤ 8492 by decide).trans hBounds.1) hBounds.2
  exact ⟨(g, wait), hAcquire, hBefore⟩

/-- The identified staging occurrence is the recorded ordinary write. -/
theorem StageZeroStagingWrites.writes {X : Execution} {writer : EvId} {a : Acc} {bytes : List Byte}
    (h : StageZeroStagingWrites X writer a bytes) : X.Writes writer a bytes := by
  obtain ⟨_, _, he⟩ := h
  exact ⟨_, he⟩

/-- A finalization load follows the lane's successful O0 acquire. -/
theorem firstAcquireBeforeFinalizationLoad {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {i : EvId} {chunk : Fin 16}
    {address : Nat} {values : List Value} {shape : TcShape}
    (he : X.get i = some ⟨finalizeLoadPc stage chunk, .tc (.ld address values shape)⟩) :
    ∃ wait, FirstOutputAcquire l X wait ∧ po X wait i := by
  obtain ⟨g, index⟩ := i
  obtain ⟨wait, hAcquire, hBefore⟩ := stagesFollowFirstOutputPoll hp hX he
    ((by decide : ∀ (s : Fin 2) (c : Fin 16), 8480 ≤ finalizeLoadPc s c) stage chunk)
    ((by decide : ∀ (s : Fin 2) (c : Fin 16), finalizeLoadPc s c < 9201) stage chunk)
  exact ⟨(g, wait), hAcquire, hBefore⟩

/-- A terminal joint probability credit follows the successful MMA output acquire. -/
theorem firstOutputAcquireBeforeTerminalCredit {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {e : Event}
    (he : X.get (g,index) = some e) (hSite : e.pc = 8759) :
    ∃ wait, FirstOutputAcquire l X (g,wait) ∧ po X (g,wait) (g,index) := by
  exact stagesFollowFirstOutputPoll hp hX he (by omega) (by omega)

end
/-- The second stage's final load follows both successful output acquires. -/
theorem firstAcquireBeforeSecondFinalizationLoad
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {chunk : Fin 16} {address : Nat} {values : List Value}
    {shape : TcShape} (he : X.get i =
      some ⟨finalizeLoadPc 1 chunk, .tc (.ld address values shape)⟩) :
    ∃ wait, FirstOutputAcquire l X wait ∧ po X wait i :=
  firstAcquireBeforeFinalizationLoad hp hX 1 he

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
