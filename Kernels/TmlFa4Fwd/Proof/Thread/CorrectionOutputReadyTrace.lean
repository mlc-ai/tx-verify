-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Correction
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingSetup
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStaging
import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.ProxyFenceAudit
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasRendezvous
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Lemmas.Flow.EventCont
import Lemmas.Flow.Next

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Softmax
open PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

private def lastStagingPc (stage : Fin 2) : Nat := outputFencePc stage - 1

private def readyEndPc (stage : Fin 2) : Nat := outputFencePc stage + 2

private def readyTraceCode (stage : Fin 2) (pc : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || correctionReturningOp i.op) && !(scoreEventWrites i.op).contains 0 &&
  (match i.op with
  | .bra dest _ => 7745 ≤ dest && dest ≤ 9205 &&
      (if pc < lastStagingPc stage then dest ≤ lastStagingPc stage || 9201 ≤ dest
       else readyEndPc stage < pc && readyEndPc stage < dest && (pc < 9201 || 9201 ≤ dest))
  | .brx .. => false
  | _ => true)

private theorem readyTraceCodeAt (stage : Fin 2) {pc : Nat} {i : Instr}
    (hLo : 7745 ≤ pc) (hHi : pc < 9205) (hc : kernel.code[pc]? = some i) :
    readyTraceCode stage pc i = true := by
  let code := ((kernel.code.drop 7745).take (9205 - 7745)).zipIdx 7745
  have hAll : code.all (fun (i, pc) => readyTraceCode stage pc i) = true := by
    fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, pc)
  apply List.mem_of_getElem? (i := pc - 7745)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private def ReadyMotion (stage : Fin 2) (s u : TState) : Prop :=
  u.pc = s.pc ∨ u.pc = s.pc + 1 ∨
    s.pc < lastStagingPc stage ∧ (u.pc ≤ lastStagingPc stage ∨ 9201 ≤ u.pc) ∨
    readyEndPc stage < s.pc ∧ readyEndPc stage < u.pc ∧ (s.pc < 9201 ∨ 9201 ≤ u.pc)

private theorem readyTraceStep (stage : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (hLo : 7745 ≤ s.pc) (hHi : s.pc < 9205) (hSub : s.sub ≤ 3)
    (h : WStep kernel Assumptions.all l g s ev u) :
    7745 ≤ u.pc ∧ u.pc ≤ 9205 ∧ u.sub ≤ 3 ∧ ReadyMotion stage s u := by
  rcases h with ⟨_, ht⟩ | ⟨_, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, _, hTau⟩ := correctionTauFrame hOff ht
    rcases hTau with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · exact ⟨by change 7745 ≤ s.pc + 1; omega, by change s.pc + 1 ≤ 9205; omega,
        Nat.zero_le _, .inr (.inl rfl)⟩
    have hPc := hLocal.pc
    have hChecked := (Bool.and_eq_true_iff.mp (readyTraceCodeAt stage hLo hHi hc)).2
    have hFall (hPc : u.pc = s.pc + 1) :
        7745 ≤ u.pc ∧ u.pc ≤ 9205 ∧ u.sub ≤ 3 ∧ ReadyMotion stage s u :=
      ⟨by omega, by omega, hLocal.sub.symm ▸ hSub, .inr (.inl hPc)⟩
    cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
    case brx => simp [ho] at hChecked
    case bra dest uni =>
      simp only [ho, Bool.and_eq_true, decide_eq_true_eq] at hChecked
      refine ⟨hPc.symm ▸ hChecked.1.1, hPc.symm ▸ hChecked.1.2,
        hLocal.sub.symm ▸ hSub, .inr (.inr ?_)⟩
      by_cases hs : s.pc < lastStagingPc stage
      · exact .inl ⟨hs, by simpa [hPc, hs] using hChecked.2⟩
      · exact .inr (by simpa [hPc, hs, and_assoc] using hChecked.2)
    all_goals exact hFall hPc
  · obtain ⟨i, hc, hNl, _⟩ := estep_event_source he
    have hCode := (Bool.and_eq_true_iff.mp (readyTraceCodeAt stage hLo hHi hc)).1
    simp only [Bool.and_eq_true, hNl, Bool.false_or, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hCode
    have hProg := (correctionEventProgress hc hCode.1 hSub hCode.2 he).1
    rcases hProg.pc with hp | hp
    · exact ⟨by omega, by omega, hProg.sub, .inr (.inl hp.1)⟩
    · exact ⟨by omega, by omega, hProg.sub, .inl hp.1⟩

private def stationPc (stage : Fin 2) (stop : Fin 3) : Nat :=
  if stop = 0 then lastStagingPc stage else if stop = 1 then outputFencePc stage
  else readyEndPc stage

private theorem stationBounds (stage : Fin 2) (stop : Fin 3) :
    7745 < lastStagingPc stage ∧ lastStagingPc stage ≤ stationPc stage stop ∧
      stationPc stage stop ≤ readyEndPc stage ∧ readyEndPc stage < 9201 := by
  fin_cases stage <;> fin_cases stop <;> decide

private theorem stationCode (stage : Fin 2) (stop : Fin 3) :
    ∃ i, kernel.code[stationPc stage stop]? = some i ∧ i.guard = none ∧
      i.op.isLocal = false := by
  fin_cases stage <;> fin_cases stop
  · exact ⟨_, Flow.code_8757, rfl, rfl⟩
  · exact ⟨_, Flow.code_8758, rfl, rfl⟩
  · exact ⟨_, Flow.code_8760, rfl, rfl⟩
  · exact ⟨_, Flow.code_9053, rfl, rfl⟩
  · exact ⟨_, Flow.code_9054, rfl, rfl⟩
  · exact ⟨_, Flow.code_9056, rfl, rfl⟩

private theorem stationNotLocal {l : Launch} {g : Nat} {s u : TState}
    {stage : Fin 2} {stop : Fin 3} (hs : s.pc = stationPc stage stop)
    (ht : Tau kernel Assumptions.all l g s u) : False := by
  obtain ⟨i, hi, hg, hl⟩ := stationCode stage stop
  have hc : kernel.code[s.pc]? = some i := hs.symm ▸ hi
  cases hf : s.fault
  · exact not_tau_of_stops ⟨_, out_event hf hc (by rw [hg]; rfl) hl⟩ ht
  · simp only [Tau, out, hf, reduceCtorEq] at ht

private theorem atReadyFenceAdvance {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {stage : Fin 2} (hPc : s.pc = outputFencePc stage)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc + 1 ∧ e.kind = .fenceProxy (.async (some (.shared .cta))) none := by
  obtain ⟨i, hi, _, hf⟩ := estep_event_source he
  have hCode : kernel.code[outputFencePc stage]? =
      some ⟨none, .fence (.proxy (.async (some (.shared .cta))))⟩ := by
    fin_cases stage
    · exact Flow.code_8758
    · exact Flow.code_9054
  rw [hPc, hCode] at hi
  obtain rfl := Option.some.inj hi.symm
  change Fires s.pc (.fenceProxy (.async (some (.shared .cta))) none (next s)) e (some u) at hf
  exact ⟨(congrArg TState.pc (Option.some.inj hf.2)).trans rfl, congrArg Event.kind hf.1⟩

private theorem atReadyArrivalAdvance {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {stage : Fin 2} (hPc : s.pc = readyEndPc stage)
    (he : EStep kernel Assumptions.all l g s e (some u)) : u.pc = s.pc + 1 := by
  obtain ⟨i, hi, _, hf⟩ := estep_event_source he
  fin_cases stage
  · change s.pc = 8760 at hPc
    rw [hPc, Flow.code_8760] at hi
    obtain rfl := Option.some.inj hi.symm
    obtain ⟨rfl, _⟩ := fires_arrive_state hf
    rfl
  · change s.pc = 9056 at hPc
    rw [hPc, Flow.code_9056] at hi
    obtain rfl := Option.some.inj hi.symm
    obtain ⟨rfl, _⟩ := fires_arrive_state hf
    rfl

private theorem sameStageStorePc (stage : Fin 2) (box : Fin 4) (chunk : Fin 8) :
    outputStorePc stage box chunk ≤ lastStagingPc stage := by
  fin_cases stage <;> fin_cases box <;> fin_cases chunk <;> decide

private theorem lastStagingWriteKind {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {stage : Fin 2} (hPc : s.pc = lastStagingPc stage)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ a bytes, e = ⟨outputStorePc stage 3 7, .wr a bytes⟩ := by
  have hLast : lastStagingPc stage = outputStorePc stage 3 7 := by
    fin_cases stage <;> decide
  obtain ⟨i, hi, _, hf⟩ := estep_event_source he
  rw [hPc, hLast, outputStoreCode] at hi
  obtain rfl := Option.some.inj hi.symm
  have hSource := hPc.trans hLast
  change Fires s.pc (storeTmpl l g s .shared 32 (outputStoreAddrReg stage 7)
    (16384 * (3 : Fin 4).val : Nat) (outputOperands stage 3 7)) e (some u) at hf
  unfold storeTmpl at hf
  repeat' split at hf
  all_goals try (cases hf.2)
  exact ⟨_, _, hSource ▸ hf.1⟩

private theorem passesStation {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} (stage : Fin 2) (stop : Fin 3)
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : 7745 ≤ s.pc) (hHi : s.pc ≤ 9205) (hSub : s.sub ≤ 3)
    (hStart : s.pc ≤ stationPc stage stop ∨ 9201 ≤ s.pc)
    {j : Nat} {target : Event} (he : events[j]? = some target)
    (hTarget : stationPc stage stop < target.pc) (hTargetEnd : target.pc < 9201) :
    ∃ k < j, ∃ prior t u, events[k]? = some prior ∧ t.pc = stationPc stage stop ∧
      EStep kernel Assumptions.all l g t prior (some u) := by
  have hBand := stationBounds stage stop
  have finish {s u : TState} (hs : s.pc ≤ stationPc stage stop ∨ 9201 ≤ s.pc)
      (hn : s.pc ≠ stationPc stage stop) (hm : ReadyMotion stage s u) :
      u.pc ≤ stationPc stage stop ∨ 9201 ≤ u.pc := by
    rcases hm with h | h | h | h <;> omega
  induction hw generalizing j with
  | stop => simp at he
  | @last s e hs =>
    have hu := estep_source_pc hs
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst target; omega
    | succ j => simp at he
  | @tau s u events visits ht hw ih =>
    have hEnd : s.pc < 9205 := by
      by_contra hn
      have hOnly := correctionReturnTail (by omega : s.pc = 9205) (.tau ht hw)
        (List.mem_of_getElem? he)
      omega
    have hn : s.pc ≠ stationPc stage stop := fun hs => stationNotLocal hs ht
    obtain ⟨hl, hh, hsub, hm⟩ := readyTraceStep stage hLo hEnd hSub (.inl ⟨rfl, ht⟩)
    exact ih hl hh hsub (finish hStart hn hm) he
  | @ev s u e events visits hs hw ih =>
    have hSource := estep_source_pc hs
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst target
      omega
    | succ j =>
      have he' : events[j]? = some target := he
      by_cases hAt : s.pc = stationPc stage stop
      · exact ⟨0, by omega, e, s, u, rfl, hAt, hs⟩
      have hEnd : s.pc < 9205 := by
        by_contra hn
        have hOnly := correctionReturnTail (by omega : s.pc = 9205) (.ev hs hw)
          (List.mem_cons_of_mem _ (List.mem_of_getElem? he'))
        omega
      obtain ⟨hl, hh, hsub, hm⟩ := readyTraceStep stage hLo hEnd hSub (.inr ⟨_, rfl, hs⟩)
      obtain ⟨k, hk, f, t, v, hf, ht, hF⟩ :=
        ih hl hh hsub (finish hStart hAt hm) he'
      exact ⟨k + 1, by omega, f, t, v, hf, ht, hF⟩

private theorem neverReturnsBeforeStation (stage : Fin 2) (stop : Fin 3)
    {l : Launch} {g : Nat} {s : TState} {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hl : 7745 ≤ s.pc) (hh : s.pc ≤ 9205) (hSub : s.sub ≤ 3)
    (hPast : stationPc stage stop < s.pc) {e : Event} (he : e ∈ events) :
    stationPc stage stop < e.pc := by
  have hBand := stationBounds stage stop
  have after {s u : TState} (hp : stationPc stage stop < s.pc) (h : ReadyMotion stage s u) :
      stationPc stage stop < u.pc := by
    rcases h with h | h | h | h <;> omega
  induction hw with
  | stop => cases he
  | last hs => obtain rfl := List.mem_singleton.mp he; rwa [estep_source_pc hs]
  | @tau s u events visits ht hw ih =>
    by_cases hExit : s.pc = 9205
    · rw [correctionReturnTail hExit (.tau ht hw) he]
      omega
    obtain ⟨hLo, hHi, hSmall, hMove⟩ := readyTraceStep stage hl (by omega) hSub (.inl ⟨rfl, ht⟩)
    exact ih hLo hHi hSmall (after hPast hMove) he
  | @ev s u event events visits hs hw ih =>
    rcases List.mem_cons.mp he with rfl | he
    · rwa [estep_source_pc hs]
    · by_cases hExit : s.pc = 9205
      · rw [correctionReturnTail hExit (.ev hs hw) (List.mem_cons_of_mem _ he)]
        omega
      obtain ⟨hLo, hHi, hSmall, hMove⟩ :=
        readyTraceStep stage hl (by omega) hSub (.inr ⟨_, rfl, hs⟩)
      exact ih hLo hHi hSmall (after hPast hMove) he

private theorem afterStation (stage : Fin 2) (stop : Fin 3)
    {l : Launch} {g : Nat} {s : TState} {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hl : 7745 ≤ s.pc) (hh : s.pc ≤ 9205) (hSub : s.sub ≤ 3)
    (advance : ∀ {t u e}, t.pc = stationPc stage stop →
      EStep kernel Assumptions.all l g t e (some u) → u.pc = t.pc + 1)
    {i j : Nat} {first last : Event} (hi : events[i]? = some first)
    (hj : events[j]? = some last) (hOrder : i < j) (hFirst : first.pc = stationPc stage stop) :
    stationPc stage stop < last.pc := by
  have hBand := stationBounds stage stop
  induction hw generalizing i j with
  | stop => simp at hi
  | @last s e h =>
    have hj' := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_singleton] at hj'
    omega
  | @tau s u events visits ht hw ih =>
    have hEnd : s.pc < 9205 := by
      by_contra hn
      have hOnly := correctionReturnTail (by omega : s.pc = 9205) (.tau ht hw)
        (List.mem_of_getElem? hi)
      omega
    obtain ⟨hLo, hHi, hSmall, _⟩ := readyTraceStep stage hl hEnd hSub (.inl ⟨rfl, ht⟩)
    exact ih hLo hHi hSmall hi hj hOrder
  | @ev s u event events visits hs hw ih =>
    have hEnd : s.pc < 9205 := by
      by_contra hn
      have hOnly := correctionReturnTail (by omega : s.pc = 9205) (.ev hs hw)
        (List.mem_of_getElem? hi)
      omega
    obtain ⟨hLo, hHi, hSmall, _⟩ := readyTraceStep stage hl hEnd hSub (.inr ⟨_, rfl, hs⟩)
    cases j with
    | zero => omega
    | succ j =>
      have hj' : events[j]? = some last := hj
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst first
        have hPc := (estep_source_pc hs).symm.trans hFirst
        have hNext := advance hPc hs
        exact neverReturnsBeforeStation stage stop hw hLo hHi hSmall (by omega)
          (List.mem_of_getElem? hj')
      | succ i =>
        have hi' : events[i]? = some first := hi
        exact ih hLo hHi hSmall hi' hj' (by omega)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem correctionLateWalk (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {e : Event} (he : X.get (g,j) = some e) (hBand : 8492 ≤ e.pc ∧ e.pc < 9201) :
    ∃ t vs, 5 ≤ j ∧ t.pc = 7745 ∧ t.sub = 0 ∧
      Walk kernel Assumptions.all l g t ((X.tr g).drop 5) vs := by
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hHint
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hNonzero : 0 < warpIndex l g := by omega
  obtain ⟨_, _, hj, _, _⟩ := nonzeroCommonPrefixOfLateEvent hp hX (g := g) hg hNonzero he
    (by omega)
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s, o, hs, hr⟩ := nonzeroRoleEntryPrefix hp hX (g := g) hg hNonzero (by omega)
  have hDispatch : dispatchParamPc ⟨warpIndex l g, warpIndex_lt hp g⟩ = 7745 := by
    simp only [dispatchParamPc]
    split_ifs <;> omega
  rw [hDispatch] at hs
  obtain ⟨_, hw⟩ := Mma.walkFromRun hr
  exact ⟨s, _, hj, hs.1, hs.2.1, hw⟩

private theorem correctionReadyWalk (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {stage : Fin 2} (h : CorrectionReady X (g, j) stage) :
    ∃ t vs, 5 ≤ j ∧ t.pc = 7745 ∧ t.sub = 0 ∧
      Walk kernel Assumptions.all l g t ((X.tr g).drop 5) vs := by
  apply correctionLateWalk hp hX (h.decoded hp hX)
  change 8492 ≤ readyEndPc stage ∧ readyEndPc stage < 9201
  fin_cases stage <;> decide

private theorem getFromReadySuffix {X : Execution} {g j : Nat} {e : Event} (hj : 5 ≤ j)
    (h : X.get (g,j) = some e) : ((X.tr g).drop 5)[j - 5]? = some e := by
  rw [List.getElem?_drop, Nat.add_sub_of_le hj]
  exact h

private theorem getAtReadySuffix {X : Execution} {g j : Nat} {e : Event}
    (h : ((X.tr g).drop 5)[j]? = some e) : X.get (g, 5 + j) = some e := by
  rw [List.getElem?_drop] at h
  exact h

/-- One correction lane releases the ready object at most once per output stage. -/
theorem CorrectionReady.unique (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j k : Nat} {stage : Fin 2} (hj : CorrectionReady X (g,j) stage)
    (hk : CorrectionReady X (g,k) stage) : j = k := by
  let e : Event := ⟨readyEndPc stage, .arrive (Epilogue.readyLoc l g stage) 0 1 true .cta⟩
  obtain ⟨s, vs, hj₅, hs, hSub, hw⟩ := correctionReadyWalk hp hX hj
  obtain ⟨_, _, hk₅, _, _, _⟩ := correctionReadyWalk hp hX hk
  have hGetJ : ((X.tr g).drop 5)[j - 5]? = some e := getFromReadySuffix hj₅ (hj.decoded hp hX)
  have hGetK : ((X.tr g).drop 5)[k - 5]? = some e := getFromReadySuffix hk₅ (hk.decoded hp hX)
  have after {i i' : Nat} (hFirst : ((X.tr g).drop 5)[i]? = some e)
      (hLast : ((X.tr g).drop 5)[i']? = some e) (hOrd : i < i') : False := by
    have h := afterStation stage 2 hw (by omega) (by omega) (by omega)
      (fun hPc => atReadyArrivalAdvance (stage := stage) hPc)
      hFirst hLast hOrd (show e.pc = stationPc stage 2 from rfl)
    exact (Nat.lt_irrefl e.pc) h
  rcases lt_trichotomy j k with h | h | h
  · exact (after hGetJ hGetK (by omega)).elim
  · exact h
  · exact (after hGetK hGetJ (by omega)).elim

private theorem correctionReadyFence (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {stage : Fin 2} (h : CorrectionReady X (g,j) stage) :
    ∃ k < j, 5 ≤ k ∧ X.get (g,k) = some ⟨outputFencePc stage,
      .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  let target : Event := ⟨readyEndPc stage, .arrive (Epilogue.readyLoc l g stage) 0 1 true .cta⟩
  have he : X.get (g,j) = some target := h.decoded hp hX
  obtain ⟨s, vs, hj, hs, hSub, hw⟩ := correctionReadyWalk hp hX h
  have hStart : s.pc ≤ stationPc stage 1 := by
    have := stationBounds stage 1
    omega
  have hTarget : stationPc stage 1 < target.pc := by
    change outputFencePc stage < outputFencePc stage + 2
    omega
  obtain ⟨k, hk, f, t, u, hf, hPc, hStep⟩ :=
    passesStation stage 1 hw (by omega) (by omega) (by omega) (.inl hStart)
      (getFromReadySuffix hj he) hTarget (stationBounds stage 1).2.2.2
  have hKind := (atReadyFenceAdvance hPc hStep).2
  have hEvent : f = ⟨outputFencePc stage, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
    obtain ⟨pc, kind⟩ := f
    have hSource := (estep_source_pc hStep).trans hPc
    change pc = outputFencePc stage at hSource
    change kind = _ at hKind
    rw [hSource, hKind]
  exact ⟨5 + k, by omega, by omega, hEvent ▸ getAtReadySuffix hf⟩

/-- Every observed output-ready arrival has an earlier proxy fence in its own lane. -/
theorem CorrectionReady.fence (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {stage : Fin 2} (h : CorrectionReady X (g,j) stage) :
    ∃ fence, TraceBefore X (g,fence) (g,j) ∧
      X.IsProxyFence (g,fence) (.async (some (.shared .cta))) none := by
  obtain ⟨fence, hOrd, _, hFence⟩ := correctionReadyFence hp hX h
  have hLen := (List.getElem?_eq_some_iff.mp (h.decoded hp hX)).1
  exact ⟨fence, ⟨rfl, hOrd, hLen⟩, ⟨_, hFence⟩⟩

/-- An ordinary write of one lane's staging element for the indicated output stage. -/
@[no_expose] def StageStagingWrite (X : Execution) (i : EvId) (stage : Fin 2)
    (a : Acc) (data : List Byte) : Prop :=
  ∃ (box : Fin 4) (chunk : Fin 8), X.get i = some ⟨outputStorePc stage box chunk, .wr a data⟩

/-- A decoded occurrence identifies the stage of its staging write. -/
theorem StageStagingWrite.ofEvent {X : Execution} {i : EvId} {stage : Fin 2}
    {a : Acc} {data : List Byte} (box : Fin 4) (chunk : Fin 8)
    (he : X.get i = some ⟨outputStorePc stage box chunk, .wr a data⟩) :
    StageStagingWrite X i stage a data :=
  ⟨box, chunk, he⟩

/-- Recover the staging station within the Thread layer. -/
theorem StageStagingWrite.decoded {X : Execution} {i : EvId} {stage : Fin 2}
    {a : Acc} {data : List Byte}
    (h : StageStagingWrite X i stage a data) :
    ∃ (box : Fin 4) (chunk : Fin 8), X.get i = some ⟨outputStorePc stage box chunk, .wr a data⟩ :=
  h

/-- The stage observation is a performed ordinary write with its recorded word. -/
theorem StageStagingWrite.writes {X : Execution} {i : EvId} {stage : Fin 2}
    {a : Acc} {data : List Byte}
    (h : StageStagingWrite X i stage a data) :
    X.Writes i a data := by
  obtain ⟨_, _, he⟩ := h
  exact ⟨_, he⟩

/-- A completed active correction lane issued a concrete first-stage write. -/
theorem firstStagingObservationOfComplete (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X) {g : Nat}
    (hg : g < l.threads) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads) :
    ∃ j a bytes, StageStagingWrite X (g,j) 0 a bytes := by
  obtain ⟨_, j, bytes, _, _, hStore⟩ := Correction.firstStagingWriteEventAfterAcquire hp hX
    hDone hg hLo hHi hWork
  exact ⟨j, _, bytes, .ofEvent 0 0 hStore⟩

/-- A staging observation gives the physical element in its recorded stage. -/
theorem StageStagingWrite.element (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {stage : Fin 2} {a : Acc} {data : List Byte} (h : StageStagingWrite X i stage a data)
    :
    ∃ (box : Fin 4) (x row : Nat), x < 32 ∧ row < 128 ∧
      a = outputElementAccess l i.1 stage box x row := by
  obtain ⟨box, chunk, he⟩ := h.decoded
  obtain ⟨elem, hA⟩ := Correction.stagingWriteElement hp hX stage box chunk he
  have := chunk.isLt
  have := elem.isLt
  exact ⟨box, 4 * chunk.val + elem.val, rowOf l i.1, by omega, Nat.mod_lt _ (by decide), hA⟩

/-- An output proxy fence is the correction lane's handoff of its staging writes. -/
@[no_expose] def CorrectionOutputFence (X : Execution) (i : EvId) (stage : Fin 2) : Prop :=
  X.get i = some ⟨outputFencePc stage, .fenceProxy (.async (some (.shared .cta))) none⟩

/-- A correction output fence cannot occur before the lane has staged its first O tile. -/
theorem CorrectionOutputFence.priorFirstStaging (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {stage : Fin 2}
    (hFence : CorrectionOutputFence X (g,j) stage) :
    ∃ k a bytes, StageStagingWrite X (g,k) 0 a bytes ∧ TraceBefore X (g,k) (g,j) := by
  let target : Event := ⟨outputFencePc stage, .fenceProxy (.async (some (.shared .cta))) none⟩
  have he : X.get (g,j) = some target := hFence
  have hBand : 8492 ≤ target.pc ∧ target.pc < 9201 := by fin_cases stage <;> decide
  have hLower : stationPc 0 0 < target.pc := by fin_cases stage <;> decide
  obtain ⟨s, vs, hj, hs, hSub, hw⟩ := correctionLateWalk hp hX he hBand
  have hStart : s.pc ≤ stationPc 0 0 := by rw [hs]; decide
  obtain ⟨k, hk, _, _, _, hGet, hPc, hStep⟩ :=
    passesStation 0 0 hw (by omega) (by omega) (by omega) (.inl hStart)
      (getFromReadySuffix hj he) hLower hBand.2
  obtain ⟨a, bytes, hEvent⟩ := lastStagingWriteKind hPc hStep
  refine ⟨5 + k, a, bytes, StageStagingWrite.ofEvent 3 7 (hEvent ▸ getAtReadySuffix hGet),
    rfl, by omega, (List.getElem?_eq_some_iff.mp he).1⟩

/-- The only remaining proxy fences are the two Bias-consumer stations. -/
@[no_expose] def BiasOperandFence (X : Execution) (i : EvId) (repeated : Bool) : Prop :=
  X.get i = some ⟨Softmax.biasFencePc repeated, .fenceProxy (.async (some (.shared .cta))) none⟩

/-- The underlying event for the Bias-fence observation. -/
theorem BiasOperandFence.decoded {X : Execution} {i : EvId} {repeated : Bool}
    (h : BiasOperandFence X i repeated) :
    X.get i = some
      ⟨Softmax.biasFencePc repeated, .fenceProxy (.async (some (.shared .cta))) none⟩ :=
  h

/-- Only the two softmax groups issue a Bias proxy fence. -/
theorem BiasOperandFence.role (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {repeated : Bool} (h : BiasOperandFence X i repeated) :
    warpIndex l i.1 < 8 := by
  have hRange : 3100 ≤ Softmax.biasFencePc repeated ∧ Softmax.biasFencePc repeated < 7745 ∧
      Softmax.biasFencePc repeated ∉ registerHintSites := by cases repeated <;> decide
  have hr := roleBodyPcOfEvent hp hX h.decoded (by dsimp only; omega) hRange.2.2
  unfold roleBodyPc at hr
  rcases hr with hExit | hBody
  · dsimp only at hExit
    omega
  · split_ifs at hBody <;> dsimp only at hBody <;> omega

private theorem proxyFenceSites :
    OpPcsFast kernel.code proxyFenceOp [3581, 5269, 8758, 9054] = true := by
  decide +kernel

/-- Every performed proxy fence belongs to the Bias or O staging protocol. -/
theorem proxyFenceObservation {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {kind : ProxyFence} {scope : Option MbarScope}
    (hFence : X.IsProxyFence i kind scope) :
    (∃ repeated, BiasOperandFence X i repeated) ∨ (∃ stage, CorrectionOutputFence X i stage) := by
  obtain ⟨rfl, rfl⟩ := actualProxyFence hX hFence
  obtain ⟨pc, he⟩ := hFence
  rcases get_source hX he with ⟨_, hFault⟩ | ⟨_, _, _, _, hc, hf⟩
  · cases hFault
  have hPc := OpPcsFast.mem proxyFenceSites hc (fires_proxyFence_op hf rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hPc
  rcases hPc with rfl | rfl | rfl | rfl
  · exact .inl ⟨false, he⟩
  · exact .inl ⟨true, he⟩
  · exact .inr ⟨0, he⟩
  · exact .inr ⟨1, he⟩

/-- Actual staging stores expose both their stage and their exact physical element. -/
theorem Correction.StagingWrite.stageElement (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {a : Acc} {data : List Byte}
    (h : Correction.StagingWrite X (.thread i) a data) :
    ∃ (stage : Fin 2) (box : Fin 4) (x row : Nat), x < 32 ∧ row < 128 ∧
      a = outputElementAccess l i.1 stage box x row ∧ StageStagingWrite X i stage a data := by
  obtain ⟨stage, box, chunk, he⟩ := h.decoded
  have hStage := StageStagingWrite.ofEvent box chunk he
  obtain ⟨plane, x, row, hx, hr, hA⟩ := hStage.element hp hX
  exact ⟨stage, plane, x, row, hx, hr, hA, hStage⟩

/-- A ready arrival follows a real final-vector write and its stage's shared proxy fence. -/
theorem CorrectionReady.finalWriteAndFence (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {stage : Fin 2}
    (h : CorrectionReady X (g,j) stage) :
    ∃ writer fence : Nat, ∃ a bytes,
      StageStagingWrite X (g,writer) stage a bytes ∧
      TraceBefore X (g,writer) (g,fence) ∧ TraceBefore X (g,fence) (g,j) ∧
      X.IsProxyFence (g,fence) (.async (some (.shared .cta))) none := by
  obtain ⟨s, vs, _, hs, hSub, hw⟩ := correctionReadyWalk hp hX h
  obtain ⟨f, hf, hF, hGet⟩ := correctionReadyFence hp hX h
  let target : Event := ⟨outputFencePc stage, .fenceProxy (.async (some (.shared .cta))) none⟩
  have hBand := stationBounds stage 0
  have hStart : s.pc ≤ stationPc stage 0 := by
    have hh : stationPc stage 0 = lastStagingPc stage := rfl
    omega
  have hLower : stationPc stage 0 < target.pc := by fin_cases stage <;> decide
  have hUpper : target.pc < 9201 := by fin_cases stage <;> decide
  obtain ⟨k, hk, e, t, u, he, hPc, hStep⟩ :=
    passesStation stage 0 hw (by omega) (by omega) (by omega) (.inl hStart)
      (getFromReadySuffix hF (show X.get (g,f) = some target from hGet)) hLower hUpper
  obtain ⟨a, bytes, heq⟩ := lastStagingWriteKind hPc hStep
  have hStore := StageStagingWrite.ofEvent 3 7 (heq ▸ getAtReadySuffix he)
  have hLen := (List.getElem?_eq_some_iff.mp (h.decoded hp hX)).1
  have hFenceLen := (List.getElem?_eq_some_iff.mp hGet).1
  exact ⟨5 + k, f, a, bytes, hStore, ⟨rfl, by omega, hFenceLen⟩,
    ⟨rfl, hf, hLen⟩, ⟨_, hGet⟩⟩

private theorem stagingBeforeReadyFence (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j k f : Nat} {stage : Fin 2}
    (h : CorrectionReady X (g,j) stage) (hF : 5 ≤ f)
    (hFence : X.get (g,f) = some ⟨outputFencePc stage,
      .fenceProxy (.async (some (.shared .cta))) none⟩) (box : Fin 4) (chunk : Fin 8) {a : Acc}
    {bytes : List Byte} (hStore : X.get (g,k) = some ⟨outputStorePc stage box chunk, .wr a bytes⟩)
    : k < f := by
  obtain ⟨s, vs, _, hs, hSub, hw⟩ := correctionReadyWalk hp hX h
  by_contra hn
  have hBound := sameStageStorePc stage box chunk
  have hLess : lastStagingPc stage < outputFencePc stage := by fin_cases stage <;> decide
  have hNe : k ≠ f := by
    intro he
    subst k
    exact Kind.noConfusion (congrArg Event.kind (Option.some.inj (hStore.symm.trans hFence)))
  have hk : 5 ≤ k := by omega
  let fence : Event := ⟨outputFencePc stage, .fenceProxy (.async (some (.shared .cta))) none⟩
  let store : Event := ⟨outputStorePc stage box chunk, .wr a bytes⟩
  have hAfter := afterStation stage 1 hw (by omega) (by omega) (by omega)
    (fun hPc he => (atReadyFenceAdvance (stage := stage) hPc he).1)
    (getFromReadySuffix hF (show X.get (g,f) = some fence from hFence))
    (getFromReadySuffix hk (show X.get (g,k) = some store from hStore))
    (by omega) (show fence.pc = stationPc stage 1 from rfl)
  change outputFencePc stage < outputStorePc stage box chunk at hAfter
  omega

/-- Each actual same-stage output write in the lane precedes its publication fence. -/
theorem CorrectionReady.stagingBeforeFence (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {stage : Fin 2}
    (h : CorrectionReady X (g,j) stage) :
    ∃ fence, TraceBefore X (g,fence) (g,j) ∧
      X.IsProxyFence (g,fence) (.async (some (.shared .cta))) none ∧
      ∀ {writer : Nat} {a : Acc} {bytes : List Byte},
        StageStagingWrite X (g,writer) stage a bytes → TraceBefore X (g,writer) (g,fence) := by
  obtain ⟨fence, hOrd, hF, hFence⟩ := correctionReadyFence hp hX h
  have hLen := (List.getElem?_eq_some_iff.mp (h.decoded hp hX)).1
  have hFenceLen := (List.getElem?_eq_some_iff.mp hFence).1
  refine ⟨fence, ⟨rfl, hOrd, hLen⟩, ⟨_, hFence⟩, ?_⟩
  intro writer a bytes hStore
  obtain ⟨box, chunk, he⟩ := hStore
  exact ⟨rfl, stagingBeforeReadyFence hp hX h hF hFence box chunk he, hFenceLen⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread
