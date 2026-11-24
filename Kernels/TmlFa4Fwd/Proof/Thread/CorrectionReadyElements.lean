-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionOutputReadyTrace
import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Flow.EventCont

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Softmax
open PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

private def firstVectorPc (stage : Fin 2) : Nat := outputStorePc stage 0 0

private def publishPc (stage : Fin 2) : Nat := outputFencePc stage + 2

private def elementWalkCode (stage : Fin 2) (pc : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || correctionReturningOp i.op) && !(scoreEventWrites i.op).contains 0 &&
    (match i.op with | .mem a => a.kind != .load || a.regs.length ≤ 1 | _ => true) &&
    match i.op with
    | .bra dest _ => 7755 ≤ dest && dest ≤ 9205 &&
        (if pc < firstVectorPc stage then dest < firstVectorPc stage || publishPc stage < dest
         else publishPc stage < pc && publishPc stage < dest)
    | .brx .. => false
    | _ => true

private theorem elementWalkCodeAt (stage : Fin 2) {pc : Nat} {i : Instr}
    (hLo : 7755 ≤ pc) (hHi : pc < 9205) (hc : kernel.code[pc]? = some i) :
    elementWalkCode stage pc i = true := by
  let code := ((kernel.code.drop 7755).take (9205 - 7755)).zipIdx 7755
  have hAll : code.all (fun (i, pc) => elementWalkCode stage pc i) = true := by
    fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, pc)
  apply List.mem_of_getElem? (i := pc - 7755)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private def storePredecessorCheck (p : Instr × Instr) : Bool :=
  match p.2.op with
  | .mem ma => ma.kind != .store || p.1.op.isLocal
  | _ => true

private theorem storePredecessorLocal (stage : Fin 2) (box : Fin 4) (chunk : Fin 8)
    {i : Instr} (hc : kernel.code[outputStorePc stage box chunk - 1]? = some i) :
    i.op.isLocal = true := by
  let pos := outputStorePc stage box chunk
  let left := (kernel.code.drop 8491).take 562
  let right := (kernel.code.drop 8492).take 562
  have hAll : (left.zip right).all storePredecessorCheck = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hPos : 8492 ≤ pos ∧ pos < 9054 := by
    dsimp only [pos]
    fin_cases stage <;> fin_cases box <;> fin_cases chunk <;> decide
  let off := pos - 8492
  have hOff : off < 562 := by dsimp only [off]; omega
  have hLeft : 8491 + off = pos - 1 := by dsimp only [off]; omega
  have hRight : 8492 + off = pos := by dsimp only [off]; omega
  have hMem : (i, outputStoreInstr stage box chunk) ∈ left.zip right := by
    apply List.mem_of_getElem? (i := off)
    apply List.getElem?_zip_eq_some.mpr
    constructor
    · dsimp only [left]
      rw [List.getElem?_take_of_lt hOff, List.getElem?_drop, hLeft]
      exact hc
    · dsimp only [right]
      rw [List.getElem?_take_of_lt hOff, List.getElem?_drop, hRight]
      exact outputStoreCode stage box chunk
  exact List.all_eq_true.mp hAll _ hMem

private def BeforeVector (stage : Fin 2) (site : Nat) (t : TState) : Prop :=
  t.pc ≤ site ∨ publishPc stage < t.pc

private theorem elementWalkStep (stage : Fin 2) (box : Fin 4) (chunk : Fin 8)
    {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 7755 ≤ s.pc) (hHi : s.pc < 9205) (hSub : s.sub ≤ 3) (hs : SetupScratch s)
    (hBefore : BeforeVector stage (outputStorePc stage box chunk) s)
    (hStrict : s.pc ≠ outputStorePc stage box chunk)
    (h : WStep kernel Assumptions.all l g s ev u) :
    7755 ≤ u.pc ∧ u.pc ≤ 9205 ∧ u.sub ≤ 3 ∧ SetupScratch u ∧
      BeforeVector stage (outputStorePc stage box chunk) u ∧
      (u.pc = outputStorePc stage box chunk → u.sub = 0) := by
  have hSites : firstVectorPc stage ≤ outputStorePc stage box chunk ∧
      outputStorePc stage box chunk < publishPc stage := by
    fin_cases stage <;> fin_cases box <;> fin_cases chunk <;> decide
  have hBounds := hBefore
  unfold BeforeVector at hBounds
  have hKeep {i : Instr} (hc : kernel.code[s.pc]? = some i) (hNl : i.op.isLocal = false) :
      correctionReturningOp i.op = true ∧ 0 ∉ scoreEventWrites i.op ∧
      (match i.op with | .mem a => a.kind = .load → a.regs.length ≤ 1 | _ => True) := by
    have hOk := (Bool.and_eq_true_iff.mp (elementWalkCodeAt stage hLo hHi hc)).1
    simp only [Bool.and_eq_true, hNl, Bool.false_or, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hOk
    refine ⟨hOk.1.1, hOk.1.2, ?_⟩
    cases ho : i.op <;> try trivial
    case mem a =>
      intro hLd
      simpa only [ho, hLd, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] using hOk.2
  have hFinish (hPc : u.pc = s.pc ∨ u.pc = s.pc + 1) : 7755 ≤ u.pc ∧ u.pc ≤ 9205 ∧
      BeforeVector stage (outputStorePc stage box chunk) u :=
    ⟨by omega, by omega, by unfold BeforeVector; omega⟩
  rcases h with ⟨_, ht⟩ | ⟨_, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, _, hTau⟩ := correctionTauFrame hOff ht
    rcases hTau with ⟨rfl, _⟩ | ⟨_, hLocal, hFrame⟩
    · have hBounds := hFinish (.inr rfl)
      exact ⟨hBounds.1, hBounds.2.1, Nat.zero_le _, SetupScratch.clear rfl rfl,
        hBounds.2.2, fun _ => rfl⟩
    have hShape := scratchLocal hs hc hLocal
    have hNextClear := hFrame.sub.trans hShape.1
    have hNext := SetupScratch.clear hNextClear (hFrame.acc.trans hShape.2)
    have hPc := hFrame.pc
    have hChecked := (Bool.and_eq_true_iff.mp (elementWalkCodeAt stage hLo hHi hc)).2
    cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
    case brx => simp [ho] at hChecked
    case bra dest uni =>
      simp only [ho, Bool.and_eq_true, decide_eq_true_eq] at hChecked
      refine ⟨hPc.symm ▸ hChecked.1.1, hPc.symm ▸ hChecked.1.2,
        by rw [hNextClear]; decide, hNext, ?_, fun _ => hNextClear⟩
      unfold BeforeVector
      by_cases hB : s.pc < firstVectorPc stage
      · have hd : dest < firstVectorPc stage ∨ publishPc stage < dest :=
          by simpa [hB] using hChecked.2
        omega
      · have hd : publishPc stage < s.pc ∧ publishPc stage < dest :=
          by simpa [hB] using hChecked.2
        omega
    all_goals
      have hDone := hFinish (.inr hPc)
      exact ⟨hDone.1, hDone.2.1, by rw [hNextClear]; decide, hNext, hDone.2.2,
        fun _ => hNextClear⟩
  · obtain ⟨i, hc, hNl, _⟩ := estep_event_source he
    have hCode := hKeep hc hNl
    have hProg := (correctionEventProgress hc hCode.1 hSub hCode.2.1 he).1
    have hNext := scratchReturning hs hSub hc hNl hCode.1 hCode.2.1 hCode.2.2 he
    have hPc : u.pc = s.pc ∨ u.pc = s.pc + 1 :=
      hProg.pc.elim (fun hs => .inr hs.1) (fun hs => .inl hs.1)
    have hDone := hFinish hPc
    refine ⟨hDone.1, hDone.2.1, hProg.sub, hNext, hDone.2.2, ?_⟩
    intro hAt
    have hPred : s.pc = outputStorePc stage box chunk - 1 := by rcases hPc with h | h <;> omega
    have hAudit := storePredecessorLocal stage box chunk (hPred ▸ hc)
    rw [hNl] at hAudit
    cases hAudit

private theorem stagingRoleMotion (stage : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {event : Option Event} (hLo : 7755 ≤ s.pc) (hHi : s.pc < 9205) (hSub : s.sub ≤ 3)
    (hw : WStep kernel Assumptions.all l g s event u) :
    7755 ≤ u.pc ∧ u.pc ≤ 9205 ∧ u.sub ≤ 3 ∧
      (u.pc = s.pc ∨ u.pc = s.pc + 1 ∨ s.pc < firstVectorPc stage ∨ publishPc stage < u.pc) := by
  rcases hw with ⟨_, ht⟩ | ⟨_, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, _, hTau⟩ := correctionTauFrame hOff ht
    rcases hTau with ⟨rfl, _⟩ | ⟨_, _, hFrame⟩
    · exact ⟨by change 7755 ≤ s.pc + 1; omega, by change s.pc + 1 ≤ 9205; omega,
        Nat.zero_le _, .inr (.inl rfl)⟩
    have hPc := hFrame.pc
    have hSub' : u.sub ≤ 3 := hFrame.sub.symm ▸ hSub
    have hFall (h : u.pc = s.pc + 1) :
        7755 ≤ u.pc ∧ u.pc ≤ 9205 ∧ u.sub ≤ 3 ∧
          (u.pc = s.pc ∨ u.pc = s.pc + 1 ∨ s.pc < firstVectorPc stage ∨ publishPc stage < u.pc) :=
      ⟨by omega, by omega, hSub', .inr (.inl h)⟩
    have hChecked := (Bool.and_eq_true_iff.mp (elementWalkCodeAt stage hLo hHi hc)).2
    cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
    case brx => simp [ho] at hChecked
    case bra dest uni =>
      simp only [ho, Bool.and_eq_true, decide_eq_true_eq] at hChecked
      refine ⟨hPc.symm ▸ hChecked.1.1, hPc.symm ▸ hChecked.1.2, hSub', .inr (.inr ?_)⟩
      by_cases hB : s.pc < firstVectorPc stage
      · exact .inl hB
      · exact .inr (hPc.symm ▸ (by simpa [hB] using hChecked.2 :
          publishPc stage < s.pc ∧ publishPc stage < dest).2)
    all_goals exact hFall hPc
  · obtain ⟨i, hc, hNl, _⟩ := estep_event_source he
    have hCode := (Bool.and_eq_true_iff.mp (elementWalkCodeAt stage hLo hHi hc)).1
    simp only [Bool.and_eq_true, hNl, Bool.false_or, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hCode
    have hProg := (correctionEventProgress hc hCode.1.1 hSub hCode.1.2 he).1
    rcases hProg.pc with hp | hp
    · exact ⟨by omega, by omega, hProg.sub, .inr (.inl hp.1)⟩
    · exact ⟨by omega, by omega, hProg.sub, .inl hp.1⟩

/-- The role stays within its active interval through every returning transition. -/
theorem stagingRoleStepBounds (stage : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {event : Option Event} (hLo : 7755 ≤ s.pc) (hHi : s.pc < 9205) (hSub : s.sub ≤ 3)
    (hw : WStep kernel Assumptions.all l g s event u) :
    7755 ≤ u.pc ∧ u.pc ≤ 9205 ∧ u.sub ≤ 3 := by
  obtain ⟨hl, hh, hs, _⟩ := stagingRoleMotion stage hLo hHi hSub hw
  exact ⟨hl, hh, hs⟩

/-- A correction lane cannot re-enter an earlier vector once it leaves that instruction. -/
theorem afterStagingVectorStep (stage : Fin 2) (box : Fin 4) (chunk : Fin 8)
    {l : Launch} {g : Nat} {s u : TState} {event : Option Event}
    (hLo : 7755 ≤ s.pc) (hHi : s.pc < 9205) (hSub : s.sub ≤ 3)
    (hp : outputStorePc stage box chunk < s.pc) (hw : WStep kernel Assumptions.all l g s event u) :
    7755 ≤ u.pc ∧ u.pc ≤ 9205 ∧ u.sub ≤ 3 ∧ outputStorePc stage box chunk < u.pc := by
  obtain ⟨hLow, hHigh, hS, hMotion⟩ := stagingRoleMotion stage hLo hHi hSub hw
  have hSite : firstVectorPc stage ≤ outputStorePc stage box chunk ∧
      outputStorePc stage box chunk < publishPc stage := by
    fin_cases stage <;> fin_cases box <;> fin_cases chunk <;> decide
  refine ⟨hLow, hHigh, hS, ?_⟩
  rcases hMotion with h | h | h | h <;> omega

private theorem cutAtVector (stage : Fin 2) (box : Fin 4) (chunk : Fin 8)
    {l : Launch} {g : Nat} {s : TState} {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : 7755 ≤ s.pc) (hHi : s.pc ≤ 9205) (hSub : s.sub ≤ 3) (hScratch : SetupScratch s)
    (hBefore : BeforeVector stage (outputStorePc stage box chunk) s)
    (hClear : s.pc = outputStorePc stage box chunk → s.sub = 0)
    {target : Event} (hm : target ∈ events) (hTarget : target.pc = publishPc stage) :
    ∃ t before rest marks, events = before ++ rest ∧ t.pc = outputStorePc stage box chunk ∧
      t.sub = 0 ∧ Walk kernel Assumptions.all l g t rest marks ∧ target ∈ rest := by
  have hSite : outputStorePc stage box chunk < publishPc stage ∧ publishPc stage < 9205 := by
    fin_cases stage <;> fin_cases box <;> fin_cases chunk <;> decide
  have finish {s : TState} {events : List Event} {visits : List Visit}
      (hw : Walk kernel Assumptions.all l g s events visits)
      (hPc : s.pc = outputStorePc stage box chunk) (hs : s.sub = 0) (hm : target ∈ events) :
      ∃ t before rest marks, events = before ++ rest ∧
        t.pc = outputStorePc stage box chunk ∧ t.sub = 0 ∧
        Walk kernel Assumptions.all l g t rest marks ∧ target ∈ rest :=
    ⟨s, [], events, visits, rfl, hPc, hs, hw, hm⟩
  induction hw with
  | stop => cases hm
  | @last s e he =>
    obtain rfl := List.mem_singleton.mp hm
    have hPc := estep_source_pc he
    unfold BeforeVector at hBefore
    omega
  | @tau s u events visits ht hw ih =>
    by_cases hPc : s.pc = outputStorePc stage box chunk
    · exact finish (.tau ht hw) hPc (hClear hPc) hm
    have hEnd : s.pc < 9205 := by
      by_contra hn
      have hEq := correctionReturnTail (by omega : s.pc = 9205) (.tau ht hw) hm
      omega
    obtain ⟨hl, hh, hsmall, hs, hb, hz⟩ :=
      elementWalkStep stage box chunk hLo hEnd hSub hScratch hBefore hPc (.inl ⟨rfl, ht⟩)
    exact ih hl hh hsmall hs hb hz hm
  | @ev s u event events visits he hw ih =>
    by_cases hPc : s.pc = outputStorePc stage box chunk
    · exact finish (.ev he hw) hPc (hClear hPc) hm
    have hPast : target ∈ events := by
      rcases List.mem_cons.mp hm with rfl | h
      · have hE := estep_source_pc he
        unfold BeforeVector at hBefore
        omega
      · exact h
    have hEnd : s.pc < 9205 := by
      by_contra hn
      have hEq := correctionReturnTail (by omega : s.pc = 9205) (.ev he hw) hm
      omega
    obtain ⟨hl, hh, hsmall, hs, hb, hz⟩ :=
      elementWalkStep stage box chunk hLo hEnd hSub hScratch hBefore hPc (.inr ⟨_, rfl, he⟩)
    obtain ⟨v, before, rest, marks, hTrace, hV, hZero, hW, hTargetIn⟩ :=
      ih hl hh hsmall hs hb hz hPast
    exact ⟨v, event :: before, rest, marks, congrArg (event :: ·) hTrace,
      hV, hZero, hW, hTargetIn⟩

/-- A staging instruction has no local transition between its element writes. -/
theorem decodedStoreStops {l : Launch} {g : Nat} {s : TState}
    (stage : Fin 2) (box : Fin 4) (chunk : Fin 8)
    (hs : s.pc = outputStorePc stage box chunk) : Stops kernel Assumptions.all l g s := by
  cases hf : s.fault with
  | some fault => exact ⟨.ub fault, by simp only [out, hf]⟩
  | none =>
    exact ⟨_, out_event hf (hs.symm ▸ outputStoreCode stage box chunk) rfl rfl⟩

/-- The decoded element store emits its current component and advances the vector cursor. -/
theorem vectorElementStep {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (box : Fin 4) (chunk : Fin 8) (hPc : s.pc = outputStorePc stage box chunk)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ a bytes, e = ⟨outputStorePc stage box chunk, .wr a bytes⟩ ∧ a.elem = s.sub ∧
      u = afterStore s (outputOperands stage box chunk) := by
  obtain ⟨i, hc, _, hf⟩ := estep_event_source he
  rw [hPc, outputStoreCode] at hc
  obtain rfl := Option.some.inj hc.symm
  let reg := outputStoreAddrReg stage chunk
  let off : Int := (16384 * box.val : Nat)
  let operands := outputOperands stage box chunk
  change Fires s.pc (storeTmpl l g s .shared 32 reg off operands) e (some u) at hf
  unfold storeTmpl at hf
  cases hAddr : effAddr l g s .shared reg off with
  | error fault =>
    simp only [hAddr, bind, Except.bind] at hf
    cases hf.2
  | ok loc =>
    simp only [hAddr, bind, Except.bind] at hf
    cases hAcc : elemAcc loc (32 / 8) operands.length s.sub with
    | error fault => rw [hAcc] at hf; cases hf.2
    | ok a =>
      rw [hAcc] at hf
      have hElem : a.elem = s.sub := by
        unfold elemAcc at hAcc
        split at hAcc
        · cases hAcc
        · obtain rfl := Except.ok.inj hAcc.symm
          rfl
      cases hs : operands[s.sub]? with
      | none => rw [hs] at hf; cases hf.2
      | some operand =>
        rw [hs] at hf
        change Fires s.pc (match readValue l g s 32 operand >>= storeValue 32 with
          | .error fault => .ub fault
          | .ok value => .write a value.toBytes (afterStore s operands)) e (some u) at hf
        cases hValue : readValue l g s 32 operand >>= storeValue 32 with
        | error fault =>
          rw [hValue] at hf
          cases hf.2
        | ok value =>
          rw [hValue] at hf
          have hEvent : e = ⟨s.pc, .wr a value.toBytes⟩ := hf.1
          rw [hPc] at hEvent
          exact ⟨a, value.toBytes, hEvent, hElem, Option.some.inj hf.2⟩

private theorem vectorPrefixElement (stage : Fin 2) (box : Fin 4) (chunk : Fin 8)
    {l : Launch} {g : Nat} {s : TState} {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hPc : s.pc = outputStorePc stage box chunk) {target : Event}
    (hm : target ∈ events) (hTarget : target.pc ≠ outputStorePc stage box chunk)
    {n : Nat} (hN : s.sub + n < 4) :
    ∃ a bytes, events[n]? = some ⟨outputStorePc stage box chunk, .wr a bytes⟩ ∧
      a.elem = s.sub + n := by
  induction n generalizing s events visits with
  | zero =>
    cases hw with
    | stop => cases hm
    | tau ht _ => exact (not_tau_of_stops (decodedStoreStops stage box chunk hPc) ht).elim
    | last he =>
      obtain rfl := List.mem_singleton.mp hm
      exact (hTarget ((estep_source_pc he).trans hPc)).elim
    | ev he _ =>
      obtain ⟨a, bytes, hE, hElem, _⟩ := vectorElementStep stage box chunk hPc he
      exact ⟨a, bytes, congrArg some hE, hElem⟩
  | succ n ih =>
    cases hw with
    | stop => cases hm
    | tau ht _ => exact (not_tau_of_stops (decodedStoreStops stage box chunk hPc) ht).elim
    | last he =>
      obtain rfl := List.mem_singleton.mp hm
      exact (hTarget ((estep_source_pc he).trans hPc)).elim
    | ev he hw =>
      obtain ⟨a, bytes, hE, hElem, hNext⟩ := vectorElementStep stage box chunk hPc he
      have hLen : (outputOperands stage box chunk).length = 4 := List.length_ofFn
      have hStep : s.sub + 1 < 4 := by omega
      rw [afterStore, hLen, ite_eq_left hStep] at hNext
      have hU : _ := congrArg TState.pc hNext
      have hSub : _ := congrArg TState.sub hNext
      change _ = s.pc at hU
      change _ = s.sub + 1 at hSub
      have hm' := (List.mem_cons.mp hm).resolve_left (fun heq => hTarget (by rw [heq, hE]))
      obtain ⟨b, data, hW, hJ⟩ := ih hw (hU.trans hPc) hm' (by omega)
      exact ⟨b, data, hW, by omega⟩

/-- A correction lane's observed ready arrival guarantees that it staged every column of
each subbox in that stage. The element's payload is the recorded ordinary store word. -/
theorem stageElementWrittenBeforeReady {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g ready : Nat} {stage : Fin 2} (h : CorrectionReady X (g,ready) stage)
    (box : Fin 4) (column : Fin 32) :
    ∃ write data, StageStagingWrite X (g,write) stage
        (outputElementAccess l g stage box column.val (rowOf l g)) data ∧
      TraceBefore X (g,write) (g,ready) := by
  let chunk : Fin 8 := ⟨column.val / 4, by have := column.isLt; omega⟩
  let n := column.val % 4
  let target : Event := ⟨publishPc stage, .arrive (Epilogue.readyLoc l g stage) 0 1 true .cta⟩
  have he : X.get (g,ready) = some target := h.decoded hp hX
  have hWarp := (CorrectionReady.ofActualArrival hp hX stage he).2
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hBounds (c : Fin 8) : 7755 < outputStorePc stage box c ∧
      outputStorePc stage box c < publishPc stage := by
    fin_cases stage <;> fin_cases box <;> fin_cases c <;> decide
  have hLate : 7754 < target.pc := by
    change 7754 < publishPc stage
    have := hBounds chunk
    omega
  obtain ⟨s, o, _, hAt, _, _, _, _, _, _, hRun, hIndex⟩ :=
    correctionEntryBeforeEvent hp hX (g := g) hg hWarp.1 hWarp.2 he (.inl hLate)
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun hRun
  have hTarget : target ∈ (X.tr g).drop 9 := by
    apply List.mem_of_getElem? (i := ready - 9)
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  have hBefore : BeforeVector stage (outputStorePc stage box chunk) s := by
    have := (hBounds chunk).1
    exact .inl (by rw [hAt.1]; omega)
  obtain ⟨t, before, rest, marks, hTrace, hPc, hSub, hTail, hMember⟩ :=
    cutAtVector stage box chunk hWalk hAt.1.ge (by rw [hAt.1]; decide)
      (by rw [hAt.2.1]; decide) (SetupScratch.clear hAt.2.1 hAt.2.2.1)
      hBefore (fun he => by have := (hBounds chunk).1; rw [hAt.1] at he; omega) hTarget rfl
  have hNe : target.pc ≠ outputStorePc stage box chunk := by
    change publishPc stage ≠ outputStorePc stage box chunk
    exact (Nat.ne_of_lt (hBounds chunk).2).symm
  have hN : t.sub + n < 4 := by rw [hSub, Nat.zero_add]; exact Nat.mod_lt _ (by decide)
  obtain ⟨a, data, hWrite, hElem⟩ := vectorPrefixElement stage box chunk hTail hPc hMember hNe hN
  let writer := 9 + before.length + n
  have hGet : X.get (g,writer) = some ⟨outputStorePc stage box chunk, .wr a data⟩ := by
    have hIndex : ((X.tr g).drop 9)[before.length + n]? =
        some ⟨outputStorePc stage box chunk, .wr a data⟩ := by
      rw [hTrace, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact hWrite
    rw [List.getElem?_drop, ← Nat.add_assoc] at hIndex
    exact hIndex
  obtain ⟨elem, hA⟩ := stagingWriteElement hp hX stage box chunk hGet
  rw [hA, hSub, Nat.zero_add] at hElem
  change (4 * chunk.val + elem.val) % 4 = n at hElem
  have hCol : 4 * chunk.val + elem.val = column.val := by
    have := elem.isLt
    have hChunk : chunk.val = column.val / 4 := rfl
    have hMod : n = column.val % 4 := rfl
    omega
  rw [hCol] at hA
  subst a
  have hObs := StageStagingWrite.ofEvent box chunk hGet
  obtain ⟨fence, hf, _, hSource⟩ := h.stagingBeforeFence hp hX
  exact ⟨writer, data, hObs, (hSource hObs).trans hf⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
