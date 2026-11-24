-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionAlignedTensor
import Kernels.TmlFa4Fwd.Proof.CorrectionLinearPrefix
import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixAccumulator
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleBranch
import Kernels.TmlFa4Fwd.Proof.CorrectionTmemStores
import Lemmas.Flow.Final
public import Lemmas.Flow.WarpUniform
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open _root_.PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

/-- The static label of a Tensor Memory event, with operands erased. -/
private def tensorLabel (e : Event) : Option (Nat × Fin 4) :=
  (correctionTensorOperation e.kind).map (e.pc, ·)

private def straightLocal (op : Op) : Bool :=
  op.isLocal && match op with | .bra .. | .brx .. => false | _ => true

private def labelsAt (pc : Nat) : Op → List (Nat × Fin 4)
  | .tcLd .. => [(pc, 0), (pc, 1)]
  | .tcSt .. => [(pc, 2)]
  | .tcWaitSt => [(pc, 3)]
  | _ => []

private def bodyLo (stage : Fin 2) : Nat := rescaleLoadPc stage 0
private def bodyHi (stage : Fin 2) : Nat := rescaleSkipPc stage

private def bodyAudit (pc : Nat) (i : Instr) : Bool :=
  straightLocal i.op ||
    (i.guard.isNone && match i.op with
      | .tcLd _ _ .s32x32b none => Assumptions.all.any (·.tcLdWait pc)
      | .tcSt _ _ .s32x32b => !(Assumptions.all.any (·.tcStWaitLd pc))
      | .tcWaitSt => true
      | _ => false)

set_option maxRecDepth 100000 in
private theorem bodyAuditAt (stage : Fin 2) {pc : Nat} {i : Instr}
    (hLo : bodyLo stage ≤ pc) (hHi : pc < bodyHi stage)
    (hc : kernel.code[pc]? = some i) : bodyAudit pc i = true := by
  let lo := bodyLo stage
  let code := ((kernel.code.drop lo).take (bodyHi stage - lo)).zipIdx lo
  have hAll : code.all (fun (ins, site) => bodyAudit site ins) = true := by
    fin_cases stage <;> decide +kernel
  apply List.all_eq_true.mp hAll (i,pc)
  apply List.mem_of_getElem? (i := pc - lo)
  have hp : lo ≤ pc := hLo
  have hq : pc < bodyHi stage := hHi
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hp, hc]
  rfl

private def decodedLabels (pc : Nat) : List (Nat × Fin 4) :=
  ((kernel.code[pc]?).map (fun i => labelsAt pc i.op)).getD []

private def bodyLabels (hi : Nat) (t : TState) : List (Nat × Fin 4) :=
  if t.pc < hi then (decodedLabels t.pc).drop t.sub ++
    (((kernel.code.drop (t.pc + 1)).take (hi - (t.pc + 1))).zipIdx (t.pc + 1)).flatMap
      (fun (i,pc) => labelsAt pc i.op)
  else []

private theorem labelsNext {hi : Nat} {s u : TState} (hs : s.pc < hi) (hPc : u.pc = s.pc + 1)
    (hSub : u.sub = 0) {i : Instr} (hc : kernel.code[s.pc]? = some i) :
    bodyLabels hi s = (labelsAt s.pc i.op).drop s.sub ++ bodyLabels hi u := by
  unfold bodyLabels
  rw [ite_eq_left hs, hSub, hPc, List.drop_zero]
  have hDec : decodedLabels s.pc = labelsAt s.pc i.op := by simp [decodedLabels, hc]
  rw [hDec]
  by_cases hu : s.pc + 1 < hi
  · rw [ite_eq_left hu]
    cases h : kernel.code[s.pc+1]? with
    | none =>
      have hLen := List.getElem?_eq_none_iff.mp h
      simp [decodedLabels, h, List.drop_eq_nil_of_le hLen,
        List.drop_eq_nil_of_le (show kernel.code.length ≤ s.pc+1+1 by omega)]
    | some j =>
      obtain ⟨hLen,hj⟩ := List.getElem?_eq_some_iff.mp h
      have hDrop := List.drop_eq_getElem_cons hLen
      rw [hj] at hDrop
      have hDec' : decodedLabels (s.pc+1) = labelsAt (s.pc+1) j.op := by simp [decodedLabels,h]
      rw [hDec', show hi-(s.pc+1) = hi-(s.pc+1+1)+1 by omega,
        hDrop, List.take_succ_cons, List.zipIdx_cons, List.flatMap_cons]
  · rw [ite_eq_right hu, show hi - (s.pc + 1) = 0 by omega]
    simp

private theorem labelsSame {hi : Nat} {s u : TState} (hPc : u.pc = s.pc)
    (hS : s.sub = 0) (hU : u.sub = 1) (hs : s.pc < hi) {i : Instr}
    (hc : kernel.code[s.pc]? = some i) (hLabels : labelsAt s.pc i.op = [(s.pc,0),(s.pc,1)]) :
    bodyLabels hi s = (s.pc,0) :: bodyLabels hi u := by
  simp [bodyLabels, decodedLabels, hPc, hS, hU, hs, hc, hLabels]

private theorem rescaleLoadEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {ds : List Nat} {ta : Nat}
    (hHook : Assumptions.all.any (·.tcLdWait s.pc) = true) (hs : s.sub = 0)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.tcLd ds ta .s32x32b none))
      e (some u)) : tensorLabel e = some (s.pc,0) ∧ u.pc = s.pc ∧ u.sub = 1 := by
  have hShape : ∀ sh, TcShape.s32x32b ≠ .packed16 sh := by intro _ h; cases h
  simp only [eventTmpl, tcLdTmpl, hHook, hs, ↓reduceIte, tcTmpl_tcLd_none hShape] at hf
  cases ha : readBits l g s 32 (.reg ta) with
  | error f =>
    simp [ofExec, ha, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp [Tmpl.thenWaitLd, Fires] at hf
  | ok v =>
    simp [ofExec, ha, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp only [Tmpl.thenWaitLd, Fires, reduceCtorEq, and_false] at hf
    obtain ⟨_, _, rfl, hu⟩ := hf
    obtain rfl := Option.some.inj hu
    exact ⟨rfl,rfl,rfl⟩

private theorem rescaleStoreEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {ta : Nat} {ss : List Opnd}
    (hHook : Assumptions.all.any (·.tcStWaitLd s.pc) = false)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.tcSt ta ss .s32x32b))
      e (some u)) : tensorLabel e = some (s.pc,2) ∧ u = next s := by
  rw [eventTmpl_tcSt_noWait hHook] at hf
  cases ha : readBits l g s 32 (.reg ta) <;>
  cases hv : ss.mapM (readValue l g s 32) <;>
    simp only [tcTmpl, ofExec, ha, hv, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf <;>
    split_ifs at hf <;> simp only [Fires, reduceCtorEq, and_false] at hf
  obtain ⟨rfl,hu⟩ := hf
  exact ⟨rfl,Option.some.inj hu⟩

private def BodySub (s : TState) : Prop :=
  s.sub = 0 ∨ s.sub = 1 ∧ ∃ ds ta,
    kernel.code[s.pc]? = some ⟨none, .tcLd ds ta .s32x32b none⟩

private theorem tauBodySlot {l : Launch} {g : Nat} {s u : TState}
    (stage : Fin 2) (hLo : bodyLo stage ≤ s.pc) (hHi : s.pc < bodyHi stage)
    (hs : BodySub s) (ht : Tau kernel Assumptions.all l g s u) :
    u.pc = s.pc + 1 ∧ BodySub u ∧ bodyLabels (bodyHi stage) s = bodyLabels (bodyHi stage) u := by
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by
    have hMin : 8012 ≤ s.pc := by
      have h : 8012 ≤ bodyLo stage := by fin_cases stage <;> decide
      omega
    simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  obtain ⟨i, hCode, _, hTau⟩ := correctionTauFrame hOff ht
  have hAudit := bodyAuditAt stage hLo hHi hCode
  have hDataNonLocal (hn : straightLocal i.op = false) : i.guard = none := by
    have := (Bool.and_eq_true_iff.mp (by simpa only [bodyAudit, hn, Bool.false_or] using
      hAudit)).1
    exact Option.isNone_iff_eq_none.mp this
  have hStatic (hLocal : straightLocal i.op = true) : labelsAt s.pc i.op = [] := by
    cases ho : i.op <;> simp_all [labelsAt, straightLocal, Op.isLocal]
  have hPos (hAdvance : u.pc = s.pc + 1) (hZero : u.sub = 0)
      (hLabels : labelsAt s.pc i.op = []) :
      u.pc = s.pc + 1 ∧ BodySub u ∧ bodyLabels (bodyHi stage) s =
        bodyLabels (bodyHi stage) u := by
    refine ⟨hAdvance, .inl hZero, ?_⟩
    simpa [hLabels] using labelsNext hHi hAdvance hZero hCode
  rcases hTau with ⟨rfl, hGuard⟩ | ⟨_, hIsLocal, hFrame⟩
  · cases hb : straightLocal i.op
    · have hG := hDataNonLocal hb
      simp [hG, guardHolds, pure, Except.pure] at hGuard
    · exact hPos rfl rfl (hStatic hb)
  · have hActual : straightLocal i.op = true := by
      have hCheck (hFail : straightLocal i.op = false) : False := by
        have hAllowed : (match i.op with
          | .tcLd _ _ .s32x32b none => Assumptions.all.any (·.tcLdWait s.pc)
          | .tcSt _ _ .s32x32b => !(Assumptions.all.any (·.tcStWaitLd s.pc))
          | .tcWaitSt => true
          | _ => false) = true := by
          simpa only [bodyAudit, hFail, Bool.false_or, Bool.and_eq_true,
            hDataNonLocal hFail, Option.isNone_none, true_and] using hAudit
        split at hAllowed <;> simp_all [Op.isLocal]
      cases hb : straightLocal i.op
      · exact (hCheck hb).elim
      · rfl
    have hAdv : u.pc = s.pc + 1 := by
      have hP := hFrame.pc
      cases ho : i.op <;> simp_all [nextPc, BrxTarget, straightLocal]
    have hz : s.sub = 0 := by
      rcases hs with h | ⟨_, ds, ta, hLd⟩
      · exact h
      · obtain rfl := Option.some.inj (hCode.symm.trans hLd)
        cases hIsLocal
    exact hPos hAdv (hFrame.sub.trans hz) (hStatic hActual)

private theorem tensorBodySlot {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (hLo : bodyLo stage ≤ s.pc) (hHi : s.pc < bodyHi stage)
    (hSub : BodySub s) (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ label, tensorLabel e = some label ∧ s.pc ≤ u.pc ∧ u.pc ≤ s.pc + 1 ∧ BodySub u ∧
      bodyLabels (bodyHi stage) s = label :: bodyLabels (bodyHi stage) u := by
  obtain ⟨i, hCode, hNotLocal, hf⟩ := estep_event_source he
  have hAudit := bodyAuditAt stage hLo hHi hCode
  have hAllowed := Bool.and_eq_true_iff.mp (by
    simpa only [bodyAudit, straightLocal, hNotLocal, Bool.false_and, Bool.false_or] using hAudit)
  have hGuard : i.guard = none := Option.isNone_iff_eq_none.mp hAllowed.1
  have hSubZero (hNotLd : ∀ ds ta, i.op ≠ .tcLd ds ta .s32x32b none) : s.sub = 0 := by
    rcases hSub with hz | ⟨_, ds, ta, hLd⟩
    · exact hz
    · exact (hNotLd ds ta (congrArg Instr.op (Option.some.inj (hCode.symm.trans hLd)))).elim
  let check := hAllowed.2
  change (match i.op with
      | .tcLd _ _ .s32x32b none => Assumptions.all.any (·.tcLdWait s.pc)
      | .tcSt _ _ .s32x32b => !(Assumptions.all.any (·.tcStWaitLd s.pc))
      | .tcWaitSt => true
      | _ => false) = true at check
  split at check
  next ds ta hOp =>
    rw [hOp] at hf
    by_cases hz : s.sub = 0
    · obtain ⟨he, hp, hu⟩ := rescaleLoadEvent check hz hf
      have hCode' : kernel.code[u.pc]? = some ⟨none, .tcLd ds ta .s32x32b none⟩ := by
        rw [hp, hCode, ← hOp, ← hGuard]
      exact ⟨_, he, by omega, by omega, .inr ⟨hu, ds, ta, hCode'⟩,
        labelsSame hp hz hu hHi hCode (by simp [hOp, labelsAt])⟩
    · obtain ⟨rfl, rfl⟩ := fires_tcLd_wait check hz hf
      have hs : s.sub = 1 := hSub.elim (fun h => (hz h).elim) And.left
      refine ⟨(s.pc,1), rfl, by simp [next], by simp [next], .inl rfl, ?_⟩
      simpa [hOp, labelsAt, hs] using labelsNext hHi (u := {next s with sub := 0}) rfl rfl hCode
  next ta ss hOp =>
    rw [hOp] at hf
    obtain ⟨hEvent,rfl⟩ := rescaleStoreEvent (by simpa using check) hf
    have hz := hSubZero (by intros; simp [hOp])
    refine ⟨(s.pc,2), hEvent, by simp [next], by simp [next], .inl hz, ?_⟩
    simpa [hOp, labelsAt, hz] using labelsNext hHi (u := next s) rfl hz hCode
  next hOp =>
    rw [hOp] at hf
    obtain ⟨rfl,rfl⟩ := fires_tcWaitSt hf
    have hz := hSubZero (by intros; simp [hOp])
    refine ⟨(s.pc,3), rfl, by simp [next], by simp [next], .inl hz, ?_⟩
    simpa [hOp, labelsAt, hz] using labelsNext hHi (u := next s) rfl hz hCode
  next => contradiction

@[no_expose] def visitsTensorLabels (hi : Nat) (vs : List Visit) : List (Nat × Fin 4) :=
  ((vs.takeWhile (fun v => v.pc < hi)).filterMap Visit.ev).filterMap tensorLabel

private theorem visitsTensorCons {l : Launch} {g : Nat} {s : TState} {v : Option Event}
    {vs : List Visit} {hi : Nat} (h : s.pc < hi) :
    visitsTensorLabels hi (visit kernel l g s v :: vs) =
      (v.bind tensorLabel).toList ++ visitsTensorLabels hi vs := by
  cases v with
  | none => simp [visitsTensorLabels, h, List.filterMap_cons]
  | some e => cases hLabel : tensorLabel e <;> simp [visitsTensorLabels, h, hLabel]

@[no_expose] def rescaleSchedule (stage : Fin 2) : List (Nat × Fin 4) :=
  ((List.finRange 8).flatMap fun chunk =>
    [(rescaleLoadPc stage chunk,0), (rescaleLoadPc stage chunk,1),
      (rescaleStorePc stage chunk,2)]) ++ [(bodyHi stage - 1,3)]

set_option maxRecDepth 100000 in
private theorem rescaleScheduleAt (stage : Fin 2) {s : TState} (hp : s.pc = bodyLo stage)
    (hs : s.sub = 0) : bodyLabels (bodyHi stage) s = rescaleSchedule stage := by
  simp only [bodyLabels,hp,hs]
  fin_cases stage <;> decide +kernel

private inductive FinalInterval where
  | stage (stage : Fin 2)
  | complete

private def finalLo : FinalInterval → Nat
  | .stage stage => 8479 + 296 * stage.val
  | .complete => 8447

private def finalHi : FinalInterval → Nat
  | .stage stage => if stage = 0 then 8769 else 9044
  | .complete => 9044

private def finalLabelsAt (pc : Nat) : Op → List (Nat × Fin 4)
  | .tcLd .. => [(pc,0)]
  | .tcWaitLd => [(pc,1)]
  | _ => []

private def finalLabels (hi pc : Nat) : List (Nat × Fin 4) :=
  (((kernel.code.drop pc).take (hi - pc)).zipIdx pc).flatMap
    (fun (i,site) => finalLabelsAt site i.op)

private def finalAudit (band : FinalInterval) (pc : Nat) (i : Instr) : Bool :=
  match i.op with
  | .tcLd _ _ .s32x32b none => i.guard.isNone && !(Assumptions.all.any (·.tcLdWait pc))
  | .tcWaitLd => i.guard.isNone
  | .bra target _ => decide (finalLo band ≤ target ∧
      finalLabels (finalHi band) pc = finalLabels (finalHi band) target)
  | op => !tcDataOp op && (straightLocal op || !op.isLocal && Epilogue.ordinaryEvent op)

set_option maxRecDepth 100000 in
private theorem finalAuditAt (stage : FinalInterval) {pc : Nat} {i : Instr}
    (hLo : finalLo stage ≤ pc) (hHi : pc < finalHi stage)
    (hc : kernel.code[pc]? = some i) : finalAudit stage pc i = true := by
  let lo := finalLo stage
  let code := ((kernel.code.drop lo).take (finalHi stage - lo)).zipIdx lo
  have hAll : code.all (fun (ins,site) => finalAudit stage site ins) = true := by
    cases stage with
    | stage k => fin_cases k <;> decide +kernel
    | complete => decide +kernel
  apply List.all_eq_true.mp hAll (i,pc)
  apply List.mem_of_getElem? (i := pc - lo)
  have hp : lo ≤ pc := hLo
  have hq : pc < finalHi stage := hHi
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hp, hc]
  rfl

private theorem finalLabelsNext {hi pc : Nat} (hs : pc < hi)
    {i : Instr} (hc : kernel.code[pc]? = some i) :
    finalLabels hi pc = finalLabelsAt pc i.op ++ finalLabels hi (pc+1) := by
  obtain ⟨hLen,hI⟩ := List.getElem?_eq_some_iff.mp hc
  have hDrop := List.drop_eq_getElem_cons hLen
  rw [hI] at hDrop
  unfold finalLabels
  rw [show hi-pc = hi-(pc+1)+1 by omega, hDrop, List.take_succ_cons, List.zipIdx_cons,
    List.flatMap_cons]

private theorem finalNoTensor {op : Op} (h : tcDataOp op = false) (pc : Nat) :
    finalLabelsAt pc op = [] := by cases op <;> simp_all [finalLabelsAt, tcDataOp]

private theorem finalLocalSlots {l : Launch} {g : Nat} {s u : TState}
    (stage : FinalInterval) (hLo : finalLo stage ≤ s.pc) (hHi : s.pc < finalHi stage)
    (ht : Tau kernel Assumptions.all l g s u) :
    finalLo stage ≤ u.pc ∧ finalLabels (finalHi stage) s.pc = finalLabels (finalHi stage) u.pc := by
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by
    have hStart : 8447 ≤ finalLo stage := by
      cases stage with
      | stage k => change 8447 ≤ 8479 + 296 * k.val; omega
      | complete => decide
    have hMin := hStart.trans hLo
    simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  obtain ⟨i, hCode, _, hTau⟩ := correctionTauFrame hOff ht
  have hAudit := finalAuditAt stage hLo hHi hCode
  have advance (hp : u.pc = s.pc + 1) (hNone : finalLabelsAt s.pc i.op = []) :
      finalLo stage ≤ u.pc ∧
        finalLabels (finalHi stage) s.pc = finalLabels (finalHi stage) u.pc :=
    ⟨by omega, by rw [finalLabelsNext hHi hCode, hp, hNone, List.nil_append]⟩
  rcases hTau with ⟨rfl,hGuard⟩ | ⟨_,hIsLocal,hFrame⟩
  · have hNot : i.guard ≠ none := by rintro hg; simp [hg, guardHolds, pure, Except.pure] at hGuard
    apply advance rfl
    unfold finalAudit at hAudit
    split at hAudit
    · simp [Option.isNone_iff_eq_none, hNot] at hAudit
    · simp [Option.isNone_iff_eq_none, hNot] at hAudit
    · simp_all [finalLabelsAt]
    · exact finalNoTensor (by simpa only [Bool.not_eq_true'] using
        (Bool.and_eq_true_iff.mp hAudit).1) _
  · unfold finalAudit at hAudit
    split at hAudit
    · simp_all [Op.isLocal]
    · simp_all [Op.isLocal]
    next target aligned hop =>
      have hp : u.pc = target := by simpa [hop, nextPc, BrxTarget] using hFrame.pc
      rw [hp]
      exact of_decide_eq_true hAudit
    · have hCheck : straightLocal i.op = true ∧ tcDataOp i.op = false := by
        simpa [hIsLocal, and_comm] using hAudit
      refine advance ?_ (finalNoTensor hCheck.2 _)
      have hP := hFrame.pc
      cases ho : i.op <;> simp_all [nextPc, BrxTarget, straightLocal]

private theorem finalEventSlots {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : FinalInterval) (hLo : finalLo stage ≤ s.pc) (hHi : s.pc < finalHi stage)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    s.pc ≤ u.pc ∧ finalLabels (finalHi stage) s.pc =
      (tensorLabel e).toList ++ finalLabels (finalHi stage) u.pc := by
  obtain ⟨i, hCode, hNonlocal, hFire⟩ := estep_event_source he
  have hAudit := finalAuditAt stage hLo hHi hCode
  unfold finalAudit at hAudit
  split at hAudit
  next ds ta hop =>
    rw [hop] at hFire
    obtain ⟨_, values, _, rfl, rfl⟩ := fires_tcLd (by intro _ h; cases h) hFire
      (by simpa using (Bool.and_eq_true_iff.mp hAudit).2)
    have hPc := (setRegs_skel (next s) ds values).1
    refine ⟨by rw [hPc]; simp [next], ?_⟩
    rw [finalLabelsNext hHi hCode, hop, hPc]
    rfl
  next hop =>
    rw [hop, eventTmpl, tcTmpl] at hFire
    split at hFire
    · obtain rfl := hFire.1
      obtain rfl := Option.some.inj hFire.2
      refine ⟨by simp [next], ?_⟩
      rw [finalLabelsNext hHi hCode, hop]
      rfl
    · cases hFire.2
  next _ _ hop => simp [hop, Op.isLocal] at hNonlocal
  next =>
    have hSafe : tcDataOp i.op = false ∧ Epilogue.ordinaryEvent i.op = true := by
      simpa [straightLocal, hNonlocal] using hAudit
    have hEmpty : tensorLabel e = none := by
      by_contra hh
      have hData : isTcData e = true := by
        rcases e with ⟨pc,k⟩
        cases k <;> try (exfalso; exact hh rfl)
        rename_i a
        cases a <;> first | rfl | exact (hh rfl).elim
      have := fires_tcData_op hFire hData
      rw [hSafe.1] at this
      cases this
    obtain hp | hp := callbackFrame_fires (Epilogue.ordinaryEventFrame hSafe.2) hFire
    · exact ⟨hp.symm.le, by simp [hp,hEmpty]⟩
    · refine ⟨by omega, ?_⟩
      rw [finalLabelsNext hHi hCode, finalNoTensor hSafe.1, hp]
      simp [hEmpty]

variable {l : Launch} {g : Nat} {s : TState} {events : List Event} {visits : List Visit}

private theorem finalPrefixLabels (stage : FinalInterval)
    (hw : Walk kernel Assumptions.all l g s events visits) (hLo : finalLo stage ≤ s.pc) :
    List.IsPrefix (visitsTensorLabels (finalHi stage) visits) (finalLabels (finalHi stage) s.pc) ∧
      ((∃ v ∈ visits, finalHi stage ≤ v.pc) →
        visitsTensorLabels (finalHi stage) visits = finalLabels (finalHi stage) s.pc) := by
  induction hw with
  | stop =>
    simp [visitsTensorLabels, List.IsPrefix]
  | @tau t u _ vs ht _ ih =>
    by_cases hi : t.pc < finalHi stage
    · obtain ⟨hp,hEq⟩ := finalLocalSlots stage hLo hi ht
      obtain ⟨hPre,hComplete⟩ := ih hp
      rw [visitsTensorCons hi, hEq]
      refine ⟨hPre, fun hSeen => hComplete ?_⟩
      simpa [visit_pc, Nat.not_le_of_lt hi] using hSeen
    · have hLen : finalHi stage - t.pc = 0 := by omega
      simp [visitsTensorLabels, finalLabels, hi, hLen, List.IsPrefix]
  | @ev t u e _ vs he _ ih =>
    by_cases hi : t.pc < finalHi stage
    · obtain ⟨hp,hEq⟩ := finalEventSlots stage hLo hi he
      obtain ⟨⟨rest,hPre⟩, hComplete⟩ := ih (by omega)
      rw [visitsTensorCons hi, hEq, Option.bind_some]
      refine ⟨⟨rest, by rw [List.append_assoc, hPre]⟩, ?_⟩
      intro hSeen
      congr 1
      apply hComplete
      simpa [visit_pc, Nat.not_le_of_lt hi] using hSeen
    · have hLen : finalHi stage - t.pc = 0 := by omega
      simp [visitsTensorLabels, finalLabels, hi, hLen, List.IsPrefix]
  | @last t e he =>
    obtain ⟨_,_,hf⟩ := he
    have hEmpty : tensorLabel e = none := by
      rcases fires_none_ends hf with ⟨_, he⟩ | he <;>
        simp [tensorLabel, he, correctionTensorOperation]
    by_cases hi : t.pc < finalHi stage
    · rw [visitsTensorCons hi]
      simp [hEmpty, visit_pc, Nat.not_le_of_lt hi, List.IsPrefix, visitsTensorLabels]
    · have hLen : finalHi stage - t.pc = 0 := by omega
      simp [visitsTensorLabels, finalLabels, hi, hLen, List.IsPrefix]

@[no_expose] def correctionFinalStageSchedule (stage : Fin 2) : List (Nat × Fin 4) :=
  (List.finRange 16).flatMap fun chunk =>
    [(finalizeLoadPc stage chunk,0), (finalizeLoadPc stage chunk + 5,1)]

set_option maxRecDepth 100000 in
private theorem finalScheduleComplete :
    finalLabels (finalHi .complete) (finalLo .complete) =
      correctionFinalStageSchedule 0 ++ correctionFinalStageSchedule 1 := by decide +kernel

/-- From the correction rescale exit, the two final stages contribute their full fixed sequence
as far as the finite trace has executed. Waiting for either stage does not advance the sequence. -/
theorem correctionFinalizationSlots (hw : Walk kernel Assumptions.all l g s events visits)
    (hs : s.pc = 8447) :
    let slots := visitsTensorLabels 9044 visits
    let schedule := correctionFinalStageSchedule 0 ++ correctionFinalStageSchedule 1
    List.IsPrefix slots schedule ∧ ((∃ v ∈ visits, 9044 ≤ v.pc) → slots = schedule) := by
  have h := finalPrefixLabels .complete hw hs.ge
  rw [show s.pc = finalLo .complete from hs, finalScheduleComplete] at h
  exact h

/-- A trace's Tensor Memory labels, in their actual issue order. -/
@[no_expose] def correctionTensorLabels (events : List Event) : List (Nat × Fin 4) :=
  events.filterMap tensorLabel

private theorem rescaleBodyCutLabels (stage : Fin 2) (P : TState → Prop)
    (hw : Walk kernel Assumptions.all l g s events visits) (hLo : bodyLo stage ≤ s.pc)
    (hHi : s.pc ≤ bodyHi stage) (hSub : BodySub s) (hInv : P s)
    (hStep : ∀ {t u : TState} {e : Option Event}, bodyLo stage ≤ t.pc → t.pc < bodyHi stage →
      BodySub t → P t → WStep kernel Assumptions.all l g t e u → P u) :
    (List.IsPrefix (correctionTensorLabels events) (bodyLabels (bodyHi stage) s) ∧
      ∀ e ∈ events, bodyLo stage ≤ e.pc ∧ e.pc < bodyHi stage) ∨
      ∃ u pre tail rest, events = pre ++ tail ∧ u.pc = bodyHi stage ∧ BodySub u ∧ P u ∧
        correctionTensorLabels pre = bodyLabels (bodyHi stage) s ∧
        (∀ e ∈ pre, bodyLo stage ≤ e.pc ∧ e.pc < bodyHi stage) ∧
        Walk kernel Assumptions.all l g u tail rest := by
  have hCut {s : TState} {es : List Event} {vs : List Visit}
      (h : s.pc = bodyHi stage) (hs : BodySub s) (hP : P s)
      (hw : Walk kernel Assumptions.all l g s es vs) :
      ∃ u pre tail rest, es = pre ++ tail ∧ u.pc = bodyHi stage ∧ BodySub u ∧ P u ∧
        correctionTensorLabels pre = bodyLabels (bodyHi stage) s ∧
        (∀ e ∈ pre, bodyLo stage ≤ e.pc ∧ e.pc < bodyHi stage) ∧
        Walk kernel Assumptions.all l g u tail rest :=
    ⟨s, [], es, vs, rfl, h, hs, hP, by simp [bodyLabels,h,correctionTensorLabels], by simp, hw⟩
  induction hw with
  | stop => exact .inl ⟨⟨_, rfl⟩, by simp⟩
  | @tau t u es vs ht hw ih =>
    by_cases h : t.pc = bodyHi stage
    · exact .inr (hCut h hSub hInv (.tau ht hw))
    have hi : t.pc < bodyHi stage := by omega
    obtain ⟨hp,hs,hEq⟩ := tauBodySlot stage hLo hi hSub ht
    have hP := hStep hLo hi hSub hInv (.inl ⟨rfl,ht⟩)
    rw [hEq]
    exact ih (by omega) (by omega) hs hP
  | @ev t u e es vs he hw ih =>
    by_cases h : t.pc = bodyHi stage
    · exact .inr (hCut h hSub hInv (.ev he hw))
    have hi : t.pc < bodyHi stage := by omega
    obtain ⟨label,hLabel,hLow,hHigh,hs,hEq⟩ := tensorBodySlot stage hLo hi hSub he
    have hP := hStep hLo hi hSub hInv (.inr ⟨e,rfl,he⟩)
    have hSite : bodyLo stage ≤ e.pc ∧ e.pc < bodyHi stage := by
      rw [estep_source_pc he]
      exact ⟨hLo,hi⟩
    rcases ih (by omega) (by omega) hs hP with ⟨⟨suffix,hPrefix⟩,hSites⟩ |
      ⟨v,pre,tail,rest,hEs,hV,hSubV,hPV,hLabV,hSites,hWalk⟩
    · left
      refine ⟨⟨suffix,?_⟩, fun x hx => (List.mem_cons.mp hx).elim (· ▸ hSite) (hSites x)⟩
      simpa [correctionTensorLabels,hLabel,hEq,List.cons_append] using
        congrArg (List.cons label) hPrefix
    · right
      refine ⟨v,e::pre,tail,rest,?_,hV,hSubV,hPV,?_,?_,hWalk⟩
      · rw [hEs,List.cons_append]
      · rw [hEq]
        simpa [correctionTensorLabels,hLabel] using congrArg (List.cons label) hLabV
      · exact fun x hx => (List.mem_cons.mp hx).elim (· ▸ hSite) (hSites x)
  | @last t e he =>
    by_cases h : t.pc = bodyHi stage
    · exact .inr (hCut h hSub hInv (.last he))
    have hPc := estep_source_pc he
    obtain ⟨_,_,hf⟩ := he
    have hNone : tensorLabel e = none := by
      rcases fires_none_ends hf with ⟨_,he⟩ | he <;>
        simp [tensorLabel,he,correctionTensorOperation]
    left
    refine ⟨⟨bodyLabels (bodyHi stage) t, by simp [correctionTensorLabels,hNone]⟩, ?_⟩
    intro x hx
    obtain rfl := List.mem_singleton.mp hx
    rw [hPc]
    exact ⟨hLo, by omega⟩

private theorem bodySubAtEnd {s : TState} (stage : Fin 2)
    (hp : s.pc = bodyHi stage) (hs : BodySub s) : s.sub = 0 := by
  rcases hs with h | ⟨_,ds,ta,hc⟩
  · exact h
  · have ha : ∀ i, kernel.code[bodyHi stage]? = some i → i.op.isLocal = true := by
      have hAll : ((kernel.code[bodyHi stage]?).map (·.op.isLocal)).getD false = true := by
        fin_cases stage <;> decide +kernel
      intro i hi
      simpa [hi] using hAll
    rw [hp] at hc
    cases ha _ hc

/-- A finite rescale body either stays in its fixed TC prefix or returns at the exact stage
boundary after every element of that sequence. A supplied state frame holds at that boundary. -/
theorem correctionRescaleBodyDecompose (stage : Fin 2) (P : TState → Prop)
    (hw : Walk kernel Assumptions.all l g s events visits) (hPc : s.pc = rescaleLoadPc stage 0)
    (hSub : s.sub = 0) (hInv : P s)
    (hStep : ∀ {t u : TState} {e : Option Event},
      rescaleLoadPc stage 0 ≤ t.pc → t.pc < rescaleSkipPc stage →
      t.sub ≤ 1 → P t → WStep kernel Assumptions.all l g t e u → P u) :
    (List.IsPrefix (correctionTensorLabels events) (rescaleSchedule stage) ∧
      ∀ e ∈ events, rescaleLoadPc stage 0 ≤ e.pc ∧ e.pc < rescaleSkipPc stage) ∨
      ∃ u pre tail rest, events = pre ++ tail ∧ u.pc = rescaleSkipPc stage ∧ u.sub = 0 ∧ P u ∧
        correctionTensorLabels pre = rescaleSchedule stage ∧
        (∀ e ∈ pre, rescaleLoadPc stage 0 ≤ e.pc ∧ e.pc < rescaleSkipPc stage) ∧
        Walk kernel Assumptions.all l g u tail rest := by
  have hBound : s.pc ≤ bodyHi stage := by rw [hPc]; fin_cases stage <;> decide
  have hLower : bodyLo stage ≤ s.pc := hPc.symm ▸ Nat.le_refl _
  have h := rescaleBodyCutLabels stage P hw hLower hBound (.inl hSub) hInv
    (fun hLo hHi hs hInv hW =>
      hStep hLo hHi (hs.elim (fun h => by omega) (fun ⟨h,_⟩ => by omega)) hInv hW)
  rw [rescaleScheduleAt stage hPc hSub] at h
  exact h.elim Or.inl (fun ⟨u,pre,tail,rest,hE,hU,hs,hP,hLabels,hSites,hw⟩ =>
    .inr ⟨u,pre,tail,rest,hE,hU,bodySubAtEnd stage hU hs,hP,hLabels,hSites,hw⟩)

/-- The nonzero body preserves the accumulator and the seeded rescale counter. -/
theorem correctionRescaleBodyFrame {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (stage : Fin 2) (hLo : rescaleLoadPc stage 0 ≤ s.pc) (hHi : s.pc < rescaleSkipPc stage)
    (hSub : s.sub ≤ 1) (hAcc : s.acc = [])
    (hStep : WStep kernel Assumptions.all l g s e u) :
    u.acc = [] ∧ u.regs 7278 = s.regs 7278 := by
  have hLower : 8006 ≤ s.pc := by
    have h : 8006 ≤ rescaleLoadPc stage 0 := by fin_cases stage <;> decide
    omega
  have hUpper : s.pc < 8444 := by
    have h : rescaleSkipPc stage ≤ 8444 := by fin_cases stage <;> decide
    omega
  obtain ⟨_,_,hKeep⟩ := correctionLinearStep 3 hLower hUpper (by omega) hStep
  refine ⟨?_,hKeep⟩
  rcases hStep with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨_,_,_,⟨rfl,_⟩ | ⟨_,_,hFrame⟩⟩ := correctionTauFrame hOff ht
    · rfl
    · exact hFrame.acc.trans hAcc
  · obtain ⟨i,hc,hNonlocal,_⟩ := estep_event_source he
    have hCheck := bodyAuditAt stage hLo hHi hc
    have ha : (match i.op with
      | .tcLd _ _ .s32x32b none => Assumptions.all.any (·.tcLdWait s.pc)
      | .tcSt _ _ .s32x32b => !(Assumptions.all.any (·.tcStWaitLd s.pc))
      | .tcWaitSt => true
      | _ => false) = true := by
      simp only [bodyAudit, straightLocal, hNonlocal, Bool.false_and, Bool.false_or,
        Bool.and_eq_true] at hCheck
      exact hCheck.2
    apply correctionEventAccumulator hc ?_ ?_ hAcc he
    · split at ha <;> simp_all [correctionReturningOp, Softmax.scoreEventOp]
    · split at ha <;> simp_all

private theorem correctionTensorLabelSome {e : Event} :
    (tensorLabel e).isSome = isTcData e := by
  rcases e with ⟨p,kind⟩
  cases kind <;> try rfl
  rename_i tc
  cases tc <;> rfl

theorem correctionTensorLabelsNone {events : List Event}
    (h : ∀ e ∈ events, isTcData e = false) : correctionTensorLabels events = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro e he
  cases hx : tensorLabel e with
  | none => rfl
  | some _ => have hh := correctionTensorLabelSome (e := e); simp [hx, h e he] at hh

theorem correctionTensorLabelsAppend (left right : List Event) :
    correctionTensorLabels (left ++ right) =
      correctionTensorLabels left ++ correctionTensorLabels right := List.filterMap_append

/-- Under actual correction event classification, selects the exact site and operation at
the ordinal counted by the execution's Tensor Memory collective predicate. -/
theorem correctionTensorLabelAt {events : List Event} {i k : Nat} {e : Event}
    (hClass : ∀ x ∈ events, isTcColl x = isTcData x)
    (he : events[i]? = some e) (hColl : isTcColl e = true)
    (hOrd : (events.take i).countP isTcColl = k) :
    ∃ op, correctionTensorOperation e.kind = some op ∧
      (correctionTensorLabels events)[k]? = some (e.pc, op) := by
  have hData := hColl.symm.trans (hClass e (List.mem_of_getElem? he))
  have hSome : (correctionTensorOperation e.kind).isSome = true := by
    have h := correctionTensorLabelSome (e := e)
    rw [← hData] at h
    simpa [tensorLabel] using h
  obtain ⟨op,hOp⟩ := Option.isSome_iff_exists.mp hSome
  refine ⟨op,hOp,?_⟩
  rw [← hOrd]
  have hLabel : tensorLabel e = some (e.pc,op) := by simp [tensorLabel,hOp]
  clear hOrd k hData hSome hColl hOp
  unfold correctionTensorLabels
  induction events generalizing i with
  | nil => simp at he
  | cons x xs ih =>
    cases i with
    | zero =>
      have := Option.some.inj he
      subst e
      simp [hLabel]
    | succ i =>
      have hTail (y : Event) (hy : y ∈ xs) := hClass y (List.mem_cons_of_mem _ hy)
      have hNext := ih hTail (by simpa using he)
      cases hHead : tensorLabel x with
      | none =>
        have hNo : isTcColl x = false := by
          rw [hClass x List.mem_cons_self, ← correctionTensorLabelSome, hHead]
          rfl
        simpa [hHead,hNo] using hNext
      | some label =>
        have hYes : isTcColl x = true := by
          rw [hClass x List.mem_cons_self, ← correctionTensorLabelSome, hHead]
          rfl
        simpa [hHead,hYes] using hNext

set_option maxRecDepth 100000 in
private theorem finalizationSlotsFloor :
    (kernel.code.drop 9044).all (fun i => staysPastEvent 9044 i.op) = true := by kernel_rfl

private theorem finalizationVisitsAll (hw : Walk kernel Assumptions.all l g s events visits)
    (hNone : ∀ e ∈ events, 9044 ≤ e.pc → isTcData e = false) :
    visitsTensorLabels 9044 visits = correctionTensorLabels events := by
  have hCut (t : TState) {es : List Event} {vs : List Visit}
      (hw : Walk kernel Assumptions.all l g t es vs) (hp : 9044 ≤ t.pc)
      (h : ∀ e ∈ es, 9044 ≤ e.pc → isTcData e = false) : correctionTensorLabels es = [] :=
    correctionTensorLabelsNone (fun e he => h e he (eventTailEventsOfSegmentFloor
      finalizationSlotsFloor (fun site hLo hm => by
        simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hm
        omega) hw hp e he))
  induction hw with
  | stop => rfl
  | @tau t _ es vs ht hw ih =>
    by_cases hi : t.pc < 9044
    · rw [visitsTensorCons hi]
      exact ih hNone
    · rw [hCut t (.tau ht hw) (Nat.le_of_not_gt hi) hNone]
      simp [visitsTensorLabels, hi]
  | @ev t _ e es vs he hw ih =>
    by_cases hi : t.pc < 9044
    · rw [visitsTensorCons hi, ih (fun x hx => hNone x (List.mem_cons_of_mem _ hx))]
      cases hl : tensorLabel e <;> simp [correctionTensorLabels, hl]
    · rw [hCut t (.ev he hw) (Nat.le_of_not_gt hi) hNone]
      simp [visitsTensorLabels, hi]
  | @last t e he =>
    by_cases hi : t.pc < 9044
    · rw [visitsTensorCons hi]
      cases hl : tensorLabel e <;> simp [correctionTensorLabels, hl, visitsTensorLabels]
    · rw [hCut t (.last he) (Nat.le_of_not_gt hi) hNone]
      simp [visitsTensorLabels, hi]

/-- Finalization's ordered TC schedule covers the entire data trace of the suffix whenever
the lane has no further data events after its final load wait. -/
theorem correctionFinalizationTraceLabels (hw : Walk kernel Assumptions.all l g s events visits)
    (hs : s.pc = 8447) (hNone : ∀ e ∈ events, 9044 ≤ e.pc → isTcData e = false) :
    List.IsPrefix (correctionTensorLabels events)
      (correctionFinalStageSchedule 0 ++ correctionFinalStageSchedule 1) := by
  rw [← finalizationVisitsAll hw hNone]
  exact (correctionFinalizationSlots hw hs).1

end
end PTX.Kernels.TmlFa4Fwd.Thread
