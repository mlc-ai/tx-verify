-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.LoaderDrainPoll
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
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Kernels.TmlFa4Fwd.Flow.Code.Part054
import Kernels.TmlFa4Fwd.Flow.Code.Part078
import Kernels.TmlFa4Fwd.Flow.Code.Part080
import Kernels.TmlFa4Fwd.Flow.Code.Part081
import Kernels.TmlFa4Fwd.Flow.Code.Part103
import Lemmas.Flow.ContinuingEvent
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Loader (DrainWaitSite LoaderWaitCode)

private inductive ReadyMode
  | finished
  | known (bit : Bool) (reg : Option Nat)
  | live (pending : Bool)
  | tested (repeated : Bool)
  deriving DecidableEq

private def readySite (repeated : Bool) : DrainWaitSite :=
  if repeated then ⟨5181, 9755, 3965, 7250⟩ else ⟨3498, 9752, 2771, 2770⟩

private def readyMode (pc : Nat) : ReadyMode :=
  if 6654 ≤ pc then .finished
  else if pc = 3499 then .tested false
  else if pc = 5182 then .tested true
  else if 3425 ≤ pc ∧ pc ≤ 3500 then .known false (some 2770)
  else if pc ≤ 3424 then .known false none
  else if pc = 5028 ∨ pc = 5029 then .known true (some 7253)
  else if pc ≤ 5029 then .known true none
  else .live (decide (5184 ≤ pc ∧ pc ≤ 6648))

private def readyModeHolds (s : TState) (bit : Bool) : ReadyMode → Prop
  | .finished => True
  | .known value reg => bit = value ∧ ∀ r ∈ reg.toList, s.regs r = some (b32 value.toNat)
  | .live pending => s.regs 7250 = some (b32 (xor bit pending).toNat)
  | .tested repeated => ∃ ok, s.regs (readySite repeated).result = some (.pred ok) ∧
      if repeated then s.regs 7250 = some (b32 (xor bit ok).toNat)
      else s.regs 2770 = some (b32 0) ∧ bit = ok

private def readyPhaseEdge (src dst : Nat) : Bool :=
  decide ((3103 ≤ src → 3103 ≤ dst) ∧
    (readyMode src = readyMode dst ∨ readyMode dst = .finished))

private def readyModeRegs (pc : Nat) : List Nat :=
  match readyMode pc with
  | .finished | .tested _ => []
  | .known _ reg => reg.toList
  | .live _ => [7250]

private def readyNormal (pc : Nat) : Prop := pc ∉ [3424, 3498, 3499, 5027, 5029, 5181, 5182, 6648]

private instance (pc : Nat) : Decidable (readyNormal pc) :=
  inferInstanceAs (Decidable (pc ∉ [3424, 3498, 3499, 5027, 5029, 5181, 5182, 6648]))

private def readyPhaseCheck (pc : Nat) (ins : Instr) : Bool :=
  (ins.op.isLocal || Epilogue.ordinaryEvent ins.op) &&
    (!decide (readyNormal pc) ||
      ((readyModeRegs pc).all
          (fun r => !((writesRegs ins.op ++ scoreEventWrites ins.op).contains r)) &&
        match ins.op with
        | .bra dst _ => readyPhaseEdge pc dst &&
            (ins.guard.isNone || readyPhaseEdge pc (pc + 1))
        | .brx .. => false
        | _ => readyPhaseEdge pc (pc + 1)))

private theorem readyPhaseCheckAt {pc : Nat} {ins : Instr}
    (hc : kernel.code[pc]? = some ins) : readyPhaseCheck pc ins = true := by
  have hAll : (kernel.code.zipIdx 0).all (fun (ins,pc) => readyPhaseCheck pc ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  exact List.all_eq_true.mp hAll (ins,pc) (List.mem_zipIdx_iff_getElem?.mpr hc)

private theorem readyPhaseCheckNormal {pc : Nat} {ins : Instr}
    (hc : kernel.code[pc]? = some ins) (hn : readyNormal pc) :
    (readyModeRegs pc).all
        (fun r => !((writesRegs ins.op ++ scoreEventWrites ins.op).contains r)) = true ∧
      (match ins.op with
        | .bra dst _ => readyPhaseEdge pc dst &&
            (ins.guard.isNone || readyPhaseEdge pc (pc + 1))
        | .brx .. => false
        | _ => readyPhaseEdge pc (pc + 1)) = true := by
  have h := (Bool.and_eq_true_iff.mp (readyPhaseCheckAt hc)).2
  simpa only [hn, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] using h

private theorem readyPhaseCheckSegment {pc : Nat} {seg : SegMatch CuteSlot}
    (hSite : pc ∈ Assumptions.swExp2Sites) (hSeg : cuteExp2.matchAt kernel pc = some seg) :
    readyPhaseEdge pc seg.stop = true ∧
      (readyModeRegs pc).all (fun r => !(scoreSegmentWrites seg).contains r) = true := by
  have hAll : Assumptions.swExp2Sites.all (fun i => match cuteExp2.matchAt kernel i with
    | some seg => readyPhaseEdge i seg.stop &&
        (readyModeRegs i).all (fun r => !(scoreSegmentWrites seg).contains r)
    | none => false) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAll _ hSite
  rw [hSeg] at h
  exact Bool.and_eq_true_iff.mp h


private structure ReadyState (s : TState) (bit : Bool) : Prop where
  role : 3103 ≤ s.pc
  shape : s.pc < 6654 → s.sub ≤ 3
  mode : readyModeHolds s bit (readyMode s.pc)

private theorem readyNormalNotTest {pc : Nat} (hn : readyNormal pc) (b : Bool) :
    readyMode pc ≠ .tested b := by
  have hTail : pc ≠ 3499 ∧ pc ≠ 5182 := by
    have h := hn
    simp [readyNormal] at h
    exact ⟨h.2.2.1, h.2.2.2.2.2.2.1⟩
  unfold readyMode
  simp only [hTail.1, hTail.2, ↓reduceIte]
  split
  · intro h
    cases h
  · split
    · intro h
      cases h
    · split
      · intro h
        cases h
      · split
        · intro h
          cases h
        · split <;> intro h <;> cases h

private theorem keepReadyMode {s u : TState} {bit : Bool} (hState : ReadyState s bit)
    (hn : readyNormal s.pc) (hEdge : readyPhaseEdge s.pc u.pc = true)
    (hSub : u.pc < 6654 → u.sub ≤ 3)
    (hKeep : ∀ r ∈ readyModeRegs s.pc, u.regs r = s.regs r) :
    ReadyState u bit := by
  obtain ⟨hRole, hAlt⟩ := of_decide_eq_true hEdge
  refine ⟨hRole hState.role, hSub, ?_⟩
  rcases hAlt with hMode | hMode
  · rw [← hMode]
    have h := hState.mode
    cases hSrc : readyMode s.pc <;> rw [hSrc] at h
    · trivial
    · obtain ⟨hq, hFacts⟩ := h
      exact ⟨hq, fun r hr => (hKeep r (by simpa only [readyModeRegs, hSrc] using hr)).trans
        (hFacts r hr)⟩
    · have hR := hKeep 7250 (by simp [readyModeRegs, hSrc])
      change s.regs 7250 = _ at h
      change u.regs 7250 = _
      exact hR.trans h
    · exact (readyNormalNotTest hn _ hSrc).elim
  · rw [hMode]
    trivial

private theorem readyPhaseTau {l : Launch} {g : Nat} {s u : TState} {bit : Bool}
    (hState : ReadyState s bit) (hn : readyNormal s.pc)
    (ht : Tau kernel Assumptions.all l g s u) : ReadyState u bit := by
  obtain ⟨ins, hc, _, hExec⟩ := tauScoreSource ht
  obtain ⟨hRegs, hEdge⟩ := readyPhaseCheckNormal hc hn
  have hWithin (hS : u.pc < 6654)
      (hSrc : u.pc = s.pc ∨ u.pc = s.pc + 1 ∨ readyPhaseEdge s.pc u.pc = true) :
      s.pc < 6654 := by
    rcases hSrc with hp | hp | hp
    · omega
    · omega
    · have hMode : readyMode u.pc ≠ .finished := by
        simp only [readyMode, Nat.not_le_of_gt hS, ↓reduceIte]
        split_ifs <;> intro h <;> cases h
      have hSame := (of_decide_eq_true hp).2.resolve_right hMode
      by_contra! h
      simp only [readyMode, h, ↓reduceIte] at hSame
      exact hMode hSame.symm
  rcases hExec with ⟨rfl, hg⟩ | ⟨_, _, he⟩
  · have hNext : readyPhaseEdge s.pc (s.pc + 1) = true := by
      cases ho : ins.op <;> simp only [ho, Bool.and_eq_true] at hEdge
      case bra dst aligned =>
        cases hi : ins.guard
        · rw [hi] at hg; cases hg
        · simpa only [hi, Option.isNone_some, Bool.false_or] using hEdge.2
      case brx => cases hEdge
      all_goals exact hEdge
    exact keepReadyMode hState hn hNext (fun _ => Nat.zero_le _) (fun _ _ => rfl)
  · rcases scoreExecLocal he with hFrame | ⟨seg, hSite, hM, hRun⟩
    · have hPc := hFrame.pc
      have hPc' : readyPhaseEdge s.pc u.pc = true := by
        cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
        all_goals simp only [ho, Bool.and_eq_true] at hEdge
        case bra dst aligned => exact hPc ▸ hEdge.1
        case brx => cases hEdge
        all_goals exact hPc ▸ hEdge
      apply keepReadyMode hState hn hPc'
      · intro hu
        exact hFrame.sub.symm ▸ hState.shape (hWithin hu (.inr (.inr hPc')))
      · intro r hr
        apply hFrame.regs
        have hN : r ∉ writesRegs ins.op ++ scoreEventWrites ins.op := by
          simpa using List.all_eq_true.mp hRegs r hr
        exact fun h => hN (List.mem_append_left _ h)
    · obtain ⟨hPc, hSub, _, hReg⟩ := scoreSegmentFrame hRun
      obtain ⟨hEdge', hRegs'⟩ := readyPhaseCheckSegment hSite hM
      apply keepReadyMode hState hn (hPc ▸ hEdge')
      · exact fun _ => hSub.symm ▸ Nat.zero_le _
      · exact fun r hr => hReg r (by simpa using List.all_eq_true.mp hRegs' r hr)

private theorem readyRoleEventCode {pc : Nat} {ins : Instr} (hLo : 3103 ≤ pc)
    (hHi : pc < 6654) (hc : kernel.code[pc]? = some ins) (hl : ins.op.isLocal = false) :
    scoreEventOp ins.op = true ∧ 2535 ∉ scoreEventWrites ins.op := by
  let code := (kernel.code.drop 3103).take (6654 - 3103)
  have hAll : code.all (fun ins => (ins.op.isLocal || scoreEventOp ins.op) &&
      !(scoreEventWrites ins.op).contains 2535) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hi : code[pc - 3103]? = some ins := by
    dsimp only [code]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    exact hc
  have h := List.all_eq_true.mp hAll _ (List.mem_of_getElem? hi)
  simpa [hl] using h

private theorem readyOrdinaryEvent {l : Launch} {g : Nat} {s u : TState} {e : Event} {bit : Bool}
    (hState : ReadyState s bit) (hn : readyNormal s.pc)
    (he : EStep kernel Assumptions.all l g s e (some u)) : ReadyState u bit := by
  obtain ⟨i, hc, hl, hf⟩ := estep_event_source he
  by_cases hTail : 6654 ≤ s.pc
  · have h := (Bool.and_eq_true_iff.mp (readyPhaseCheckAt hc)).1
    have hOp : Epilogue.ordinaryEvent i.op = true := by simpa only [hl, Bool.false_or] using h
    have hPc := callbackFrame_fires (Epilogue.ordinaryEventFrame hOp) hf
    have hEnd : 6654 ≤ u.pc := by rcases hPc with h | h <;> omega
    exact ⟨by omega, fun h => (Nat.not_lt_of_ge hEnd h).elim, by
      simp [readyMode, hEnd, readyModeHolds]⟩
  · obtain ⟨hOp, hBase⟩ := readyRoleEventCode hState.role (by omega) hc hl
    have hProg := (scoreEventStep hc hOp (hState.shape (by omega)) hBase he).1
    obtain ⟨hRegs, hEdge⟩ := readyPhaseCheckNormal hc hn
    have hNext : readyPhaseEdge s.pc u.pc = true := by
      rcases hProg.pc with h | h
      · rw [h.1]
        cases ho : i.op <;> simp only [ho] at hEdge
        all_goals first | exact hEdge | (rw [ho] at hl; cases hl)
      · rw [h.1]
        simp [readyPhaseEdge]
    apply keepReadyMode hState hn hNext (fun _ => hProg.sub)
    intro r hr
    have hN : r ∉ writesRegs i.op ++ scoreEventWrites i.op := by
      simpa using List.all_eq_true.mp hRegs r hr
    exact (scoreEventStep hc hOp (hState.shape (by omega))
      (fun h => hN (List.mem_append_right _ h)) he).2

private theorem readyLocalStep {l : Launch} {g : Nat} {s u v : TState} {ev : Option Event}
    {ins : Instr} (hc : kernel.code[s.pc]? = some ins) (hLocal : ins.op.isLocal = true)
    (hRun : guardHolds s ins.guard = .ok false ∧ v = skip s ∨
      guardHolds s ins.guard = .ok true ∧ execLocalA Assumptions.all l g s ins.op = .ok v)
    (hStep : WStep kernel Assumptions.all l g s ev u) : ev = none ∧ u = v := by
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · obtain ⟨other, ho, _, hf⟩ := tauScoreSource ht
    obtain rfl := Option.some.inj (hc.symm.trans ho)
    rcases hf with ⟨rfl, hF⟩ | ⟨hF, _, hExec⟩
    · rcases hRun with ⟨_, rfl⟩ | ⟨hT, _⟩
      · exact ⟨rfl, rfl⟩
      · rw [hF] at hT
        cases hT
    · rcases hRun with ⟨hf, _⟩ | ⟨_, ht⟩
      · rw [hF] at hf
        cases hf
      · exact ⟨rfl, Except.ok.inj (hExec.symm.trans ht)⟩
  · obtain ⟨other, ho, hl, _⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hc.symm.trans ho)
    rw [hLocal] at hl
    cases hl

private theorem readyLocalExec {l : Launch} {g : Nat} {s u v : TState} {ev : Option Event}
    {op : Op} (hc : kernel.code[s.pc]? = some ⟨none, op⟩)
    (hLocal : op.isLocal = true) (hCore : Assumptions.coreOp op = true)
    (hOff : s.pc ∉ Assumptions.swExp2Sites) (hExec : execLocal l g s op = .ok v)
    (hStep : WStep kernel Assumptions.all l g s ev u) : ev = none ∧ u = v := by
  refine readyLocalStep hc hLocal (.inr ⟨rfl, ?_⟩) hStep
  rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff hCore,
    execLocalA_nil, hExec]

private def readyInitWord (r : Nat) (o : Opnd) : Op :=
  .move ⟨.scalar, .int .b 32, [some r], [o]⟩

section
variable {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}

private theorem readyInitStep {bit : Bool} (hState : ReadyState s bit) (hPc : s.pc = 3424)
    (hStep : WStep kernel Assumptions.all l g s ev u) : ev = none ∧ ReadyState u bit := by
  let v := next (setReg s 2770 (b32 0))
  have hRun : execLocal l g s (readyInitWord 2770 (.imm 0)) = .ok v := rfl
  obtain ⟨rfl, rfl⟩ := readyLocalExec (hPc.symm ▸ Flow.code_3424) rfl rfl
    (by rw [hPc]; decide) hRun hStep
  have hNext : v.pc = 3425 := by simp [v, next, setReg, hPc]
  have hB := hState.mode
  rw [hPc] at hB
  change bit = false ∧ _ at hB
  refine ⟨rfl, ⟨by omega, fun _ => hState.shape (by omega), ?_⟩⟩
  rw [hNext]
  change bit = false ∧ ∀ r ∈ [2770], v.regs r = some (b32 0)
  exact ⟨hB.1, by simp [v, next, setReg]⟩

private theorem readyCopySeedStep {bit : Bool} (hState : ReadyState s bit) (hPc : s.pc = 5027)
    (hStep : WStep kernel Assumptions.all l g s ev u) : ev = none ∧ ReadyState u bit := by
  let v := next (setReg s 7253 (b32 1))
  have hRun : execLocal l g s (readyInitWord 7253 (.imm 1)) = .ok v := rfl
  obtain ⟨rfl, rfl⟩ := readyLocalExec (hPc.symm ▸ Flow.code_5027) rfl rfl
    (by rw [hPc]; decide) hRun hStep
  have hNext : v.pc = 5028 := by simp [v, next, setReg, hPc]
  have hB := hState.mode
  rw [hPc] at hB
  change bit = true ∧ _ at hB
  refine ⟨rfl, ⟨by omega, fun _ => hState.shape (by omega), ?_⟩⟩
  rw [hNext]
  change bit = true ∧ ∀ r ∈ [7253], v.regs r = some (b32 1)
  exact ⟨hB.1, by simp [v, next, setReg]⟩

private theorem readyRestartStep {bit : Bool} (hState : ReadyState s bit) (hPc : s.pc = 5029)
    (hStep : WStep kernel Assumptions.all l g s ev u) : ev = none ∧ ReadyState u bit := by
  let v := next (setReg s 7250 (b32 1))
  have hB := hState.mode
  rw [hPc] at hB
  change bit = true ∧ (∀ r ∈ [7253], s.regs r = some (b32 1)) at hB
  have hWord := hB.2 7253 (by simp)
  have hRun : execLocal l g s (readyInitWord 7250 (.reg 7253)) = .ok v := by
    unfold readyInitWord
    rw [execLocal_move rfl]
    simp [execMove, readValue, readReg, hWord, DType.width, Value.bytes, b32, v,
      bind, Except.bind, pure, Except.pure]
  obtain ⟨rfl, rfl⟩ := readyLocalExec (hPc.symm ▸ Flow.code_5029) rfl rfl
    (by rw [hPc]; decide) hRun hStep
  have hNext : v.pc = 5030 := by simp [v, next, setReg, hPc]
  refine ⟨rfl, ⟨by omega, fun _ => hState.shape (by omega), ?_⟩⟩
  rw [hNext]
  change v.regs 7250 = some (b32 (xor bit false).toNat)
  rw [hB.1]
  simp [v, next, setReg]

private theorem readyFlipStep {bit : Bool} (hState : ReadyState s bit) (hPc : s.pc = 6648)
    (hStep : WStep kernel Assumptions.all l g s ev u) : ev = none ∧ ReadyState u bit := by
  let v := next (setReg s 7250 (b32 bit.toNat))
  have hB := hState.mode
  rw [hPc] at hB
  change s.regs 7250 = some (b32 (xor bit true).toNat) at hB
  let op : IntInstr := ⟨.xor, .int .b 32, false, [some 7250], [.reg 7250, .imm 1]⟩
  have hRun : execLocal l g s (.int op) = .ok v := by
    rw [execLocal_int rfl]
    cases bit
    all_goals
      simp [op, execInt, DType.width, readBits, readReg, hB, b32, bind,
        Except.bind, pure, Except.pure, v]
      try rfl
  obtain ⟨rfl, rfl⟩ := readyLocalExec (hPc.symm ▸ Flow.code_6648) rfl rfl
    (by rw [hPc]; decide) hRun hStep
  have hNext : v.pc = 6649 := by simp [v, next, setReg, hPc]
  refine ⟨rfl, ⟨by omega, fun _ => hState.shape (by omega), ?_⟩⟩
  rw [hNext]
  change v.regs 7250 = some (b32 (xor bit false).toNat)
  simp [v, next, setReg]

private theorem readyWaitCode (repeated : Bool) : LoaderWaitCode (readySite repeated) := by
  cases repeated
  · exact ⟨Flow.code_3498, Flow.code_3499, Flow.code_3500⟩
  · exact ⟨Flow.code_5181, Flow.code_5182, Flow.code_5183⟩

private theorem readyGateOutcome (repeated ok : Bool) (hPc : s.pc = (readySite repeated).pc + 1)
    (hR : s.regs (readySite repeated).result = some (.pred ok))
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    ev = none ∧ u = (if ok then {s with pc := (readySite repeated).pc + 3} else skip s) := by
  have ho : s.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; cases repeated <;> decide
  apply readyLocalStep (hPc.symm ▸ (readyWaitCode repeated).2.1) rfl ?_ hStep
  have hGuard : guardHolds s (some ((readySite repeated).result, false)) = .ok ok := by
    simp [guardHolds, readReg, hR, bind, Except.bind, pure, Except.pure]
  cases ok
  · exact .inl ⟨hGuard, rfl⟩
  · refine .inr ⟨hGuard, ?_⟩
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil ho rfl,
      execLocalA_nil]
    rfl

private theorem readyGateStep {bit : Bool} (repeated : Bool)
    (hPc : s.pc = (readySite repeated).pc + 1) (hState : ReadyState s bit)
    (hw : WStep kernel Assumptions.all l g s ev u) :
    ev = none ∧ ReadyState u bit := by
  have hSource : readyMode s.pc = .tested repeated := by
    rw [hPc]
    cases repeated <;> rfl
  have hF := hState.mode
  rw [hSource] at hF
  obtain ⟨ok, hR, hV⟩ := hF
  obtain ⟨rfl, rfl⟩ := readyGateOutcome repeated ok hPc hR hw
  refine ⟨rfl, ?_⟩
  cases ok
  · change ReadyState (skip s) bit
    have hNext : (skip s).pc = (readySite repeated).pc + 2 := by simp [skip, hPc]
    refine ⟨by rw [hNext]; cases repeated <;> decide, fun _ => Nat.zero_le _, ?_⟩
    rw [hNext]
    cases repeated
    · obtain ⟨hReg, hBit⟩ := hV
      change bit = false ∧ ∀ r ∈ [2770], (skip s).regs r = some (b32 0)
      exact ⟨hBit, by simpa only [List.mem_singleton, forall_eq, skip] using hReg⟩
    · exact hV
  · change ReadyState {s with pc := (readySite repeated).pc + 3} bit
    have hNext : ({s with pc := (readySite repeated).pc + 3 } : TState).pc =
        (readySite repeated).pc + 3 := rfl
    have hLow : 3103 ≤ (readySite repeated).pc + 3 := by cases repeated <;> decide
    have hSub := hState.shape (by rw [hPc]; cases repeated <;> decide)
    refine ⟨hLow, fun _ => hSub, ?_⟩
    rw [hNext]
    cases repeated
    · exact ⟨hV.2, by simp⟩
    · exact hV

private theorem readyPollStep {bit : Bool} (repeated : Bool) (hPc : s.pc = (readySite repeated).pc)
    (hState : ReadyState s bit) (hw : WStep kernel Assumptions.all l g s ev u) :
    ReadyState u (xor bit (ev.toList.any readSuccess)) := by
  obtain ⟨area, parity, ok, scope, rfl, rfl⟩ :=
    wstep_poll hw (hPc.symm ▸ (readyWaitCode repeated).1)
  let v := next (setReg s (readySite repeated).result (.pred ok))
  have hNext : v.pc = (readySite repeated).pc + 1 := by simp [v, next, setReg, hPc]
  have hLow : 3103 ≤ v.pc := by rw [hNext]; cases repeated <;> decide
  have hParity : (Option.toList (some (⟨s.pc, .wait area parity ok true scope⟩ : Event))).any
      readSuccess = ok := by
    cases repeated <;> cases ok <;> simp [readSuccess, hPc, readySite]
  rw [hParity]
  refine ⟨hLow, fun _ => hState.shape (by rw [hPc]; cases repeated <;> decide), ?_⟩
  rw [hNext]
  have hM := hState.mode
  rw [hPc] at hM
  cases repeated
  · change bit = false ∧ (∀ r ∈ [2770], s.regs r = some (b32 0)) at hM
    have hR := hM.2 2770 (by simp)
    change ∃ b, v.regs 9752 = some (.pred b) ∧
      v.regs 2770 = some (b32 0) ∧ xor bit ok = b
    refine ⟨ok, by simp [v, readySite, next, setReg], ?_, by simp [hM.1]⟩
    simpa [v, readySite, next, setReg] using hR
  · change s.regs 7250 = some (b32 (xor bit false).toNat) at hM
    change ∃ b, v.regs 9755 = some (.pred b) ∧
      v.regs 7250 = some (b32 (xor (xor bit ok) b).toNat)
    refine ⟨ok, by simp [v, readySite, next, setReg], ?_⟩
    rw [show v.regs 7250 = s.regs 7250 by simp [v, readySite, next, setReg]]
    rw [hM]
    cases bit <;> cases ok <;> rfl

private theorem readyStateStep {bit : Bool} (hState : ReadyState s bit)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    ReadyState u (xor bit (ev.toList.any readSuccess)) := by
  have localResult (h : ev = none ∧ ReadyState u bit) : ReadyState u
      (xor bit (ev.toList.any readSuccess)) := by
    obtain ⟨rfl, hs⟩ := h
    simpa using hs
  by_cases hInit : s.pc = 3424
  · exact localResult (readyInitStep hState hInit hStep)
  by_cases hSeed : s.pc = 5027
  · exact localResult (readyCopySeedStep hState hSeed hStep)
  by_cases hCopy : s.pc = 5029
  · exact localResult (readyRestartStep hState hCopy hStep)
  by_cases hFlip : s.pc = 6648
  · exact localResult (readyFlipStep hState hFlip hStep)
  by_cases hStart : s.pc = 3498
  · exact readyPollStep false hStart hState hStep
  by_cases hTest : s.pc = 3499
  · exact localResult (readyGateStep false hTest hState hStep)
  by_cases hStart' : s.pc = 5181
  · exact readyPollStep true hStart' hState hStep
  by_cases hTest' : s.pc = 5182
  · exact localResult (readyGateStep true hTest' hState hStep)
  have hn : readyNormal s.pc := by simp [readyNormal, hInit, hSeed, hCopy, hFlip,
    hStart, hTest, hStart', hTest']
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · exact localResult ⟨rfl, readyPhaseTau hState hn ht⟩
  · have hm : readSuccess e = false := by
      have hPc := estep_source_pc he
      cases h : e.kind <;> simp [readSuccess, h, hPc]
      rename_i _ _ ok _ _
      cases ok <;> simp_all
    simpa [hm] using readyOrdinaryEvent hState hn he
end

private def readBit (n : Nat) : Bool := (n % 2) == 1

private theorem readBitSucc (n : Nat) (b : Bool) : xor (readBit n) b = readBit (n + b.toNat) := by
  cases b
  · simp
  · by_cases h : n % 2 = 1
    · have hN : (n + 1) % 2 ≠ 1 := by omega
      simp [readBit, h, hN]
    · have hN : (n + 1) % 2 = 1 := by omega
      simp [readBit, h, hN]

private theorem readyPhasePath {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (hTrace : TraceReach kernel Assumptions.all l g s events u) {n : Nat}
    (hState : ReadyState s (readBit n)) :
    ReadyState u (readBit (n + events.countP readSuccess)) := by
  induction hTrace generalizing n with
  | refl => simpa using hState
  | tau hTau _ ih =>
    have h := readyStateStep hState (.inl ⟨rfl, hTau⟩)
    exact ih (by simpa using h)
  | @event s t u events e he _ ih =>
    have h := readyStateStep hState (.inr ⟨e, rfl, he⟩)
    simp only [Option.toList_some, List.any_cons, List.any_nil, Bool.or_false, readBitSucc] at h
    have hN : n + (readSuccess e).toNat + events.countP readSuccess =
        n + (e :: events).countP readSuccess := by
      rw [List.countP_cons]
      cases readSuccess e <;> simp
      omega
    exact hN ▸ ih h

/-- The phase register at the end of the packed-score loads holds a legal Bias parity. -/
theorem repeatedBiasPhaseWordOfScoreTail {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (hs : At s 3103 []) (hPc : t.pc = 5180)
    (hReach : TraceReach kernel Assumptions.all l g s events t) :
    ∃ phase < 2, t.regs 7250 = some (b32 phase) := by
  have hStartup : ReadyState s (readBit 0) := by
    refine ⟨hs.1.ge, fun _ => hs.2.1.symm ▸ Nat.zero_le _, ?_⟩
    rw [hs.1]
    exact ⟨rfl, by simp⟩
  have hMode := (readyPhasePath hReach hStartup).mode
  rw [hPc] at hMode
  change t.regs 7250 = some (b32 (xor (readBit (0+events.countP readSuccess)) false).toNat)
    at hMode
  refine ⟨(xor (readBit (0+events.countP readSuccess)) false).toNat,?_,hMode⟩
  cases xor (readBit (0+events.countP readSuccess)) false <;> decide

private theorem readSuccessMark {e : Event} (h : readSuccess e = true) :
    e.pc = 3498 ∨ e.pc = 5181 := by
  cases he : e.kind <;> simp [readSuccess, he] at h
  rename_i _ _ ok _ _
  cases ok
  · cases h
  · simpa using h

private theorem readyRegRead {l : Launch} {g : Nat} {s : TState} {ending : Option TState}
    {source q : Nat} {target : Loc} {ok acq : Bool} {scope : MbarScope}
    (repeated bit : Bool) (hPc : s.pc = (readySite repeated).pc)
    (hR : s.regs (readySite repeated).phase = some (b32 bit.toNat))
    (hE : EStep kernel Assumptions.all l g s ⟨source, .wait target q ok acq scope⟩ ending) :
    q = bit.toNat := by
  obtain ⟨tm, hOut, hFire⟩ := hE
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases congrArg Event.kind hFire.1
  rw [hPc, (readyWaitCode repeated).1] at hc
  obtain rfl := Option.some.inj hc
  have hWide : (Assumptions.all.any (·.clusterScopeMbar s.pc)) = false := rfl
  have hBits := readBits_b32 (L := l) (g := g) hR (by cases bit <;> decide)
  simp only [eventTmpl, tmaTmpl, hWide, widenMbarScope, Bool.false_eq_true, ↓reduceIte,
    bind, Except.bind, pure, Except.pure, hBits] at hFire
  cases hLoc : mbarLoc l g s (readySite repeated).base 0 with
  | error f => simp [hLoc, ofExec, Fires] at hFire
  | ok loc =>
    simp only [hLoc, ofExec, Fires] at hFire
    obtain ⟨passed, hEq, _⟩ := hFire
    have h := (Kind.wait.inj (congrArg Event.kind hEq)).2.1
    cases bit <;> exact h

/-- In every realized softmax prefix, each successful Bias-ready observation uses
the parity of the number of preceding successful Bias-ready observations. -/
theorem biasReadySourceParity {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j pc q : Nat} {target : Loc} {acq : Bool} {scope : MbarScope}
    (he : X.get (g,j) = some ⟨pc, .wait target q true acq scope⟩)
    (hMark : pc = 3498 ∨ pc = 5181) :
    q = (((X.tr g).take j).countP readSuccess) % 2 := by
  classical
  let e : Event := ⟨pc, .wait target q true acq scope⟩
  let seen (i : Nat) := ∃ f, X.get (g,i) = some f ∧ readSuccess f = true
  have hSeen : seen j := by
    refine ⟨e, he, ?_⟩
    rcases hMark with h | h <;> simp [e, readSuccess, h]
  have hEx : ∃ i, seen i := ⟨j,hSeen⟩
  let k := Nat.find hEx
  have hK : k ≤ j := Nat.find_min' hEx hSeen
  obtain ⟨f, hf, hm⟩ := Nat.find_spec hEx
  have hSites := readSuccessMark hm
  obtain ⟨_, _, pos, s, ending, hPos, hAt, hRun⟩ :=
    softmaxBodySuffix hp hX hf (by omega) (by omega)
  have hPJ : pos ≤ j := hPos.trans hK
  have he' : ((X.tr g).drop pos)[j-pos]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hPJ]
    exact he
  obtain ⟨t, out, hPath, hStep⟩ := hRun.before_event he'
  have hStartup : ReadyState s (readBit 0) := by
    refine ⟨hAt.1.ge, fun _ => hAt.2.1.symm ▸ Nat.zero_le _, ?_⟩
    rw [hAt.1]
    exact ⟨rfl, by simp⟩
  have hState := readyPhasePath hPath hStartup
  have hZero : ((X.tr g).take pos).countP readSuccess = 0 := by
    apply List.countP_eq_zero.mpr
    intro f hf hm
    obtain ⟨j, he⟩ := List.mem_iff_getElem?.mp hf
    have hLt := (List.getElem?_eq_some_iff.mp he).1
    have h : j < pos := by simp only [List.length_take] at hLt; omega
    rw [List.getElem?_take_of_lt h] at he
    exact Nat.find_min hEx (h.trans_le hPos) ⟨f, he, hm⟩
  have hCount : ((X.tr g).take j).countP readSuccess =
      (((X.tr g).drop pos).take (j-pos)).countP readSuccess := by
    have hRest : ((X.tr g).drop pos).take (j-pos) = ((X.tr g).take j).drop pos := by
      rw [List.take_drop, Nat.add_sub_of_le hPJ]
    conv_lhs => rw [← List.take_append_drop pos ((X.tr g).take j)]
    rw [List.countP_append, List.take_take, Nat.min_eq_left hPJ, hZero, Nat.zero_add, hRest]
  let n := ((X.tr g).take j).countP readSuccess
  have hMode := hState.mode
  rw [Nat.zero_add, ← hCount] at hMode
  have hPc : t.pc = pc := (estep_source_pc hStep).symm
  rw [hPc] at hMode
  have hB : (readBit n).toNat = n % 2 := by
    have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases h with h | h <;> simp [readBit, h]
  rw [← hB]
  rcases hMark with rfl | rfl
  · change readBit n = false ∧ (∀ r ∈ [2770], t.regs r = some (b32 0)) at hMode
    rw [hMode.1]
    exact readyRegRead false false hPc (hMode.2 2770 (by simp)) hStep
  · change t.regs 7250 = some (b32 (xor (readBit n) false).toNat) at hMode
    rw [Bool.xor_false] at hMode
    exact readyRegRead true (readBit n) hPc hMode hStep
end PTX.Kernels.TmlFa4Fwd.Softmax
