-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part051
import Kernels.TmlFa4Fwd.Flow.Code.Part078
import Kernels.TmlFa4Fwd.Flow.Code.Part103
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Lemmas.Flow.ElemAccess

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Softmax

private def probabilityMassAdd (a b : Nat) : FloatInstr :=
  { op := .add, ty := ⟨.f32,1⟩, mode := .ieee, dsts := [some 7257], srcs := [.reg a,.reg b] }

private theorem massCoreWrites {l : Launch} {g a b : Nat} {s : TState} :
    AllOk (fun u => ∃ v, u.regs 7257 = some v) (execFloat l g s (probabilityMassAdd a b)) := by
  unfold execFloat
  simp only [probabilityMassAdd]
  apply allOk_bind
  intro combine
  apply allOk_bind
  intro inputs
  apply allOk_bind
  intro outputs
  split
  all_goals try trivial
  all_goals
    rename_i he _
    simp only [List.cons.injEq,Option.some.injEq] at he
    obtain ⟨rfl,_⟩ := he
    simp [pure,Except.pure,AllOk,next,setReg]

private theorem massIdealWrites {l : Launch} {g a b : Nat} {s : TState} {result : Exec TState}
    (h : execIdealFloat l g s (.float (probabilityMassAdd a b)) = some result) :
    AllOk (fun u => ∃ v, u.regs 7257 = some v) result := by
  change bindRead (readERealOpnd s .f32 (.reg a)) (fun x =>
    bindRead (readERealOpnd s .f32 (.reg b)) (fun y =>
      (addEReal x y).map fun r => .ok (next (setReg s 7257 (erealValue .f32 r))))) =
    some result at h
  cases ha : readERealOpnd s .f32 (.reg a) with
  | none => simp [ha,bindRead] at h
  | some ra =>
    cases ra with
    | error f =>
      cases (Option.some.inj (by simpa only [ha,bindRead] using h))
      trivial
    | ok x =>
      cases hb : readERealOpnd s .f32 (.reg b) with
      | none => simp [ha,hb,bindRead] at h
      | some rb =>
        cases rb with
        | error f =>
          cases (Option.some.inj (by simpa only [ha,hb,bindRead] using h))
          trivial
        | ok y =>
          cases hx : addEReal x y with
          | none => simp [ha,hb,hx,bindRead] at h
          | some r =>
            cases (Option.some.inj (by simpa only [ha,hb,hx,bindRead,Option.map_some] using h))
            exact ⟨erealValue .f32 r,by simp [next,setReg]⟩

private theorem massAddDefines {l : Launch} {g a b : Nat} {s u : TState}
    (hOff : s.pc ∉ Assumptions.swExp2Sites)
    (he : execLocalA Assumptions.all l g s (.float (probabilityMassAdd a b)) = .ok u) :
    ∃ v, u.regs 7257 = some v := by
  rw [Assumptions.execLocalA_all_eq_numeric,execLocalA_noSegment
    (fun asm ha => Assumptions.numeric_segSites asm ha l g s hOff)] at he
  have hRules : ∀ asm ∈ Assumptions.numeric.tail,
      asm.localRule l g s (.float (probabilityMassAdd a b)) = none := by
    intro asm hAsm
    simp only [Assumptions.numeric,List.tail_cons,List.mem_cons,List.not_mem_nil,or_false] at hAsm
    rcases hAsm with rfl | rfl | rfl | rfl <;> rfl
  have hFirst : Assumptions.idealArith.localRule l g s (.float (probabilityMassAdd a b)) =
      execIdealFloat l g s (.float (probabilityMassAdd a b)) := rfl
  unfold execLocalRule at he
  change (match (Assumptions.idealArith::Assumptions.numeric.tail).findSome?
    (fun asm => asm.localRule l g s (.float (probabilityMassAdd a b))) with
    | some o => o
    | none => execLocal l g s (.float (probabilityMassAdd a b))) = .ok u at he
  rw [List.findSome?_cons,hFirst,List.findSome?_eq_none_iff.mpr hRules] at he
  cases h : execIdealFloat l g s (.float (probabilityMassAdd a b)) with
  | none =>
    rw [h] at he
    have hValue := massCoreWrites (l := l) (g := g) (s := s) (a := a) (b := b)
    change execFloat l g s (probabilityMassAdd a b) = .ok u at he
    rwa [he] at hValue
  | some value =>
    rw [h] at he
    have hs := massIdealWrites (l := l) (g := g) h
    change value = .ok u at he
    rwa [he] at hs


private def phaseMove (a : Opnd) : MoveInstr :=
  { kind := .scalar, ty := .int .b 32, dsts := [some 7258], srcs := [a] }

private def phaseXor : IntInstr :=
  { op := .xor, ty := .int .b 32, dsts := [some 7258], srcs := [.reg 7258,.imm 1] }

private theorem phaseMoveDefines {l : Launch} {g : Nat} {s u : TState} (a : Opnd)
    (hOff : s.pc ∉ Assumptions.swExp2Sites)
    (he : execLocalA Assumptions.all l g s (.move (phaseMove a)) = .ok u) :
    ∃ v, u.regs 7258 = some v := by
  have hCore : Assumptions.coreOp (.move (phaseMove a)) = true := rfl
  rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff hCore,
    execLocalA_nil] at he
  change execMove l g s (.move (phaseMove a)) = .ok u at he
  simp only [execMove,phaseMove,DType.width] at he
  cases hRead : readValue l g s 32 a with
  | error f => simp [hRead,bind,Except.bind] at he
  | ok v =>
    by_cases hWidth : v.bytes = 4
    · simp [hRead,hWidth,bind,Except.bind,pure,Except.pure] at he
      subst u
      exact ⟨v,by simp [next,setReg]⟩
    · simp [hRead,hWidth,bind,Except.bind] at he

private theorem phaseXorDefines {l : Launch} {g : Nat} {s u : TState}
    (hOff : s.pc ∉ Assumptions.swExp2Sites)
    (he : execLocalA Assumptions.all l g s (.int phaseXor) = .ok u) :
    ∃ v, u.regs 7258 = some v := by
  have hCore : Assumptions.coreOp (.int phaseXor) = true := rfl
  rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff hCore,
    execLocalA_nil] at he
  change (do
    let x ← readBits l g s 32 (.reg 7258)
    let y ← readBits l g s 32 (.imm 1)
    pure (next (setReg s 7258 (.bits 32 (x ^^^ y))))) = .ok u at he
  have h : AllOk (fun t => ∃ v, t.regs 7258 = some v) (do
    let x ← readBits l g s 32 (.reg 7258)
    let y ← readBits l g s 32 (.imm 1)
    pure (next (setReg s 7258 (.bits 32 (x ^^^ y))))) := by
    apply allOk_bind
    intro x
    apply allOk_bind
    intro y
    exact ⟨.bits 32 (x ^^^ y),by simp [next,setReg]⟩
  rwa [he] at h

private def liveReg (phase : Bool) : Nat := if phase then 7258 else 7257
private def liveInit (phase : Bool) : Nat := if phase then 3283 else 5005
private def liveSites (phase : Bool) : List Nat :=
  if phase then [3283,5022,5030,6647,7600] else [5005,6646,7598]

private def inLiveRange (phase : Bool) (pc : Nat) : Prop := liveInit phase < pc ∧ pc ≤ 7604
private instance (phase : Bool) (pc : Nat) : Decidable (inLiveRange phase pc) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def liveCode (phase : Bool) (pc : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || scoreEventOp i.op) &&
  (i.op.isLocal || !(scoreEventWrites i.op).contains (liveReg phase)) &&
  (!((writesRegs i.op).contains (liveReg phase)) || (liveSites phase).contains pc) &&
  match i.op with
  | .bra dst _ => !decide (inLiveRange phase dst) || decide (inLiveRange phase pc)
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem liveCodeAudit (phase : Bool) :
    ((((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103)).all
      (fun (i,pc) => liveCode phase pc i) = true := by
  cases phase <;> decide +kernel

private theorem liveCodeAt (phase : Bool) {pc : Nat} {i : Instr}
    (hLo : 3103 ≤ pc) (hHi : pc < 7742) (hCode : kernel.code[pc]? = some i) :
    liveCode phase pc i = true := by
  apply List.all_eq_true.mp (liveCodeAudit phase) (i,pc)
  apply List.mem_of_getElem? (i := pc-3103)
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hCode]
  rfl

private noncomputable def liveSegment (phase : Bool) (pc : Nat) : Bool :=
  match cuteExp2.matchAt kernel pc with
  | some m => !(scoreSegmentWrites m).contains (liveReg phase) &&
      (!decide (inLiveRange phase m.stop) || decide (inLiveRange phase pc))
  | none => false

set_option maxRecDepth 100000 in
private theorem liveSegmentAudit (phase : Bool) :
    Assumptions.swExp2Sites.all (liveSegment phase) = true := by
  cases phase <;> kernel_rfl

private theorem liveSegmentAt (phase : Bool) {pc : Nat} {m : SegMatch CuteSlot}
    (hSite : pc ∈ Assumptions.swExp2Sites) (hMatch : cuteExp2.matchAt kernel pc = some m) :
    liveReg phase ∉ scoreSegmentWrites m ∧ (inLiveRange phase m.stop → inLiveRange phase pc) := by
  have h := List.all_eq_true.mp (liveSegmentAudit phase) pc hSite
  unfold liveSegment at h
  rw [hMatch] at h
  simpa only [Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not,
    Bool.or_eq_true,decide_eq_true_eq,or_iff_not_imp_left,not_not] using h

private theorem initUnguarded (phase : Bool) {pc : Nat} {i : Instr}
    (hPc : pc = liveInit phase) (hc : kernel.code[pc]? = some i) : i.guard = none := by
  cases phase
  · rw [hPc,show liveInit false = 5005 by rfl,Flow.code_5005] at hc
    obtain rfl := Option.some.inj hc
    rfl
  · rw [hPc,show liveInit true = 3283 by rfl,Flow.code_3283] at hc
    obtain rfl := Option.some.inj hc
    rfl

private theorem executeLiveWriter {l : Launch} {g : Nat} (phase : Bool) {s u : TState}
    {i : Instr} (hc : kernel.code[s.pc]? = some i) (hw : s.pc ∈ liveSites phase)
    (he : execLocalA Assumptions.all l g s i.op = .ok u) :
    ∃ v, u.regs (liveReg phase) = some v := by
  cases phase
  · simp [liveSites] at hw
    rcases hw with h | h | h
    · rw [h,Flow.code_5005] at hc
      obtain rfl := Option.some.inj hc
      exact massAddDefines (hOff := h.symm ▸ (by decide : 5005 ∉ Assumptions.swExp2Sites)) he
    · rw [h,Flow.code_6646] at hc
      obtain rfl := Option.some.inj hc
      exact massAddDefines (hOff := h.symm ▸ (by decide : 6646 ∉ Assumptions.swExp2Sites)) he
    · rw [h,Flow.code_7598] at hc
      obtain rfl := Option.some.inj hc
      exact massAddDefines (hOff := h.symm ▸ (by decide : 7598 ∉ Assumptions.swExp2Sites)) he
  · simp [liveSites] at hw
    rcases hw with h | h | h | h | h
    · rw [h,Flow.code_3283] at hc
      obtain rfl := Option.some.inj hc
      exact phaseMoveDefines _ (h.symm ▸ (by decide : 3283 ∉ Assumptions.swExp2Sites)) he
    · rw [h,Flow.code_5022] at hc
      obtain rfl := Option.some.inj hc
      exact phaseMoveDefines _ (h.symm ▸ (by decide : 5022 ∉ Assumptions.swExp2Sites)) he
    · rw [h,Flow.code_5030] at hc
      obtain rfl := Option.some.inj hc
      exact phaseMoveDefines _ (h.symm ▸ (by decide : 5030 ∉ Assumptions.swExp2Sites)) he
    · rw [h,Flow.code_6647] at hc
      obtain rfl := Option.some.inj hc
      exact phaseXorDefines (h.symm ▸ (by decide : 6647 ∉ Assumptions.swExp2Sites)) he
    · rw [h,Flow.code_7600] at hc
      obtain rfl := Option.some.inj hc
      exact phaseXorDefines (h.symm ▸ (by decide : 7600 ∉ Assumptions.swExp2Sites)) he


private theorem liveRegisterStep {l : Launch} {g : Nat} (phase : Bool)
    {s u : TState} {ev : Option Event} (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742)
    (hSub : s.sub ≤ 3)
    (hHeld : inLiveRange phase s.pc → ∃ v, s.regs (liveReg phase) = some v)
    (hStep : WStep kernel Assumptions.all l g s ev u)
    (hDest : inLiveRange phase u.pc) : ∃ v, u.regs (liveReg phase) = some v := by
  have hFall (hPc : u.pc = s.pc+1) : s.pc = liveInit phase ∨ inLiveRange phase s.pc := by
    unfold inLiveRange at hDest ⊢
    omega
  have hStart : liveInit phase ∈ liveSites phase := by cases phase <;> decide
  have hKeep (hPrev : inLiveRange phase s.pc)
      (hEq : u.regs (liveReg phase) = s.regs (liveReg phase)) :
      ∃ v, u.regs (liveReg phase) = some v :=
    hEq ▸ hHeld hPrev
  rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
  · obtain ⟨i,hc,_,hSource⟩ := tauScoreSource hTau
    have ha := liveCodeAt phase hLo hHi hc
    simp only [liveCode,Bool.and_eq_true] at ha
    rcases hSource with ⟨rfl,hGuard⟩ | ⟨_,_,hExec⟩
    · rcases hFall rfl with hInit | hPrev
      · rw [initUnguarded phase hInit hc] at hGuard
        cases hGuard
      · exact hKeep hPrev rfl
    rcases scoreExecLocal hExec with hLocal | ⟨seg,hSite,hMatch,hSeg⟩
    · by_cases hWrite : liveReg phase ∈ writesRegs i.op
      · apply executeLiveWriter phase hc _ hExec
        have hSites := ha.1.2
        simpa [hWrite] using hSites
      have hEq := hLocal.regs _ hWrite
      have hPc := hLocal.pc
      cases hop : i.op <;>
        simp only [hop,nextPc,BrxTarget,or_false] at hPc
      case bra dst _ =>
        have hMayEnter : inLiveRange phase dst → inLiveRange phase s.pc := by
          have hh : ¬inLiveRange phase dst ∨ inLiveRange phase s.pc := by
            simpa [hop] using ha.2
          exact fun hd => hh.resolve_left (fun hn => hn hd)
        exact hKeep (hMayEnter (hPc ▸ hDest)) hEq
      case brx => simp [hop] at ha
      all_goals
        rcases hFall hPc with hInit | hPrev
        · exact executeLiveWriter phase hc (hInit.symm ▸ hStart) hExec
        · exact hKeep hPrev hEq
    · obtain ⟨hPc,_,_,hRegs⟩ := scoreSegmentFrame hSeg
      obtain ⟨hStable,hBack⟩ := liveSegmentAt phase hSite hMatch
      exact hKeep (hBack (hPc ▸ hDest)) (hRegs _ hStable)
  · obtain ⟨i,hc,hNotLocal,_⟩ := estep_event_source hEvent
    have ha := liveCodeAt phase hLo hHi hc
    simp only [liveCode,hNotLocal,Bool.false_or,Bool.and_eq_true] at ha
    have hStable : liveReg phase ∉ scoreEventWrites i.op := by
      simpa using ha.1.1.2
    obtain ⟨hNext,hEq⟩ := scoreEventStep hc ha.1.1.1 hSub hStable hEvent
    rcases hNext.pc with ⟨hPc,_⟩ | ⟨hPc,_⟩
    · rcases hFall hPc with hInit | hPrev
      · have hInitLocal : i.op.isLocal = true := by
          cases phase
          · rw [hInit,show liveInit false = 5005 by rfl,Flow.code_5005] at hc
            obtain rfl := Option.some.inj hc
            rfl
          · rw [hInit,show liveInit true = 3283 by rfl,Flow.code_3283] at hc
            obtain rfl := Option.some.inj hc
            rfl
        rw [hNotLocal] at hInitLocal
        cases hInitLocal
      · exact hKeep hPrev hEq
    · exact hKeep (hPc ▸ hDest) hEq

/-- On the same role-entry trace, both repeated softmax carry registers are
initialized before the selected event, including padding and finite prefixes. -/
theorem probabilityCarryRegistersFromEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g pos j : Nat} {s : TState} {ending : Option TState}
    (hEntry : At s 3103 [(1062,b32 warp.val),(2535,b32 l.sharedBase)])
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    {e : Event} (he : X.get (g,j) = some e) (hBefore : pos ≤ j)
    (hLo : 5005 < e.pc) (hHi : e.pc ≤ 7604) :
    ∃ t o, EStep kernel Assumptions.all l g t e o ∧
      TraceReach kernel Assumptions.all l g s (((X.tr g).drop pos).take (j-pos)) t ∧
      (∃ v, t.regs 7257 = some v) ∧ (∃ v, t.regs 7258 = some v) := by
  let inv (s : TState) :=
    ∀ phase, inLiveRange phase s.pc → ∃ v, s.regs (liveReg phase) = some v
  obtain ⟨t,o,hPc,_,_,_,_,hInv,hEvent,_,hPath⟩ :=
    softmaxRoleEventFromEntryWithScratch hp warp hEntry hRun he hBefore (by omega)
      (Q := inv)
      (fun phase hRange => by
        have hFloor : 3103 < liveInit phase := by cases phase <;> decide
        have hEntryPc := hEntry.1
        unfold inLiveRange at hRange
        omega)
      (fun hStart hEnd hSub _ _ _ hInv hStep phase hRange =>
        liveRegisterStep phase hStart hEnd hSub (hInv phase) hStep hRange)
  have hMass := hInv false (show inLiveRange false t.pc by
    change 5005 < t.pc ∧ t.pc ≤ 7604
    omega)
  have hPhase := hInv true (show inLiveRange true t.pc by
    change 3283 < t.pc ∧ t.pc ≤ 7604
    omega)
  exact ⟨t,o,hEvent,hPath,hMass,hPhase⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
