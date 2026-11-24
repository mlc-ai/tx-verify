-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part081
import Kernels.TmlFa4Fwd.Flow.Code.Part079
import Lemmas.Flow.TraceReach

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame

def biasedCarryRegisters : List Nat :=
  [7251,7257,1361,7258,1062,2535,5127,1230,7132,7250,7253,7248,1229,1359]

private def biasedWaitAudit (pc : Nat) (ins : Instr) : Bool :=
  !Assumptions.swExp2Sites.contains pc && (ins.op.isLocal || scoreEventOp ins.op) &&
    (writesRegs ins.op ++ scoreEventWrites ins.op).all
      (fun r => !biasedCarryRegisters.contains r) &&
    match ins.op with
    | .bra dst _ => decide (5032 ≤ dst ∧ dst ≤ 5189)
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem biasedWaitChecked :
    (((kernel.code.drop 5032).take (5189-5032)).zipIdx 5032).all
      (fun (ins,pc) => biasedWaitAudit pc ins) = true := by kernel_rfl

private theorem biasedWaitAuditAt {pc : Nat} {ins : Instr}
    (hLo : 5032 ≤ pc) (hHi : pc < 5189) (hc : kernel.code[pc]? = some ins) :
    biasedWaitAudit pc ins = true := by
  apply List.all_eq_true.mp biasedWaitChecked (ins,pc)
  apply List.mem_of_getElem? (i := pc-5032)
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

variable {l : Launch}

private theorem biasedWaitKeeps {g : Nat} {s u : TState} {e : Option Event} (hLo : 5032 ≤ s.pc)
    (hHi : s.pc < 5189) (hSub : s.sub ≤ 3) (hw : WStep kernel Assumptions.all l g s e u) :
    5032 ≤ u.pc ∧ u.pc ≤ 5189 ∧
      (∀ r ∈ biasedCarryRegisters, u.regs r = s.regs r) := by
  have hWrites {i : Instr} (hc : kernel.code[s.pc]? = some i) (r : Nat)
      (hr : r ∈ biasedCarryRegisters) : r ∉ writesRegs i.op ++ scoreEventWrites i.op := by
    intro hw
    have h := biasedWaitAuditAt hLo hHi hc
    simp only [biasedWaitAudit,Bool.and_eq_true] at h
    have := List.all_eq_true.mp h.1.2 _ hw
    simp [hr] at this
  rcases hw with ⟨rfl,ht⟩ | ⟨ev,rfl,he⟩
  · obtain ⟨i,hc,_,hBody⟩ := tauScoreSource ht
    rcases hBody with ⟨rfl,_⟩ | ⟨_,_,hx⟩
    · exact ⟨by change 5032 ≤ s.pc+1; omega,by change s.pc+1 ≤ 5189; omega,fun _ _ => rfl⟩
    rcases scoreExecLocal hx with hLoc | ⟨m,hSite,_,_⟩
    · have hPc := hLoc.pc
      have hRange : 5032 ≤ u.pc ∧ u.pc ≤ 5189 := by
        have hAudit := biasedWaitAuditAt hLo hHi hc
        cases hOp : i.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
        case bra dst uni =>
          rw [hPc]
          simp only [biasedWaitAudit,hOp,Bool.and_eq_true,decide_eq_true_eq] at hAudit
          exact hAudit.2
        case brx => simp [biasedWaitAudit,hOp] at hAudit
        all_goals omega
      exact ⟨hRange.1,hRange.2,fun r hr => hLoc.regs r (fun h =>
        hWrites hc r hr (List.mem_append_left _ h))⟩
    · have hAudit := biasedWaitAuditAt hLo hHi hc
      simp only [biasedWaitAudit,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
        decide_eq_false_iff_not] at hAudit
      exact (hAudit.1.1.1 hSite).elim
  · obtain ⟨i,hc,hNonlocal,_⟩ := estep_event_source he
    have h := biasedWaitAuditAt hLo hHi hc
    simp only [biasedWaitAudit,Bool.and_eq_true,hNonlocal,Bool.false_or] at h
    have hPc := softmaxReturningPc (by omega) (by omega) hSub he
    refine ⟨by rcases hPc with h | h <;> omega,by rcases hPc with h | h <;> omega,?_⟩
    intro r hr
    exact (scoreEventStep hc h.1.1.2 hSub (fun hm =>
      hWrites hc r hr (List.mem_append_right _ hm)) he).2

private theorem biasedFrameBeforeVectorRead {g : Nat} {s t : TState} {events : List Event}
    (ht : TraceReach kernel Assumptions.all l g s events t) (hLo : 5032 ≤ s.pc) (hHi : s.pc ≤ 5189)
    (hSub : s.sub ≤ 3) (hEvents : ∀ e ∈ events, e.pc < 5189) {Frame : TState → Prop}
    (hInitial : Frame s)
    (hPreserve : ∀ {v w : TState} {e : Option Event},
      5032 ≤ v.pc → v.pc < 5189 → v.sub ≤ 3 →
      WStep kernel Assumptions.all l g v e w → Frame v → Frame w) :
    Frame t := by
  induction ht with
  | refl => exact hInitial
  | @tau s u t es ht hPath ih =>
    have hLt : s.pc < 5189 := by
      by_contra! hGe
      have hPc : s.pc = 5189 := by omega
      obtain ⟨i,hCode,_,hBody⟩ := tauScoreSource ht
      rw [hPc,Flow.code_5189] at hCode
      obtain rfl := Option.some.inj hCode
      rcases hBody with ⟨rfl,hFalse⟩ | ⟨_,hTrue,_⟩
      · cases hFalse
      · cases hTrue
    have hs : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl,ht⟩
    obtain ⟨hLo',hHi',_⟩ := biasedWaitKeeps hLo hLt hSub hs
    have hFrame := windowStepFrame .biasedBody (by exact hLo) (by change s.pc < 6650; omega)
      hSub hs
    exact ih hLo' hHi' hFrame.2.2.1 hEvents (hPreserve hLo hLt hSub hs hInitial)
  | @event s u t es e he hPath ih =>
    have hLt : s.pc < 5189 := (estep_source_pc he) ▸ hEvents e (List.mem_cons_self ..)
    have hs : WStep kernel Assumptions.all l g s (some e) u := .inr ⟨e,rfl,he⟩
    obtain ⟨hLo',hHi',_⟩ := biasedWaitKeeps hLo hLt hSub hs
    have hFrame := windowStepFrame .biasedBody (by exact hLo) (by change s.pc < 6650; omega)
      hSub hs
    exact ih hLo' hHi' hFrame.2.2.1
      (fun e h => hEvents e (List.mem_cons_of_mem _ h)) (hPreserve hLo hLt hSub hs hInitial)

/-- Up to the selected biased wait, the lane keeps its incoming reference and
running denominator, along with the phase and iteration counter. -/
theorem biasedCarryBeforeVectorRead {g : Nat} {s t : TState} {events : List Event}
    (ht : TraceReach kernel Assumptions.all l g s events t) (hLo : 5032 ≤ s.pc) (hHi : s.pc ≤ 5189)
    (hSub : s.sub ≤ 3) (hEvents : ∀ e ∈ events, e.pc < 5189) :
    ∀ r ∈ biasedCarryRegisters, t.regs r = s.regs r := by
  apply biasedFrameBeforeVectorRead ht hLo hHi hSub hEvents
    (Frame := fun u => ∀ r ∈ biasedCarryRegisters, u.regs r = s.regs r) (fun _ _ => rfl)
  intro v w e hL hH hS hStep hPrev r hr
  exact ((biasedWaitKeeps hL hH hS hStep).2.2 r hr).trans (hPrev r hr)

private theorem biasedBlockSubWord {x : Nat} (hx : x < 2^32) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) +
      truncBits 32 (BitVec.ofInt 64 (-1))) =
      BitVec.ofNat 64 ((x+(2^32-1))%2^32) := by
  have hMask : truncBits 32 (BitVec.ofInt 64 (-1)) =
      BitVec.ofNat 64 (2^32-1) := rfl
  rw [truncBits_ofNat hx (by decide),hMask,← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show x+(2^32-1) < 2^64 by omega)]

/-- The decoded biased pass decrements the actual block word before the score wait. -/
theorem biasedBlockDecrement {g : Nat} {s u : TState} {x : Nat} (hp : s.pc = 5104) (hx : x < 2^32)
    (hr : s.regs 7249 = some (b32 x)) (h : Tau kernel Assumptions.all l g s u) :
    u.pc = 5105 ∧ u.regs 7249 = some (b32 ((x+(2^32-1))%2^32)) := by
  obtain ⟨i,hc,_,hStep⟩ := tauScoreSource h
  rw [hp,Flow.code_5104] at hc
  obtain rfl := Option.some.inj hc
  rcases hStep with ⟨rfl,hNo⟩ | ⟨_,_,hExec⟩
  · cases hNo
  rw [Assumptions.execLocalA_all_eq_numeric,
    Assumptions.execLocalA_eq_nil (by rw [hp]; decide) rfl,execLocalA_nil,
    execLocal_int rfl] at hExec
  simp only [b32,execInt,DType.width,readBits,readValue,readReg,hr,bind,Except.bind,
    pure,Except.pure] at hExec
  rw [biasedBlockSubWord hx] at hExec
  obtain rfl := Except.ok.inj hExec
  exact ⟨congrArg (·+1) hp,rfl⟩

private def biasedBlockAudit (pc : Nat) (ins : Instr) : Bool :=
  (pc == 5104 || !(writesRegs ins.op ++ scoreEventWrites ins.op).contains 7249) &&
    match ins.op with
    | .bra dst _ => decide ((pc ≤ 5104) = (dst ≤ 5104))
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem biasedBlockChecked :
    (((kernel.code.drop 5032).take (5189-5032)).zipIdx 5032).all
      (fun (ins,pc) => biasedBlockAudit pc ins) = true := by kernel_rfl

private theorem biasedBlockAuditAt {pc : Nat} {ins : Instr}
    (hLo : 5032 ≤ pc) (hHi : pc < 5189) (hc : kernel.code[pc]? = some ins) :
    biasedBlockAudit pc ins = true := by
  apply List.all_eq_true.mp biasedBlockChecked (ins,pc)
  apply List.mem_of_getElem? (i := pc-5032)
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

private theorem biasedBlockStep {g n : Nat} {s u : TState} {e : Option Event} (hLo : 5032 ≤ s.pc)
    (hHi : s.pc < 5189) (hSub : s.sub ≤ 3) (hn : n < 2^32)
    (hw : WStep kernel Assumptions.all l g s e u)
    (hr : s.regs 7249 = some (b32 (if s.pc ≤ 5104 then n else (n+(2^32-1))%2^32))) :
    u.regs 7249 = some (b32 (if u.pc ≤ 5104 then n else (n+(2^32-1))%2^32)) := by
  by_cases hDec : s.pc = 5104
  · have hIn : s.pc ≤ 5104 := by omega
    rw [ite_eq_left hIn] at hr
    rcases hw with ⟨rfl,ht⟩ | ⟨ev,rfl,he⟩
    · obtain ⟨hPC,hR⟩ := biasedBlockDecrement hDec hn hr ht
      simpa only [hPC,show ¬ (5105 : Nat) ≤ 5104 by decide,ite_false] using hR
    · obtain ⟨i,hc,hNonlocal,_⟩ := estep_event_source he
      rw [hDec,Flow.code_5104] at hc
      obtain rfl := Option.some.inj hc
      cases hNonlocal
  have hKeep {i : Instr} (hc : kernel.code[s.pc]? = some i) :
      7249 ∉ writesRegs i.op ++ scoreEventWrites i.op := by
    have h := biasedBlockAuditAt hLo hHi hc
    have hPc : (s.pc == 5104) = false := by simp [hDec]
    simp only [biasedBlockAudit,Bool.and_eq_true,hPc,Bool.false_or,
      Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at h
    exact h.1
  rcases hw with ⟨rfl,ht⟩ | ⟨ev,rfl,he⟩
  · obtain ⟨i,hc,_,hBody⟩ := tauScoreSource ht
    rcases hBody with ⟨rfl,_⟩ | ⟨_,_,hExec⟩
    · change s.regs 7249 = some (b32 (if s.pc+1 ≤ 5104 then n else (n+(2^32-1))%2^32))
      by_cases hSide : s.pc ≤ 5104
      · simpa only [hSide,show s.pc+1 ≤ 5104 by omega,ite_true] using hr
      · simpa only [hSide,show ¬ s.pc+1 ≤ 5104 by omega,ite_false] using hr
    rcases scoreExecLocal hExec with hLoc | ⟨m,hSite,_,_⟩
    · have hPc := hLoc.pc
      have sameSide : (u.pc ≤ 5104) = (s.pc ≤ 5104) := by
        have hAudit := biasedBlockAuditAt hLo hHi hc
        cases hOp : i.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
        case bra dst uni =>
          rw [hPc]
          simp only [biasedBlockAudit,hOp,Bool.and_eq_true,decide_eq_true_eq] at hAudit
          exact hAudit.2.symm
        case brx => simp [biasedBlockAudit,hOp] at hAudit
        all_goals exact propext (by omega)
      rw [hLoc.regs _ (fun hm => hKeep hc (List.mem_append_left _ hm))]
      simpa only [sameSide] using hr
    · have hAudit := biasedWaitAuditAt hLo hHi hc
      simp only [biasedWaitAudit,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
        decide_eq_false_iff_not] at hAudit
      exact (hAudit.1.1.1 hSite).elim
  · obtain ⟨i,hc,hNonlocal,_⟩ := estep_event_source he
    have h := biasedWaitAuditAt hLo hHi hc
    simp only [biasedWaitAudit,Bool.and_eq_true,hNonlocal,Bool.false_or] at h
    have hP := softmaxReturningPc (by omega) (by omega) hSub he
    have sameSide : (u.pc ≤ 5104) = (s.pc ≤ 5104) :=
      propext (by rcases hP with h | h <;> omega)
    rw [(scoreEventStep hc h.1.1.2 hSub (fun hm =>
      hKeep hc (List.mem_append_right _ hm)) he).2]
    simpa only [sameSide] using hr

/-- The block word reaching the actual Bias wait is the decrement of that
iteration's incoming block word. -/
theorem biasedBlockWordBeforeVectorRead {g n : Nat} {s t : TState} {events : List Event}
    (hn : n < 2^32) (ht : TraceReach kernel Assumptions.all l g s events t) (hStart : s.pc = 5032)
    (hEnd : t.pc = 5181) (hSub : s.sub ≤ 3) (hEvents : ∀ e ∈ events, e.pc < 5189)
    (hWord : s.regs 7249 = some (b32 n)) :
    t.regs 7249 = some (b32 ((n+(2^32-1))%2^32)) := by
  let Frame (u : TState) := u.regs 7249 =
    some (b32 (if u.pc ≤ 5104 then n else (n+(2^32-1))%2^32))
  have hInit : Frame s := by
    simpa only [Frame,hStart,show (5032 : Nat) ≤ 5104 by decide,ite_true] using hWord
  have hFinal := biasedFrameBeforeVectorRead ht hStart.ge (by omega) hSub hEvents hInit
    (fun hLo hHi hSub hStep => biasedBlockStep hLo hHi hSub hn hStep)
  simpa only [Frame,hEnd,show ¬ (5181 : Nat) ≤ 5104 by decide,ite_false] using hFinal

end PTX.Kernels.TmlFa4Fwd.Softmax
