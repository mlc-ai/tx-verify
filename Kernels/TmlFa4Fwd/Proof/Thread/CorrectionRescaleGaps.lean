-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionRescaleSlots
import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixAccumulator
import Kernels.TmlFa4Fwd.Proof.CorrectionLinearPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open _root_.PTX.Kernels.TmlFa4Fwd.Correction Softmax

/-- The short intervals before either rescale ballot and before the loop latch. -/
inductive RescaleGap where
  | firstVote
  | secondVote
  | latch

def RescaleGap.start : RescaleGap → Nat
  | .firstVote => 8006
  | .secondVote => 8222
  | .latch => 8441

def RescaleGap.stop : RescaleGap → Nat
  | .firstVote => 8009
  | .secondVote => 8228
  | .latch => 8444

private def gapLocal (op : Op) : Bool :=
  op.isLocal && match op with | .bra .. | .brx .. => false | _ => true

private def gapEvent (op : Op) : Bool :=
  match op with
  | .mem a => a.kind == .load && !a.nc && a.ext == .same && a.regs.length ≤ 1
  | .barSyncN .. | .mbarArrive .. => true
  | _ => false

private theorem gapAuditAt (gap : RescaleGap) {pc : Nat} {i : Instr}
    (hLo : gap.start ≤ pc) (hHi : pc < gap.stop) (hc : kernel.code[pc]? = some i) :
    (gapLocal i.op || gapEvent i.op) = true := by
  let code := (kernel.code.drop gap.start).take (gap.stop-gap.start)
  have hAll : code.all (fun ins => gapLocal ins.op || gapEvent ins.op) = true := by
    cases gap <;> decide +kernel
  apply List.all_eq_true.mp hAll i
  apply List.mem_of_getElem? (i := pc-gap.start)
  rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo,hc]

/-- Scratch and loop-count register preserved through a rescale interval. -/
structure CorrectionRescaleFrame (s : TState) (word : Value) : Prop where
  sub : s.sub = 0
  acc : s.acc = []
  counter : s.regs 7278 = some word

private theorem gapEventShape {l : Launch} {g : Nat} {s u : TState} {e : Event} {op : Op}
    (hOp : gapEvent op = true) (hs : s.sub = 0)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s op) e (some u)) :
    u.sub = 0 ∧ s.pc ≤ u.pc ∧ u.pc ≤ s.pc+1 ∧ isTcData e = false := by
  have hData : isTcData e = false := by
    cases ht : isTcData e
    · rfl
    · have hTc := fires_tcData_op hf ht
      cases op <;> simp_all [gapEvent,tcDataOp]
  have hShape : u.sub = 0 ∧ s.pc ≤ u.pc ∧ u.pc ≤ s.pc+1 := by
    cases op <;> simp only [gapEvent] at hOp <;> try contradiction
    case mem a =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hOp
      obtain ⟨_,bs,_,rfl⟩ := fires_load hOp.1.1.1 hOp.1.1.2 hf hOp.1.2
      cases hr : rebuild 3 bs with
      | error f => simp [afterLoad,hr,hs]
      | ok v => rw [afterLoad_last hr (by omega)]; simp
    case mbarArrive base off tx count cluster release scope dest =>
      obtain ⟨rfl,_⟩ := fires_arrive_state hf
      cases dest <;> simp [next,mbarStateDest,hs]
    case barSyncN id n uni =>
      have hFrame : CallbackFrame (· = next s) (eventTmpl Assumptions.all l g s
          (.barSyncN id n uni)) := by
        simp only [eventTmpl,barTmpl]
        repeat' split
        all_goals first | rfl | trivial
      obtain rfl := callbackFrame_fires hFrame hf
      simp [next,hs]
  exact ⟨hShape.1,hShape.2.1,hShape.2.2,hData⟩

private theorem gapStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event} {word : Value}
    (gap : RescaleGap) (hLo : gap.start ≤ s.pc) (hHi : s.pc < gap.stop)
    (hFrame : CorrectionRescaleFrame s word)
    (hW : WStep kernel Assumptions.all l g s ev u) :
    gap.start ≤ u.pc ∧ u.pc ≤ gap.stop ∧ CorrectionRescaleFrame u word ∧
      ∀ e ∈ ev.toList, isTcData e = false := by
  have hMin : 8006 ≤ gap.start := by cases gap <;> decide
  have hMax : gap.stop ≤ 8444 := by cases gap <;> decide
  have hCodeLow : (correctionLinearRegion 3).lo ≤ s.pc := by change 8006 ≤ s.pc; omega
  have hCodeHi : s.pc < (correctionLinearRegion 3).hi := by change s.pc < 8444; omega
  have hZero : s.sub ≤ 3 := by rw [hFrame.sub]; decide
  obtain ⟨_,_,hReg⟩ := correctionLinearStep 3 hCodeLow hCodeHi hZero hW
  have hCnt : u.regs 7278 = some word := hReg.trans hFrame.counter
  rcases hW with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · have hNo : s.pc ∉ Assumptions.swExp2Sites := by
      simp [Assumptions.swExp2Sites]
      omega
    obtain ⟨i,hCode,_,hT⟩ := correctionTauFrame hNo ht
    rcases hT with ⟨rfl,_⟩ | ⟨_,hLocal,hF⟩
    · have hp : (skip s).pc = s.pc+1 := rfl
      exact ⟨by omega, by omega, ⟨rfl,rfl,hCnt⟩, by simp⟩
    · have hA := gapAuditAt gap hLo hHi hCode
      have hSimple : gapLocal i.op = true := by
        cases h : gapLocal i.op
        · have hEvent : gapEvent i.op = true := by simpa only [h,Bool.false_or] using hA
          cases hop : i.op <;> simp_all [gapEvent, gapLocal, Op.isLocal]
        · rfl
      have hp : u.pc = s.pc+1 := by
        have h := hF.pc
        cases hop : i.op <;> simp_all [nextPc,BrxTarget,gapLocal]
      exact ⟨by omega,by omega,⟨hF.sub.trans hFrame.sub,hF.acc.trans hFrame.acc,hCnt⟩,by simp⟩
  · obtain ⟨i,hc,hLoc,hFire⟩ := estep_event_source he
    have hOp : gapEvent i.op = true := by
      simpa [gapLocal,hLoc] using gapAuditAt gap hLo hHi hc
    obtain ⟨hSub,hMin,hMax,hNo⟩ := gapEventShape hOp hFrame.sub hFire
    have hReturns : correctionReturningOp i.op = true := by
      cases hop : i.op <;> simp_all [gapEvent, correctionReturningOp, scoreEventOp]
      case mem a => exact .inl (hOp.2.trans (by decide))
    have hScalar : match i.op with | .mem a => a.kind = .load → a.regs.length ≤ 1 | _ => True := by
      cases hop : i.op <;> try trivial
      case mem a => exact fun _ => of_decide_eq_true (Bool.and_eq_true_iff.mp (hop ▸ hOp)).2
    have hAcc := correctionEventAccumulator hc hReturns hScalar hFrame.acc he
    exact ⟨by omega,by omega,⟨hSub,hAcc,hCnt⟩,fun x hx => List.mem_singleton.mp hx ▸ hNo⟩

/-- Crossing each gap is exact and emits only ordinary events. A finite prefix may stop
inside the gap before it observes either the next ballot or the latch. -/
theorem correctionRescaleGapDecompose {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {word : Value} (gap : RescaleGap)
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : gap.start ≤ s.pc) (hHi : s.pc ≤ gap.stop) (hFrame : CorrectionRescaleFrame s word) :
    (∀ e ∈ events, gap.start ≤ e.pc ∧ e.pc < gap.stop ∧ isTcData e = false) ∨
      ∃ u pre tail rest, events = pre ++ tail ∧ u.pc = gap.stop ∧
        CorrectionRescaleFrame u word ∧
        (∀ e ∈ pre, gap.start ≤ e.pc ∧ e.pc < gap.stop ∧ isTcData e = false) ∧
        Walk kernel Assumptions.all l g u tail rest := by
  have hCut {t : TState} {es : List Event} {vs : List Visit} (hp : t.pc = gap.stop)
      (hF : CorrectionRescaleFrame t word) (hW : Walk kernel Assumptions.all l g t es vs) :
      ∃ u pre tail rest, es = pre ++ tail ∧ u.pc = gap.stop ∧
        CorrectionRescaleFrame u word ∧
        (∀ e ∈ pre, gap.start ≤ e.pc ∧ e.pc < gap.stop ∧ isTcData e = false) ∧
        Walk kernel Assumptions.all l g u tail rest := ⟨t,[],es,vs,rfl,hp,hF,by simp,hW⟩
  induction hw with
  | stop => exact .inl (by simp)
  | @tau t u es vs ht hw ih =>
    by_cases h : t.pc = gap.stop
    · exact .inr (hCut h hFrame (.tau ht hw))
    obtain ⟨hL,hH,hs,_⟩ := gapStep gap hLo (by omega) hFrame (.inl ⟨rfl,ht⟩)
    exact ih hL hH hs
  | @ev t u e es vs he hw ih =>
    by_cases h : t.pc = gap.stop
    · exact .inr (hCut h hFrame (.ev he hw))
    obtain ⟨hL,hH,hs,hNo⟩ := gapStep gap hLo (by omega) hFrame (.inr ⟨e,rfl,he⟩)
    have hE : gap.start ≤ e.pc ∧ e.pc < gap.stop ∧ isTcData e = false := by
      rw [estep_source_pc he]
      exact ⟨hLo,by omega,hNo e (by simp)⟩
    rcases ih hL hH hs with hRest | ⟨next,pre,tail,rest,hSplit,hPc,hNext,hPre,hWalk⟩
    · exact .inl fun x hx => (List.mem_cons.mp hx).elim (· ▸ hE) (hRest x)
    · exact .inr ⟨next,e::pre,tail,rest,by rw [hSplit,List.cons_append],hPc,hNext,
        fun x hx => (List.mem_cons.mp hx).elim (· ▸ hE) (hPre x),hWalk⟩
  | @last t e he =>
    by_cases h : t.pc = gap.stop
    · exact .inr (hCut h hFrame (.last he))
    left
    intro x hx
    obtain rfl := List.mem_singleton.mp hx
    have hPc := estep_source_pc he
    obtain ⟨_,_,hf⟩ := he
    have hn : isTcData x = false := by
      rcases fires_none_ends hf with ⟨_,he⟩ | he <;> simp [isTcData,he]
    exact ⟨by omega,by omega,hn⟩

end PTX.Kernels.TmlFa4Fwd.Thread
