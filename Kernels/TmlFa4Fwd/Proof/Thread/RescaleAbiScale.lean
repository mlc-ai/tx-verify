-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxAlpha
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part068
import Lemmas.Flow.FloatOutcome
import Kernels.TmlFa4Fwd.Flow.Code.Part056
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Lemmas.Execution.EventFrameSource
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

private def scaleLoad (biased : Bool) : Nat := if biased then 3592 else 6658
private def scaleStop (biased : Bool) : Nat := if biased then 6653 else 7604

private def scaleScope (biased : Bool) (pc : Nat) : Prop :=
  scaleLoad biased < pc ∧ pc ≤ scaleStop biased

private instance (biased : Bool) (pc : Nat) : Decidable (scaleScope biased pc) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The producer retains its ABI log2 scale throughout the active arithmetic path. -/
@[no_expose] def RescaleScaleState (p : Params) (biased : Bool) (s : TState) : Prop :=
  scaleScope biased s.pc → s.regs (alphaSite biased).scale = some (b32 p.scaleLog2Bits)

private def scaleParamLoad (biased : Bool) : Op := .mem {
  kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
  addr := ⟨.param (param 12) false, 0⟩, dsts := [some (alphaSite biased).scale] }

private theorem scaleParamCode (biased : Bool) :
    kernel.code[scaleLoad biased]? = some ⟨none, scaleParamLoad biased⟩ := by
  have hName : param 12 =
      "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_obje\
      ct_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf\
      16gmemalign16o1i64div8_0_param_12" := by
    unfold param
    decide +kernel
  cases biased
  · rw [show scaleLoad false = 6658 from rfl,Flow.code_6658,scaleParamLoad,hName]
    rfl
  · rw [show scaleLoad true = 3592 from rfl,Flow.code_3592,scaleParamLoad,hName]
    rfl

private theorem scaleParamResult {p : Params} {l : Launch} {m : Mem0} {g : Nat} {s u : TState}
    (hp : Pre p l m) (biased : Bool) (hPc : s.pc = scaleLoad biased)
    (h : execLocalA Assumptions.all l g s (scaleParamLoad biased) = .ok u) :
    u.regs (alphaSite biased).scale = some (b32 p.scaleLog2Bits) := by
  have hw : (12,p.scaleLog2Bits) ∈ p.scalarWords := by simp [Params.scalarWords]
  obtain ⟨hLength,hValue⟩ := hp.values _ hw
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; cases biased <;> decide
  rw [Assumptions.execLocalA_all_eq_numeric,
    Assumptions.execLocalA_eq_nil hOff (by cases biased <;> rfl),execLocalA_nil] at h
  change (match l.params (param 12) with
    | some x => Except.ok (next (setReg s (alphaSite biased).scale (MemExt.same.extendBits 32 x)))
    | none => Except.error Fault.badParam) = .ok u at h
  rw [hValue] at h
  change Except.ok (next (setReg s (alphaSite biased).scale
    (.bits 32 (truncBits 32 (BitVec.ofNat 64 p.scaleLog2Bits))))) = .ok u at h
  rw [truncBits_ofNat hLength (by decide)] at h
  obtain rfl := Except.ok.inj h
  simp [next,setReg,b32]

private inductive ScaleResident where
  | scalar (biased : Bool)
  | negative
  | pair

private def residentStart : ScaleResident → Nat
  | .scalar biased => scaleLoad biased
  | .negative => 4398
  | .pair => 6659

private def residentStop : ScaleResident → Nat
  | .scalar biased => scaleStop biased
  | .negative | .pair => 7604

private def residentRegister : ScaleResident → Nat
  | .scalar biased => (alphaSite biased).scale
  | .negative => 1230
  | .pair => 8692

private def residentValue (p : Params) : ScaleResident → Value
  | .scalar _ => b32 p.scaleLog2Bits
  | .negative => fl (-abiFloat p.scaleLog2Bits)
  | .pair => joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits)

private def residentScope (which : ScaleResident) (pc : Nat) : Prop :=
  residentStart which < pc ∧ pc ≤ residentStop which

private instance (which : ScaleResident) (pc : Nat) : Decidable (residentScope which pc) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def ResidentScaleState (p : Params) (which : ScaleResident) (s : TState) : Prop :=
  residentScope which s.pc → s.regs (residentRegister which) = some (residentValue p which)

private def residentAudit (which : ScaleResident) (pc : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || scoreEventOp i.op) &&
    (if residentScope which pc then
      !((writesRegs i.op ++ scoreEventWrites i.op).contains (residentRegister which))
      else true) &&
    match i.op with
    | .bra target _ => decide (residentScope which target → residentScope which pc)
    | .brx .. => false
    | _ => true

private theorem residentAuditAt (which : ScaleResident) {pc : Nat} {i : Instr} (hLo : 3103 ≤ pc)
    (hHi : pc < 7742) (hc : kernel.code[pc]? = some i) : residentAudit which pc i = true := by
  let code := ((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103
  have hAll : code.all (fun (ins,site) => residentAudit which site ins) = true := by
    cases which with
    | scalar biased => cases biased <;> (set_option maxRecDepth 100000 in kernel_rfl)
    | negative => set_option maxRecDepth 100000 in kernel_rfl
    | pair => set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i,pc)
  apply List.mem_of_getElem? (i := pc-3103)
  dsimp only [code]
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

private theorem residentSegmentKeeps (which : ScaleResident) {pc : Nat} {seg : SegMatch CuteSlot}
    (hSite : pc ∈ Assumptions.swExp2Sites) (hMatch : cuteExp2.matchAt kernel pc = some seg)
    (hDest : residentScope which seg.stop) :
    residentScope which pc ∧ residentRegister which ∉ scoreSegmentWrites seg := by
  have hAll : Assumptions.swExp2Sites.all (fun src =>
      (cuteExp2.matchAt kernel src).any (fun seg =>
        !decide (residentScope which seg.stop) ||
          (decide (residentScope which src) &&
            !(scoreSegmentWrites seg).contains (residentRegister which)))) = true := by
    cases which with
    | scalar biased => cases biased <;> (set_option maxRecDepth 100000 in kernel_rfl)
    | negative => set_option maxRecDepth 100000 in kernel_rfl
    | pair => set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAll pc hSite
  simpa only [hMatch,Option.any_some,hDest,decide_true,Bool.not_true,Bool.false_or,Bool.and_eq_true,
    decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h

variable {p : Params}

private theorem residentStateStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (which : ScaleResident) (op : Op) (hEntry : kernel.code[residentStart which]? = some ⟨none,op⟩)
    (hLocalOp : op.isLocal = true)
    (hNew : s.pc = residentStart which →
      execLocalA Assumptions.all l g s op = .ok u →
      u.regs (residentRegister which) = some (residentValue p which)) (hLo : 3103 ≤ s.pc)
    (hHi : s.pc < 7742) (hSub : s.sub ≤ 3) (hPrev : ResidentScaleState p which s)
    (hStep : WStep kernel Assumptions.all l g s ev u) : ResidentScaleState p which u := by
  intro hDest
  let scaleReg := residentRegister which
  have hEnter (hPc : u.pc = s.pc+1) : residentScope which s.pc ∨ s.pc = residentStart which := by
    obtain ⟨ha,hb⟩ := hDest
    unfold residentScope
    omega
  have noWrite {i : Instr} (hc : kernel.code[s.pc]? = some i)
      (hS : residentScope which s.pc) : scaleReg ∉ writesRegs i.op ++ scoreEventWrites i.op := by
    have hAudit := residentAuditAt which hLo hHi hc
    simp only [residentAudit,Bool.and_eq_true,ite_eq_left hS,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at hAudit
    exact hAudit.1.2
  rcases hStep with ⟨rfl,hT⟩ | ⟨e,rfl,hE⟩
  · obtain ⟨i,hCode,_,hLocal⟩ := tauScoreSource hT
    rcases hLocal with ⟨rfl,hGuard⟩ | ⟨hLocal,_,hExec⟩
    · rcases hEnter rfl with hi | hLoad
      · exact hPrev hi
      · rw [hLoad,hEntry] at hCode
        obtain rfl := Option.some.inj hCode
        cases hGuard
    · by_cases hLoad : s.pc = residentStart which
      · rw [hLoad,hEntry] at hCode
        obtain rfl := Option.some.inj hCode
        exact hNew hLoad hExec
      rcases scoreExecLocal hExec with hF | ⟨seg,hSite,hMatch,hSeg⟩
      · have hAudit := residentAuditAt which hLo hHi hCode
        have hPc := hF.pc
        have hScope : residentScope which s.pc := by
          cases ho : i.op <;> simp only [ho,nextPc,BrxTarget,or_false] at hPc
          case bra target uni =>
            simp only [residentAudit,ho,Bool.and_eq_true,decide_eq_true_eq] at hAudit
            exact hAudit.2 (hPc ▸ hDest)
          case brx => simp [residentAudit,ho] at hAudit
          all_goals exact (hEnter hPc).resolve_right hLoad
        exact (hF.regs scaleReg (fun h => noWrite hCode hScope (List.mem_append_left _ h))).trans
          (hPrev hScope)
      · obtain ⟨hPc,_,_,hFrame⟩ := scoreSegmentFrame hSeg
        obtain ⟨hInside,hFree⟩ := residentSegmentKeeps which hSite hMatch (hPc ▸ hDest)
        exact (hFrame scaleReg hFree).trans (hPrev hInside)
  · obtain ⟨i,hCode,hNonlocal,hFire⟩ := estep_event_source hE
    have hAudit := residentAuditAt which hLo hHi hCode
    simp only [residentAudit,Bool.and_eq_true,hNonlocal,Bool.false_or] at hAudit
    have hLoad : s.pc ≠ residentStart which := by
      intro heq
      rw [heq,hEntry] at hCode
      obtain rfl := Option.some.inj hCode
      rw [hLocalOp] at hNonlocal
      cases hNonlocal
    have hShape := (scoreEventStep hCode hAudit.1.1 hSub
      (r := 0) (by
        -- The score-event replay always leaves register zero unused.
        have hZero : ((kernel.code.drop 3103).take (7742-3103)).all
            (fun ins => !(scoreEventWrites ins.op).contains 0) = true := by
          set_option maxRecDepth 100000 in kernel_rfl
        have hMember : i ∈ (kernel.code.drop 3103).take (7742-3103) := by
          apply List.mem_of_getElem? (i := s.pc-3103)
          rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,
            Nat.add_sub_of_le hLo,hCode]
        simpa only [Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not]
          using List.all_eq_true.mp hZero i hMember) hE).1
    have hScope : residentScope which s.pc := by
      rcases hShape.pc with ⟨hPc,_⟩ | ⟨hPc,_⟩
      · exact (hEnter hPc).resolve_right hLoad
      · exact hPc ▸ hDest
    have hKeep : scaleReg ∉ scoreEventWrites i.op :=
      fun h => noWrite hCode hScope (List.mem_append_right _ h)
    exact (scoreEventStep hCode hAudit.1.1 hSub hKeep hE).2.trans (hPrev hScope)

theorem initialRescaleScaleState (p : Params) (biased : Bool) {s : TState} (hs : s.pc = 3103) :
    RescaleScaleState p biased s := by
  intro h
  rw [hs] at h
  cases biased <;> exact False.elim ((by decide : ¬ scaleScope _ 3103) h)

theorem rescaleScaleStateStep {l : Launch} {m : Mem0} {g : Nat} {s u : TState} {ev : Option Event}
    (hp : Pre p l m) (biased : Bool) (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742) (hSub : s.sub ≤ 3)
    (hPrev : RescaleScaleState p biased s) (hStep : WStep kernel Assumptions.all l g s ev u)
    : RescaleScaleState p biased u :=
  residentStateStep (.scalar biased) (scaleParamLoad biased)
    (scaleParamCode biased) (by cases biased <;> rfl) (scaleParamResult hp biased)
    hLo hHi hSub hPrev hStep

private def negativeScaleOp : FloatInstr :=
  { op := .neg, ty := ⟨.f32,1⟩, dsts := [some 1230], srcs := [.reg 7132] }

private def pairedScaleOp : Op :=
  .move ⟨.pack,.int .b 64,[some 8692],[.reg 7133,.reg 7133]⟩

private theorem negativeScaleResult {l : Launch} {m : Mem0} {g : Nat} {s u : TState}
    (hp : Pre p l m) (hScale : s.regs 7132 = some (b32 p.scaleLog2Bits)) (hs : s.pc = 4398)
    (hExec : execLocalA Assumptions.all l g s (.float negativeScaleOp) = .ok u) :
    u.regs 1230 = some (fl (-abiFloat p.scaleLog2Bits)) := by
  have hWord := (hp.values (12,p.scaleLog2Bits) (by simp [Params.scalarWords])).1
  obtain ⟨q,_,hDecode,_,hPos,_⟩ := hp.scales
  have hOff : s.pc ∉ Assumptions.swExp2Sites := hs ▸ (by decide)
  rw [Assumptions.execLocalA_all_eq_numeric] at hExec
  have hSeg : SegFreeAt Assumptions.numeric l g s :=
    (Assumptions.numeric_segSites.pc hOff).at rfl
  have hNone : ∀ a ∈ Assumptions.numeric, a.localRule l g s (.float negativeScaleOp) = none := by
    intro a ha
    simp only [Assumptions.numeric,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hSeg.exec,execLocalRule_of_none hNone] at hExec
  have hLayout : FloatFmt.f32.layout.decode p.scaleLog2Bits = some (.fin q) := by
    obtain ⟨x,hD,hNum⟩ := Option.bind_eq_some_iff.mp hDecode
    cases x with
    | fin k => rw [Option.some.inj hNum] at hD; exact hD
    | zero z => exact (lt_irrefl _ ((Option.some.inj hNum).symm ▸ hPos)).elim
    | inf z => cases hNum
    | nan z => cases hNum
  have hClass : classify .f32 (b32 p.scaleLog2Bits) = .ok (.fin q) :=
    classify_bits (by omega) hLayout
  change execFloat l g s negativeScaleOp = .ok u at hExec
  have hv : abiFloat p.scaleLog2Bits = (q : ℝ) := by simp [abiFloat,hDecode]
  simp [execFloat,negativeScaleOp,FloatInstr.lane,FloatInstr.ieee,FloatInstr.flushIn,
    FVal.negate,FVal.toValue,floatLane,hScale,readValue,readReg,hClass,bind,Except.bind,
    pure,Except.pure,boolCombine,FloatInstr.rule,Rat.cast_neg,← hv] at hExec
  obtain rfl := hExec
  simp [next,setReg,fl]

private theorem pairedScaleResult {l : Launch} {g : Nat} {s u : TState}
    (hScale : s.regs 7133 = some (b32 p.scaleLog2Bits)) (hs : s.pc = 6659)
    (hExec : execLocalA Assumptions.all l g s pairedScaleOp = .ok u) :
    u.regs 8692 = some (joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits)) := by
  have hOff : s.pc ∉ Assumptions.swExp2Sites := hs ▸ (by decide)
  change execLocalA Assumptions.all l g s
    (.move ⟨.pack,.int .b 64,[some 8692],[.reg 7133,.reg 7133]⟩) = .ok u at hExec
  rw [Assumptions.execLocalA_all_eq_numeric,Assumptions.execLocalA_eq_nil hOff rfl,
    exec_packE (by simp [CoreMoves]) (by simp [NoSegments]) hScale hScale] at hExec
  have hBytes : (b32 p.scaleLog2Bits).bytes = 4 := rfl
  simp only [packE,hBytes,and_self,ite_true,Except.map,Except.ok.injEq] at hExec
  obtain rfl := hExec
  simp [next,setReg]

@[no_expose] def ShiftScaleFrame (p : Params) (s : TState) : Prop :=
  (∀ biased, RescaleScaleState p biased s) ∧
    ResidentScaleState p .negative s ∧ ResidentScaleState p .pair s

theorem shiftScaleFrameStep {l : Launch} {m : Mem0} {g : Nat} {s u : TState} {ev : Option Event}
    (hp : Pre p l m) (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742) (hSub : s.sub ≤ 3)
    (hFrame : ShiftScaleFrame p s) (hStep : WStep kernel Assumptions.all l g s ev u) :
    ShiftScaleFrame p u := by
  refine ⟨fun b => rescaleScaleStateStep hp b hLo hHi hSub (hFrame.1 b) hStep,?_,?_⟩
  · apply residentStateStep .negative (.float negativeScaleOp) Flow.code_4398 rfl _ hLo hHi
      hSub hFrame.2.1 hStep
    intro hs hExec
    exact negativeScaleResult hp (hFrame.1 true (hs.symm ▸ (by decide : scaleScope true 4398)))
      hs hExec
  · apply residentStateStep .pair pairedScaleOp Flow.code_6659 rfl _ hLo hHi hSub hFrame.2.2 hStep
    intro hs hExec
    exact pairedScaleResult (hFrame.1 false (hs.symm ▸ (by decide : scaleScope false 6659)))
      hs hExec

theorem initialShiftScaleFrame (p : Params) {s : TState} (hPc : s.pc = 3103) :
    ShiftScaleFrame p s := by
  refine ⟨fun b => initialRescaleScaleState p b hPc,?_,?_⟩
  · intro h
    exact ((by decide : ¬ residentScope .negative 3103) (hPc ▸ h)).elim
  · intro h
    exact ((by decide : ¬ residentScope .pair 3103) (hPc ▸ h)).elim

theorem scalarScaleInShiftFrame {s : TState} (hFrame : ShiftScaleFrame p s) (biased : Bool)
    : RescaleScaleState p biased s :=
  hFrame.1 biased

theorem shiftScalesOfFrame {s : TState} (hFrame : ShiftScaleFrame p s) (hLo : 4399 ≤ s.pc)
    (hHi : s.pc ≤ 7604) :
    s.regs 1230 = some (fl (-abiFloat p.scaleLog2Bits)) ∧
      (6660 ≤ s.pc → s.regs 8692 =
        some (joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits))) :=
  ⟨hFrame.2.1 ⟨by change 4398 < s.pc; omega,hHi⟩,
    fun hPair => hFrame.2.2 ⟨by change 6659 < s.pc; omega,hHi⟩⟩

theorem shiftScaleAbiAtScoreLoad {s : TState} (biased : Bool) (hFrame : ShiftScaleFrame p s)
    (hPc : s.pc = scorePc (if biased then .biased else .unbiased) 0) :
    s.regs (alphaSite biased).scale = some (b32 p.scaleLog2Bits) := by
  apply scalarScaleInShiftFrame hFrame biased
  rw [hPc]
  cases biased <;> decide

theorem shiftScaleAbiAtBiasWait {s : TState} (hFrame : ShiftScaleFrame p s) (hPc : s.pc = 5181) :
    s.regs 7132 = some (b32 p.scaleLog2Bits) :=
  scalarScaleInShiftFrame hFrame true (hPc.symm ▸ (by decide : scaleScope true 5181))

/-- The ABI scale word denotes the launch scaling constant. -/
theorem rescaleAbiScaleWord {l : Launch} {m : Mem0} (hp : Pre p l m) :
    readEReal .f32 (b32 p.scaleLog2Bits) = some (.ok (abiFloat p.scaleLog2Bits : EReal)) := by
  have hw := (hp.values (12,p.scaleLog2Bits) (by simp [Params.scalarWords])).1
  obtain ⟨q,_,hq,_,_,_⟩ := hp.scales
  have hRead := valFloat_b32 (by omega : p.scaleLog2Bits < 2^64) hq
  apply readEReal_of_valFloat
  simpa only [abiFloat,hq,Option.getD_some] using hRead

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
