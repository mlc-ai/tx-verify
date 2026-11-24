-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTmemLoads
import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeBridge
public import Kernels.TmlFa4Fwd.Proof.CorrectionTmemStores
public import Lemmas.Flow.WarpUniform
import Lemmas.Flow.TcLdTmpl
import Lemmas.Flow.ElemAccess
import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsRead
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
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Flow.Code.Part121

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.EventFrame PTX.Flow PTX.Proof Prologue Softmax
open PTX.Kernels.TmlFa4Fwd.Correction

private inductive ColumnCalc
  | thread
  | row
  | rowWarp
  | laneField
  | base (column : Nat)
  | offset (column : Nat)
  deriving DecidableEq

private def ColumnCalc.source : ColumnCalc → Option (Nat × ColumnCalc)
  | .thread => none
  | .row => some (1612,.thread)
  | .rowWarp => some (1613,.row)
  | .laneField => some (5952,.rowWarp)
  | .base _ => some (5953,.laneField)
  | .offset _ => some (1629,.base 256)

private def laneFieldWord (l : Launch) (g : Nat) : Nat :=
  (rowOf l g / 32) * 2 ^ 21

private def ColumnCalc.value (l : Launch) (g : Nat) : ColumnCalc → Nat
  | .thread => g % l.block
  | .row => rowOf l g
  | .rowWarp => rowOf l g / 32
  | .laneField => laneFieldWord l g
  | .base column | .offset column => laneFieldWord l g + column

private def intDefinition (op : IntOp) (ty : IType) (reg src imm : Nat) : IntInstr :=
  ⟨op,.int ty 32,false,[some reg],[.reg src,.imm imm]⟩

private def ColumnCalc.intCode (reg : Nat) : ColumnCalc → Option IntInstr
  | .thread => none
  | .row => some (intDefinition .and .b reg 1612 127)
  | .rowWarp => some (intDefinition .shr .u reg 1613 5)
  | .laneField => some (intDefinition .shl .b reg 5952 21)
  | .base col => some (intDefinition .or .b reg 5953 col)
  | .offset col => some (intDefinition .add .s reg 1629 (col - 256))

private structure ColumnFact where
  source : Nat
  last : Nat
  reg : Nat
  formula : ColumnCalc

private def ColumnFact.active (f : ColumnFact) (site : Nat) : Prop :=
  f.source < site ∧ site ≤ f.last

private instance (f : ColumnFact) (site : Nat) : Decidable (f.active site) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def fixedColumnFacts : List ColumnFact :=
  [⟨7748,7749,1612,.thread⟩,⟨7749,7938,1613,.row⟩,⟨7938,7939,5952,.rowWarp⟩,
    ⟨7939,7949,5953,.laneField⟩,⟨7940,9057,1629,.base 256⟩,⟨7949,9057,1633,.base 384⟩]

private def rescaleColumns : List ColumnFact := (List.finRange 2).flatMap fun stage =>
  (List.finRange 8).filterMap fun chunk =>
    if 0 < chunk.val then
      some ⟨7990 + 7 * stage.val + chunk.val,8446,rescaleAddressReg stage chunk,
        .offset (256 + 128 * stage.val + 16 * chunk.val)⟩
    else none

private def finalColumns : List ColumnFact := (List.finRange 2).flatMap fun stage =>
  (List.finRange 16).filterMap fun chunk =>
    if 0 < chunk.val then
      some ⟨finalizeBridgePc stage chunk,finalizeLoadPc stage chunk,finalizeAddressReg stage chunk,
        .offset (256 + 128 * stage.val + 8 * chunk.val)⟩
    else none

private def columnFacts := fixedColumnFacts ++ rescaleColumns ++ finalColumns

private def intPlain : Instr → Option IntInstr
  | ⟨none,.int code⟩ => some code
  | _ => none

private def columnCode (site : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || correctionReturningOp i.op) && columnFacts.all (fun f =>
    (!decide (f.active site) || !(writesRegs i.op ++ scoreEventWrites i.op).contains f.reg) &&
    (if f.source = site then i.guard.isNone && i.op.isLocal else true) &&
    match i.op with
    | .bra dst _ => !decide (f.active dst) || decide (f.active site)
    | .brx .. => false
    | _ => true)

private def correctionBand := ((kernel.code.drop 7745).take (9205 - 7745)).zipIdx 7745

set_option maxRecDepth 100000 in
private theorem columnCodeAudit :
    correctionBand.all (fun (i,site) => columnCode site i) = true := by decide +kernel

private theorem columnDefinitionAudit :
    columnFacts.all (fun f => if f.source = 7748 then true else
      decide (kernel.code[f.source]?.bind intPlain = f.formula.intCode f.reg)) = true := by
  decide +kernel

private theorem columnDepsAudit :
    columnFacts.all (fun f => match f.formula.source with
      | none => true
      | some (r,c) => columnFacts.any (fun d => d.reg == r && decide (d.formula = c) &&
          decide (d.active f.source))) = true := by decide +kernel

private theorem columnValueAudit :
    columnFacts.all (fun f => match f.formula with
      | .base col => 256 ≤ col && col < 512
      | .offset col => 256 ≤ col && col < 512
      | _ => true) = true := by decide +kernel

private def ColumnCalc.bounded : ColumnCalc → Prop
  | .base col | .offset col => 256 ≤ col ∧ col < 512
  | _ => True

variable {p : Params} {l : Launch} {m : Mem0}

private theorem columnCalcExec (hp : Pre p l m) {g d r : Nat} {s : TState} {c arg : ColumnCalc}
    {code : IntInstr} (hCode : c.intCode d = some code) (hSrc : c.source = some (r,arg))
    (hReg : s.regs r = some (b32 (arg.value l g))) (hBound : c.bounded) :
    execLocalA [] l g s (.int code) = .ok (next (setReg s d (b32 (c.value l g)))) := by
  let tid := g % l.block
  let row := rowOf l g
  let part := row / 32
  let high := laneFieldWord l g
  have hTid : tid < 512 := by unfold tid; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hRow : row < 128 := Nat.mod_lt _ (by decide)
  have hPart : part < 4 := by dsimp [part]; omega
  have hHigh : high < 2 ^ 23 := by dsimp [high,laneFieldWord,part] at *; omega
  cases c with
  | thread => cases hSrc
  | row =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hSrc.symm)
    obtain rfl := Option.some.inj hCode.symm
    have hValue : BitVec.ofNat 64 tid &&& 127 = BitVec.ofNat 64 row := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, toNat_ofNat_lt (by omega), show (127 : BitVec 64).toNat = 127 by rfl,
        toNat_ofNat_lt (by omega)]
      exact Nat.and_two_pow_sub_one_eq_mod tid 7
    rw [execLocalA_nil,execLocal_int rfl]
    simp only [intDefinition,execInt,DType.width,ColumnCalc.value,readBits_b32 hReg (by
      change tid < 2 ^ 32; omega), bind,Except.bind,pure,Except.pure]
    change Except.ok (next (setReg s d (.bits 32 (BitVec.ofNat 64 tid &&& 127)))) = _
    rw [hValue]
    rfl
  | rowWarp =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hSrc.symm)
    obtain rfl := Option.some.inj hCode.symm
    have hValue : BitVec.ofNat 64 row >>> 5 = BitVec.ofNat 64 part := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight,toNat_ofNat_lt (by omega),toNat_ofNat_lt (by omega)]
      exact Nat.shiftRight_eq_div_pow row 5
    rw [execLocalA_nil,execLocal_int rfl]
    simp only [intDefinition,execInt,DType.width,DType.kind?,ColumnCalc.value,readBits_b32 hReg (by
      change row < 2 ^ 32; omega), bind,Except.bind,pure,Except.pure]
    change Except.ok (next (setReg s d (.bits 32 (BitVec.ofNat 64 row >>> 5)))) = _
    rw [hValue]
    rfl
  | laneField =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hSrc.symm)
    obtain rfl := Option.some.inj hCode.symm
    have hShift : BitVec.ofNat 64 part <<< 21 = BitVec.ofNat 64 high := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft,toNat_ofNat_lt (by omega),toNat_ofNat_lt (by omega),
        Nat.shiftLeft_eq]
      change high % 2 ^ 64 = high
      exact Nat.mod_eq_of_lt (by omega)
    rw [execLocalA_nil, execLocal_int rfl]
    simp only [intDefinition,execInt,DType.width,ColumnCalc.value,readBits_b32 hReg (by
      change part < 2 ^ 32; omega), bind,Except.bind,pure,Except.pure]
    change Except.ok (next (setReg s d (.bits 32 (truncBits 32
      (BitVec.ofNat 64 part <<< 21))))) = _
    rw [hShift,truncBits_ofNat (by omega) (by decide)]
    rfl
  | base col =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hSrc.symm)
    obtain rfl := Option.some.inj hCode.symm
    have hCol : col < 512 := hBound.2
    have hOperand := truncBits_ofNat (show col < 2 ^ 32 by omega) (by decide : 32 ≤ 64)
    have hOr : high ||| col = high + col := by
      have h := Nat.two_pow_add_eq_or_of_lt (i := 21) (show col < 2 ^ 21 by omega) part
      simpa only [high,laneFieldWord,part,Nat.mul_comm (2 ^ 21)] using h.symm
    have hValue : BitVec.ofNat 64 high ||| BitVec.ofNat 64 col = BitVec.ofNat 64 (high+col) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_or,toNat_ofNat_lt (by omega),toNat_ofNat_lt (by omega),
        toNat_ofNat_lt (by omega)]
      exact hOr
    rw [execLocalA_nil, execLocal_int rfl]
    simp only [intDefinition, execInt, DType.width, ColumnCalc.value, readBits_b32 hReg (by
      change high < 2 ^ 32; omega), bind, Except.bind, pure, Except.pure]
    have himm : readBits l g s 32 (.imm (col : Int)) = .ok (BitVec.ofNat 64 col) := by
      simp only [readBits, BitVec.ofInt_natCast, hOperand, pure, Except.pure]
    simp only [show (32 : Nat) ≠ 1 by decide,ite_false,himm]
    change Except.ok (next (setReg s d (.bits 32
      (BitVec.ofNat 64 high ||| BitVec.ofNat 64 col)))) = _
    rw [hValue]
    rfl
  | offset col =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hSrc.symm)
    obtain rfl := Option.some.inj hCode.symm
    have hMin : 256 ≤ col := hBound.1
    have hCol : col < 512 := hBound.2
    have hBase : high + 256 < 2 ^ 32 := by omega
    have hAdd : high + 256 + (col - 256) = high + col := by omega
    have hOperand := truncBits_ofNat (show col - 256 < 2 ^ 32 by omega) (by decide : 32 ≤ 64)
    rw [execLocalA_nil, execLocal_int rfl]
    have hOp : readBits l g s 32 (.imm ((col - 256 : Nat) : Int)) =
        .ok (BitVec.ofNat 64 (col - 256)) := by
      simp only [readBits,BitVec.ofInt_natCast,hOperand,pure,Except.pure]
    have hVal : readValue l g s 32 (.imm ((col - 256 : Nat) : Int)) = .ok (b32 (col - 256)) := by
      let delta : Int := (col - 256 : Nat)
      change Except.ok (Value.bits 32 (truncBits 32 (BitVec.ofInt 64 delta))) = _
      dsimp only [delta]
      rw [BitVec.ofInt_natCast,hOperand]
      rfl
    have hA : readValue l g s 32 (.reg 1629) = .ok (b32 (high + 256)) := by
      simp only [readValue,readReg,hReg,pure,Except.pure]
      rfl
    simp only [intDefinition,execInt,DType.width,hA,bind,Except.bind,pure,Except.pure]
    rw [hVal]
    simp only [readBits_b32 hReg hBase, hOp]
    change Except.ok (next (setReg s d (.bits 32 (truncBits 32
      (BitVec.ofNat 64 (high+256) + BitVec.ofNat 64 (col - 256)))))) = _
    rw [← BitVec.ofNat_add,hAdd,truncBits_ofNat (by omega) (by decide)]
    rfl

private def columnFrame (l : Launch) (g : Nat) (s : TState) : Prop :=
  ∀ f ∈ columnFacts, f.active s.pc → s.regs f.reg = some (b32 (f.formula.value l g))

private theorem columnCodeAt {site : Nat} {i : Instr} (hLo : 7745 ≤ site) (hHi : site < 9205)
    (hc : kernel.code[site]? = some i) : columnCode site i = true := by
  apply List.all_eq_true.mp columnCodeAudit (i,site)
  apply List.mem_of_getElem? (i := site - 7745)
  dsimp only [correctionBand]
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

private theorem columnDefinitionSites :
    columnFacts.all (fun f => decide ((f.source = 7748 ↔ f.formula = .thread) ∧
      (f.formula = .thread → f.reg = 1612) ∧
      f.source ∉ Assumptions.swExp2Sites ∧ f.source ∉ Assumptions.tcLdDataflowSites ∧
      f.source ∉ Assumptions.delayedTmemSites)) = true := by decide +kernel

private theorem columnDefinitionStep (hp : Pre p l m) {g : Nat} {s u : TState} {f : ColumnFact}
    (hFact : f ∈ columnFacts) (hPc : s.pc = f.source) (hLo : 7745 ≤ s.pc) (hHi : s.pc < 9205)
    (hNormal : s.fault = none) (hFrame : columnFrame l g s)
    (hTau : Tau kernel Assumptions.all l g s u) :
    u.regs f.reg = some (b32 (f.formula.value l g)) := by
  obtain ⟨hThread, hReg, hExp, hLd, hSt⟩ :=
    of_decide_eq_true (List.all_eq_true.mp columnDefinitionSites f hFact)
  have run {op : Op} (hc : kernel.code[s.pc]? = some ⟨none,op⟩) (hLocal : op.isLocal = true)
      (hCore : Assumptions.coreOp op = true)
      (he : execLocalA [] l g s op = .ok (next (setReg s f.reg (b32 (f.formula.value l g))))) :
      u.regs f.reg = some (b32 (f.formula.value l g)) := by
    unfold Tau at hTau
    rw [Assumptions.out_all_eq_nil (hPc.symm ▸ hExp) (hPc.symm ▸ hLd) (hPc.symm ▸ hSt) hc hCore]
      at hTau
    simp only [out,hNormal,hc,guardHolds,pure,Except.pure,hLocal,↓reduceIte,he,
      Out.tau.injEq] at hTau
    subst u
    exact Function.update_self _ _ _
  cases hArg : f.formula.source with
  | none =>
    have hF : f.formula = .thread := by cases h : f.formula <;> simp_all [ColumnCalc.source]
    have hOrigin := hThread.mpr hF
    have hc := hPc.trans hOrigin |>.symm ▸ Flow.code_7748
    apply run hc rfl rfl
    rw [hF,hReg hF,execLocalA_nil,execLocal_move rfl]
    have hTid : g % l.block < 2 ^ 32 := by rw [hp.block]; omega
    have hsreg := (sregValue_oneDim hp.cluster.2.2 g).1
    simp [ColumnCalc.value,execMove,readValue,readBits,SReg.width,hsreg,DType.width,Value.bytes,
      b32,bind,Except.bind,pure,Except.pure,truncBits_ofNat hTid (by decide)]
  | some pair =>
    obtain ⟨r,arg⟩ := pair
    have hNot : f.formula ≠ .thread := by
      intro h
      rw [h] at hArg
      cases hArg
    have hN : f.source ≠ 7748 := fun h => hNot (hThread.mp h)
    have hLookup := List.all_eq_true.mp columnDefinitionAudit f hFact
    rw [ite_eq_right hN] at hLookup
    have hDeps := List.all_eq_true.mp columnDepsAudit f hFact
    rw [hArg] at hDeps
    obtain ⟨dep,hDep,hDepOK⟩ := List.any_eq_true.mp hDeps
    simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hDepOK
    have hValue := hFrame dep hDep (hPc.symm ▸ hDepOK.2)
    rw [hDepOK.1.1,hDepOK.1.2] at hValue
    have hBound : f.formula.bounded := by
      have h := List.all_eq_true.mp columnValueAudit f hFact
      cases hF : f.formula <;> simp only [ColumnCalc.bounded]
      all_goals simpa only [hF, Bool.and_eq_true, decide_eq_true_eq] using h
    have hSome : (f.formula.intCode f.reg).isSome = true := by
      cases h : f.formula <;> simp_all [ColumnCalc.intCode]
    obtain ⟨code,hCode⟩ := Option.isSome_iff_exists.mp hSome
    have hProjection := of_decide_eq_true hLookup
    rw [hCode] at hProjection
    obtain ⟨ins, hIns, hInt⟩ := Option.bind_eq_some_iff.mp hProjection
    have hi : ins = ⟨none,.int code⟩ := by
      cases ins with
      | mk guard op =>
        cases guard <;> cases op <;> simp_all [intPlain]
    rw [hi] at hIns
    have hc : kernel.code[s.pc]? = some ⟨none,.int code⟩ := hPc.symm ▸ hIns
    have hChecked := List.all_eq_true.mp
      (Bool.and_eq_true_iff.mp (columnCodeAt hLo hHi hc)).2 f hFact
    have hLocal := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hChecked).1).2
    rw [hPc] at hLocal
    simp only [Option.isNone_none, Bool.true_and] at hLocal
    exact run hc hLocal rfl (columnCalcExec hp hCode hArg hValue hBound)

private theorem allOrdinary :
    kernel.code.all (fun i => i.op.isLocal || Epilogue.ordinaryEvent i.op) = true :=
  by decide +kernel

private theorem columnFrameStep (hp : Pre p l m) {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 7745 ≤ s.pc) (hHi : s.pc < 9205) (hSub : s.sub ≤ 3) (hFrame : columnFrame l g s)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    columnFrame l g u := by
  intro f hFact hUse
  have hChecked {i : Instr} (hc : kernel.code[s.pc]? = some i) :=
    List.all_eq_true.mp (Bool.and_eq_true_iff.mp (columnCodeAt hLo hHi hc)).2 f hFact
  have retain {i : Instr} (hc : kernel.code[s.pc]? = some i)
      (hKeep : ∀ r, r ∉ writesRegs i.op ++ scoreEventWrites i.op → u.regs r = s.regs r)
      (hOld : f.active s.pc) : u.regs f.reg = some (b32 (f.formula.value l g)) := by
    have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (hChecked hc)).1).1
    have hNot : f.reg ∉ writesRegs i.op ++ scoreEventWrites i.op := by
      simpa [hOld] using h
    exact (hKeep f.reg hNot).trans (hFrame f hFact hOld)
  have fall (hNext : u.pc = s.pc + 1) (hNe : s.pc ≠ f.source) : f.active s.pc := by
    unfold ColumnFact.active at hUse ⊢
    omega
  rcases hStep with ⟨_,ht⟩ | ⟨event,_,he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false]
      omega
    obtain ⟨i,hc,hClean,hTau⟩ := correctionTauFrame hOff ht
    by_cases hSource : s.pc = f.source
    · exact columnDefinitionStep hp hFact hSource hLo hHi hClean hFrame ht
    rcases hTau with ⟨rfl,_⟩ | ⟨_,_,hLocal⟩
    · exact retain hc (fun _ _ => rfl) (fall rfl hSource)
    apply retain hc (fun r hNo => hLocal.regs r (fun h => hNo (List.mem_append_left _ h)))
    have hPC := hLocal.pc
    have hBranch := (Bool.and_eq_true_iff.mp (hChecked hc)).2
    cases hi : i.op <;> simp only [hi,nextPc,BrxTarget,or_false] at hPC
    case bra target aligned =>
      have hAt : f.active target := hPC ▸ hUse
      simpa [hi,hAt] using hBranch
    case brx => simp [hi] at hBranch
    all_goals exact fall hPC hSource
  · obtain ⟨i,hc,hNonlocal,hFire⟩ := estep_event_source he
    have hNe : s.pc ≠ f.source := by
      intro h
      have hLocal := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (hChecked hc)).1).2
      simp [h, hNonlocal] at hLocal
    have hOp := (Bool.and_eq_true_iff.mp (columnCodeAt hLo hHi hc)).1
    rw [hNonlocal,Bool.false_or] at hOp
    apply retain hc
    · intro r hNo
      exact (correctionEventProgress hc hOp hSub (fun h => hNo (List.mem_append_right _ h)) he).2
    · have hOrd := List.all_eq_true.mp allOrdinary i (List.mem_of_getElem? hc)
      rw [hNonlocal,Bool.false_or] at hOrd
      have hForward := callbackFrame_fires (Epilogue.ordinaryEventFrame (A := Assumptions.all)
        (l := l) (g := g) (s := s) hOrd) hFire
      exact hForward.elim (fun h => h ▸ hUse) (fun h => fall h hNe)

private theorem laneFieldEq (l : Launch) (g : Nat) : laneFieldWord l g = 2 ^ 16 * laneBase l g := by
  have hRow : rowOf l g / 32 = g % l.block / 32 % 4 := by
    change (g % l.block % 128) / 32 = _
    omega
  unfold laneFieldWord laneBase
  rw [hRow]
  omega

private def outputFormula (stage : Fin 2) (col : Nat) : ColumnCalc :=
  let offset := 256 + 128 * stage.val + col
  if col = 0 then .base offset else .offset offset

private theorem outputFormulaValue (l : Launch) (g : Nat) (stage : Fin 2) (col : Nat) :
    (outputFormula stage col).value l g = outputAddress l g stage col := by
  unfold outputFormula
  dsimp only
  split <;> simp only [ColumnCalc.value,laneFieldEq,outputAddress,outputColumn]

private def usableWord (site reg : Nat) (form : ColumnCalc) : Bool :=
  columnFacts.any (fun f => f.reg == reg && decide (f.formula = form) && decide (f.active site))

private theorem rescaleLoadWord : ∀ (stage : Fin 2) (chunk : Fin 8),
    usableWord (rescaleLoadPc stage chunk) (rescaleAddressReg stage chunk)
      (outputFormula stage (16 * chunk.val)) = true := by decide +kernel

private theorem rescaleStoreWord : ∀ (stage : Fin 2) (chunk : Fin 8),
    usableWord (rescaleStorePc stage chunk) (rescaleAddressReg stage chunk)
      (outputFormula stage (16 * chunk.val)) = true := by decide +kernel

private theorem finalizeLoadWord : ∀ (stage : Fin 2) (chunk : Fin 16),
    usableWord (finalizeLoadPc stage chunk) (finalizeAddressReg stage chunk)
      (outputFormula stage (8 * chunk.val)) = true := by decide +kernel

private theorem outputWord {l : Launch} {g : Nat} {s : TState} {reg col : Nat} {stage : Fin 2}
    (hFrame : columnFrame l g s) (hc : usableWord s.pc reg (outputFormula stage col) = true) :
    s.regs reg = some (b32 (outputAddress l g stage col)) := by
  obtain ⟨f,hf,hReady⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hReady
  have hValue := hFrame f hf hReady.2
  rw [hReady.1.1,hReady.1.2,outputFormulaValue] at hValue
  exact hValue

private theorem observedCorrectionColumn {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j site reg col : Nat} {kind : Kind}
    {stage : Fin 2} (he : X.get (g,j) = some ⟨site, kind⟩) (hBand : 8006 ≤ site ∧ site < 9057)
    (hAddr : usableWord site reg (outputFormula stage col) = true) :
    ∃ s o, s.pc = site ∧ s.regs reg = some (b32 (outputAddress l g stage col)) ∧
      EStep kernel Assumptions.all l g s ⟨site,kind⟩ o := by
  have hHint : site ∉ registerHintSites := by simp [registerHintSites]; omega
  have hRole := roleBodyPcOfEvent hp hX he (by change 173 < site; omega) hHint
  change roleBodyPc (warpIndex l g) site at hRole
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨s,o,hs,_,hFrame,hStep⟩ := correctionRoleEventWith hp hX hWarp.1 hWarp.2
    he (by change 173 < site; omega) (by change site < 9205; omega)
    (Q := columnFrame l g) (by
      intro t ht f hf hActive
      rw [ht.1] at hActive
      have hOff : columnFacts.all (fun f => !decide (f.active 7745)) = true := by decide +kernel
      have h := List.all_eq_true.mp hOff f hf
      simp [hActive] at h)
    (fun hLo hHi hSub hFrame hw => columnFrameStep hp hLo hHi hSub hFrame hw)
  change s.pc = site at hs
  exact ⟨s,o,hs,outputWord hFrame (hs.symm ▸ hAddr),hStep⟩

private theorem observedLoadAtColumn {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j site reg col address : Nat} {stage : Fin 2}
    {ds : List Nat} {values : List Value} {shape : TcShape}
    (he : X.get (g,j) = some ⟨site, .tc (.ld address values shape)⟩)
    (hBand : 8006 ≤ site ∧ site < 9057)
    (hUse : usableWord site reg (outputFormula stage col) = true)
    (hc : kernel.code[site]? = some ⟨none,.tcLd ds reg .s32x32b none⟩) (hCol : col < 128) :
    address = outputAddress l g stage col ∧ shape = .s32x32b ∧ values.length = ds.length := by
  obtain ⟨s, _, hs, hAddr, hStep⟩ := observedCorrectionColumn hp hX he hBand hUse
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨_, rfl⟩ | ⟨_, hCode, rfl⟩
  · cases congrArg Event.kind hFire.1
  rw [hs,hc] at hCode
  obtain rfl := Option.some.inj hCode.symm
  have hWidth : outputAddress l g stage col < 2 ^ 32 := by
    apply tmem_warp_encoding_lt
    have hCeil := outputColumn_range stage
    omega
  have hLen := fires_tcLd_len (by intro sh h; cases h) hFire rfl
  have hData : isTcData ⟨site,.tc (.ld address values shape)⟩ = true := rfl
  have core {o : Option TState}
      (hf : Fires s.pc (tcTmpl l g s (.tcLd ds reg .s32x32b none))
        ⟨site,.tc (.ld address values shape)⟩ o) :
      address = outputAddress l g stage col ∧ shape = .s32x32b := by
    rw [tcTmpl_tcLd_none (by intro sh h; cases h)] at hf
    obtain ⟨_, _, hEq⟩ := fires_tcLd_ofTmpl hAddr hWidth hData hf
    have h := TcKind.ld.inj (Kind.tc.inj (congrArg Event.kind hEq))
    exact ⟨h.1,h.2.2⟩
  have hRead : address = outputAddress l g stage col ∧ shape = .s32x32b := by
    rcases eventTmpl_tcLd_cases (A := Assumptions.all) (L := l) (g := g) (t := s)
      (ds := ds) (ta := reg) (sh := .s32x32b) with hh | hh | hh <;> rw [hh] at hFire
    · exact core hFire
    · obtain ⟨_, hFire⟩ := fires_thenWaitLd hFire
      exact core hFire
    · have hEq := congrArg Event.kind hFire.1
      cases hEq
  exact ⟨hRead.1,hRead.2,hLen⟩

/-- The actual rescale load starts with its computed address and retains the rest of its trace. -/
theorem actualRescaleLoadStateWith {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) (chunk : Fin 8)
    {g index address : Nat} {values : List Value} {shape : TcShape}
    (he : X.get (g,index) = some ⟨rescaleLoadPc stage chunk,.tc (.ld address values shape)⟩)
    {Q : Nat → TState → Prop}
    (hInit : ∀ t, At t 7745 ((1072,b32 (g/l.block)) :: nonzeroBarrierFacts p l g) → Q 5 t)
    (hStep : ∀ {s u ev position}, 7745 ≤ s.pc → s.pc < 9205 → s.sub ≤ 3 → s.acc = [] →
      Q position s → WStep kernel Assumptions.all l g s ev u →
      (∀ e ∈ ev.toList, X.get (g,position) = some e) → Q (position + ev.toList.length) u) :
    ∃ t ending, At t (rescaleLoadPc stage chunk) [] ∧
      t.regs (rescaleAddressReg stage chunk) =
        some (b32 (outputAddress l g stage (16 * chunk.val))) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop index) ending ∧
      Q index t := by
  have hRange : 173 < rescaleLoadPc stage chunk ∧ rescaleLoadPc stage chunk < 9205 ∧
      rescaleLoadPc stage chunk ∉ registerHintSites := by
    fin_cases stage <;> fin_cases chunk <;> decide
  have hRole := roleBodyPcOfEvent hp hX he hRange.1 hRange.2.2
  change roleBodyPc (warpIndex l g) (rescaleLoadPc stage chunk) at hRole
  have hBand : 8006 ≤ rescaleLoadPc stage chunk ∧ rescaleLoadPc stage chunk < 9057 := by
    fin_cases stage <;> fin_cases chunk <;> decide
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨t,_,ending,hSite,_,hFrame,hEvent,hRun⟩ := correctionRoleEventAt hp hX hWarp.1 hWarp.2
    he hRange.1 hRange.2.1 (Q := fun pos s => columnFrame l g s ∧ SetupScratch s ∧ Q pos s)
    (by
      intro t ht
      refine ⟨?_,SetupScratch.clear ht.2.1 ht.2.2.1,hInit t ht⟩
      intro fact hFact hActive
      rw [ht.1] at hActive
      have hOff : columnFacts.all (fun f => !decide (f.active 7745)) = true := by decide +kernel
      have h := List.all_eq_true.mp hOff fact hFact
      simp [hActive] at h)
    (fun hLo hHi hSub hf hw hr => ⟨columnFrameStep hp hLo hHi hSub hf.1 hw,
      (correctionScratchStep hLo hHi hSub hf.2.1 hw).1,
      hStep hLo hHi hSub hf.2.1.clearAccumulator hf.2.2 hw hr⟩)
  have hPc : t.pc = rescaleLoadPc stage chunk := hSite
  have hAddr : t.regs (rescaleAddressReg stage chunk) =
      some (b32 (outputAddress l g stage (16 * chunk.val))) :=
    outputWord hFrame.1 (hPc.symm ▸ rescaleLoadWord stage chunk)
  obtain ⟨tm,hOut,hFire⟩ := hEvent
  have hFault : t.fault = none := by
    cases hF : t.fault
    · rfl
    · have hTm : tm = .ub _ := Out.ev.inj (by simpa only [out,hF] using hOut.symm)
      rw [hTm] at hFire
      cases congrArg Event.kind hFire.1
  have hSub : t.sub = 0 := by
    by_contra hn
    obtain ⟨ds,_,hCode⟩ := rescaleLoadCode stage chunk
    rw [out_event hFault (hPc.symm ▸ hCode) rfl rfl] at hOut
    obtain rfl := Out.ev.inj hOut
    have hHook : Assumptions.all.any (·.tcLdWait t.pc) = true :=
      hPc.symm ▸ rescaleWaitHook stage chunk
    simp only [eventTmpl,tcLdTmpl,hHook,hn,ite_true,ite_false] at hFire
    cases congrArg Event.kind hFire.1
  exact ⟨t,ending,⟨hPc,hSub,hFrame.2.1.clearAccumulator,hFault,trivial⟩,hAddr,hRun,hFrame.2.2⟩

/-- A real rescale read loads the sixteen words of its correction chunk. -/
theorem rescaleLoadActualAddress {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) (chunk : Fin 8) {i : EvId}
    {address : Nat} {values : List Value} {shape : TcShape}
    (he : X.get i = some ⟨rescaleLoadPc stage chunk,.tc (.ld address values shape)⟩) :
    address = outputAddress l i.1 stage (16 * chunk.val) ∧ shape = .s32x32b ∧
      values.length = 16 := by
  obtain ⟨g,j⟩ := i
  obtain ⟨_,hLen,hc⟩ := rescaleLoadCode stage chunk
  have h := observedLoadAtColumn hp hX he
    ((by decide : ∀ s c, 8006 ≤ rescaleLoadPc s c ∧ rescaleLoadPc s c < 9057) stage chunk)
    (rescaleLoadWord stage chunk) hc (by have := chunk.isLt; omega)
  exact ⟨h.1,h.2.1,h.2.2.trans hLen⟩

/-- A real finalization read loads the eight words of its correction chunk. -/
theorem finalizeLoadActualAddress {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) (chunk : Fin 16) {i : EvId}
    {address : Nat} {values : List Value} {shape : TcShape}
    (he : X.get i = some ⟨finalizeLoadPc stage chunk,.tc (.ld address values shape)⟩) :
    address = outputAddress l i.1 stage (8 * chunk.val) ∧ shape = .s32x32b ∧ values.length = 8 := by
  obtain ⟨g,j⟩ := i
  obtain ⟨_,hLen,hc⟩ := finalizeLoadCode stage chunk
  have h := observedLoadAtColumn hp hX he
    ((by decide : ∀ s c, 8006 ≤ finalizeLoadPc s c ∧ finalizeLoadPc s c < 9057) stage chunk)
    (finalizeLoadWord stage chunk) hc (by have := chunk.isLt; omega)
  exact ⟨h.1,h.2.1,h.2.2.trans hLen⟩

private def storeShape (i : Instr) : Option (Nat × Nat) :=
  match i with
  | ⟨none,.tcSt reg vals .s32x32b⟩ => some (reg,vals.length)
  | _ => none

private theorem rescaleStoreShape :
    ∀ (stage : Fin 2) (chunk : Fin 8),
      (kernel.code[rescaleStorePc stage chunk]?.bind storeShape) =
        some (rescaleAddressReg stage chunk,16) := by decide +kernel

private theorem rescaleStoreInstruction (stage : Fin 2) (chunk : Fin 8) :
    ∃ operands, operands.length = 16 ∧ kernel.code[rescaleStorePc stage chunk]? =
      some ⟨none,.tcSt (rescaleAddressReg stage chunk) operands .s32x32b⟩ := by
  obtain ⟨⟨guard,op⟩,hc,hs⟩ := Option.bind_eq_some_iff.mp (rescaleStoreShape stage chunk)
  cases guard <;> cases op <;> simp only [storeShape,reduceCtorEq] at hs
  rename_i dst vals shape
  cases shape <;> simp only [Option.some.injEq,Prod.mk.injEq,reduceCtorEq] at hs
  obtain ⟨hReg,hLen⟩ := hs
  rw [hReg] at hc
  exact ⟨vals,hLen,hc⟩

/-- A real rescale write covers the sixteen words of its correction chunk. -/
theorem rescaleStoreActualAddress {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) (chunk : Fin 8) {i : EvId}
    {address : Nat} {values : List Value} {shape : TcShape}
    (he : X.get i = some ⟨rescaleStorePc stage chunk,.tc (.st address values shape)⟩) :
    address = outputAddress l i.1 stage (16 * chunk.val) ∧ shape = .s32x32b ∧
      values.length = 16 := by
  obtain ⟨g,j⟩ := i
  let col := 16 * chunk.val
  let a := outputAddress l g stage col
  have hBand := (by decide :
    ∀ s c, 8006 ≤ rescaleStorePc s c ∧ rescaleStorePc s c < 9057) stage chunk
  obtain ⟨s, _, hs, hAddr, hStep⟩ :=
    observedCorrectionColumn hp hX he hBand (rescaleStoreWord stage chunk)
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨_, rfl⟩ | ⟨_, hCode, rfl⟩
  · cases congrArg Event.kind hFire.1
  obtain ⟨ops,hOps,hc⟩ := rescaleStoreInstruction stage chunk
  rw [hs,hc] at hCode
  obtain rfl := Option.some.inj hCode.symm
  have hWidth : a < 2 ^ 32 := by
    apply tmem_warp_encoding_lt
    have hCeil := outputColumn_range stage
    have hChunk := chunk.isLt
    dsimp only [col]
    omega
  have hLen := fires_tcSt_len (by intro sh h; cases h) hFire rfl
  obtain ⟨u,hKeep,hCore⟩ := fires_tcSt_core hFire rfl (by intro h; cases h)
  have hReg := (congrFun hKeep (rescaleAddressReg stage chunk)).trans hAddr
  rw [tcTmpl_tcSt_plain (by intro sh h; cases h)] at hCore
  have hA := readBits_b32 (L := l) (g := g) hReg hWidth
  have hBits : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_lt (by omega)
  have hCount : TcShape.s32x32b.countOk ops.length = true := hOps.symm ▸ (by decide : _)
  have hGood : tcDataAddressOk l g .s32x32b a = true := by
    apply tcDataAddressOk_warp32
    have hCeil := outputColumn_range stage
    have hChunk := chunk.isLt
    dsimp only [col]
    omega
  simp only [hp.block,show 512 % 32 = 0 by decide,hCount,hA,↓reduceIte,
    bind,Except.bind] at hCore
  change (BitVec.ofNat 64 (outputAddress l g stage (16 * chunk.val))).toNat = a at hBits
  rw [hBits, hGood] at hCore
  simp only [↓reduceIte] at hCore
  cases hVals : ops.mapM (readValue l g u 32) with
  | error f =>
    simp only [hVals,ofExec] at hCore
    cases congrArg Event.kind hCore.1
  | ok vals =>
    simp only [hVals] at hCore
    split at hCore
    · have hEq := TcKind.st.inj (Kind.tc.inj (congrArg Event.kind hCore.1))
      exact ⟨hEq.1,hEq.2.2,hLen.trans hOps⟩
    · cases congrArg Event.kind hCore.1

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
