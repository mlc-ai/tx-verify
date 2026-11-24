-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MbarAddressClosure
public import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Lemmas.Flow.TcTmpl
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Flow.Code.Part051
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Kernels.TmlFa4Fwd.Flow.Code.Part054
import Kernels.TmlFa4Fwd.Flow.Code.Part055
import Kernels.TmlFa4Fwd.Flow.Code.Part056
import Kernels.TmlFa4Fwd.Flow.Code.Part060
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part076
import Kernels.TmlFa4Fwd.Flow.Code.Part078
import Kernels.TmlFa4Fwd.Flow.Code.Part079
import Kernels.TmlFa4Fwd.Flow.Code.Part080
import Kernels.TmlFa4Fwd.Flow.Code.Part082
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Kernels.TmlFa4Fwd.Flow.Code.Part120

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open Prologue Mma Epilogue

noncomputable section

private def stageOffset (stage : Bool) : Nat := if stage then 8 else 0

private def physicalStage (warp : Fin 8) : Bool := decide (3 < warp.val)

private inductive AddressValue
  | predicate
  | stage
  | bytes
  | biasBarrier
  | unit
  | shared (displacement : Nat)
  deriving DecidableEq

private def AddressValue.word (l : Launch) (stage : Bool) : AddressValue → Value
  | .predicate => .pred stage
  | .stage => .bits 16 (BitVec.ofNat 64 stage.toNat)
  | .bytes => b32 (stageOffset stage)
  | .biasBarrier => b32 (11 + stage.toNat)
  | .unit => b32 1
  | .shared off => b32 (l.sharedBase + (stageOffset stage + off))

private inductive AddressOp
  | stageTest
  | select (pred : Nat)
  | selectBiasBarrier (pred : Nat)
  | unit
  | scale (src : Nat)
  | base (src : Nat)
  | displace (src offset : Nat)
  deriving DecidableEq

private def AddressOp.value : AddressOp → AddressValue
  | .stageTest => .predicate
  | .select _ => .stage
  | .selectBiasBarrier _ => .biasBarrier
  | .unit => .unit
  | .scale _ => .bytes
  | .base _ => .shared 0
  | .displace _ off => .shared off

private def AddressOp.operand : AddressOp → Option (Nat × AddressValue)
  | .stageTest | .unit => none
  | .select pred | .selectBiasBarrier pred => some (pred, .predicate)
  | .scale src => some (src, .stage)
  | .base src => some (src, .bytes)
  | .displace src _ => some (src, .shared 0)

private def AddressOp.instruction (dst : Nat) : AddressOp → Op
  | .stageTest => .int ⟨.setp .gt none, .int .s 32, false, [some dst], [.reg 1062, .imm 3]⟩
  | .select pred => .int ⟨.selp, .int .b 16, false, [some dst], [.imm 1, .imm 0, .reg pred]⟩
  | .selectBiasBarrier pred =>
    .int ⟨.selp, .int .b 32, false, [some dst], [.imm 12, .imm 11, .reg pred]⟩
  | .unit => .move ⟨.scalar, .int .b 32, [some dst], [.imm 1]⟩
  | .scale src => .int ⟨.mul .wide, .int .u 16, false, [some dst], [.reg src, .imm 8]⟩
  | .base src => .int ⟨.add, .int .s 32, false, [some dst], [.reg 2535, .reg src]⟩
  | .displace src off => .int ⟨.add, .int .s 32, false, [some dst], [.reg src, .imm off]⟩

private structure AddressFact where
  definition : Nat
  lastPc : Nat
  reg : Nat
  operation : AddressOp
  deriving DecidableEq

/-- The two probability publications in each of the first, biased and plain rounds. -/
structure ProbabilityArrivalSite where
  pc : Nat
  base : Nat
  offset : Nat
  count : Nat
  state : Nat

def probabilityArrivalSite (i : Fin 6) : ProbabilityArrivalSite :=
  (#v[⟨4847, 3217, 96, 3927, 8186⟩, ⟨4867, 3946, 112, 3947, 8187⟩,
    ⟨6532, 5097, 96, 5098, 8603⟩, ⟨6552, 5117, 112, 5118, 8604⟩,
    ⟨7437, 5187, 96, 5781, 8850⟩,
    ⟨7457, 5800, 112, 5801, 8851⟩] : Vector ProbabilityArrivalSite 6)[i]

private def probabilityUnitFact (i : Fin 6) : AddressFact :=
  let s := probabilityArrivalSite i
  ⟨s.pc - 1, s.pc, s.count, .unit⟩

private def addressFacts : List AddressFact :=
  [⟨3286, 3582, 481, .stageTest⟩, ⟨3288, 3289, 1045, .select 481⟩, ⟨3289, 3290, 2773, .scale 1045⟩,
   ⟨3290, 3418, 2774, .base 2773⟩, ⟨3291, 3427, 2769, .displace 2774 80⟩,
   ⟨3292, 3500, 2771, .displace 2774 320⟩, ⟨3418, 3422, 2767, .displace 2774 192⟩,
   ⟨3585, 3586, 492, .stageTest⟩, ⟨3586, 3587, 1046, .select 492⟩, ⟨3587, 3588, 3076, .scale 1046⟩,
   ⟨3588, 3590, 3077, .base 3076⟩, ⟨3850, 3851, 493, .stageTest⟩, ⟨3851, 3852, 1047, .select 493⟩,
   ⟨3852, 3853, 3216, .scale 1047⟩, ⟨3853, 4847, 3217, .base 3216⟩,
   ⟨4862, 4863, 625, .stageTest⟩, ⟨4863, 4864, 1048, .select 625⟩, ⟨4864, 4865, 3945, .scale 1048⟩,
   ⟨4865, 4867, 3946, .base 3945⟩, ⟨4868, 4869, 626, .stageTest⟩, ⟨4869, 4870, 1049, .select 626⟩,
   ⟨4870, 4871, 3950, .scale 1049⟩, ⟨4871, 4872, 3951, .base 3950⟩,
   ⟨4872, 4876, 3948, .displace 3951 192⟩, ⟨5032, 5270, 631, .stageTest⟩,
   ⟨5105, 5106, 1050, .select 631⟩,
   ⟨5106, 5107, 4036, .scale 1050⟩, ⟨5107, 5180, 4037, .base 4036⟩,
   ⟨5108, 5111, 3964, .displace 4037 80⟩, ⟨5180, 5183, 3965, .displace 4037 320⟩,
   ⟨5273, 5274, 633, .stageTest⟩, ⟨5274, 5275, 1051, .select 633⟩, ⟨5275, 5276, 4236, .scale 1051⟩,
   ⟨5276, 5278, 4237, .base 4236⟩, ⟨5675, 6528, 637, .stageTest⟩, ⟨6528, 6529, 1052, .select 637⟩,
   ⟨6529, 6530, 5096, .scale 1052⟩, ⟨6530, 6532, 5097, .base 5096⟩,
   ⟨6547, 6548, 640, .stageTest⟩, ⟨6548, 6549, 1053, .select 640⟩, ⟨6549, 6550, 5116, .scale 1053⟩,
   ⟨6550, 6552, 5117, .base 5116⟩, ⟨6553, 6554, 641, .stageTest⟩, ⟨6554, 6555, 1054, .select 641⟩,
   ⟨6555, 6556, 5120, .scale 1054⟩, ⟨6556, 6557, 5121, .base 5120⟩,
   ⟨6557, 6560, 5119, .displace 5121 192⟩, ⟨6661, 6672, 644, .stageTest⟩,
   ⟨6672, 6673, 1055, .select 644⟩,
   ⟨6673, 6674, 5186, .scale 1055⟩, ⟨6674, 7437, 5187, .base 5186⟩,
   ⟨6675, 6678, 5126, .displace 5187 80⟩, ⟨7452, 7453, 649, .stageTest⟩,
   ⟨7453, 7454, 1056, .select 649⟩,
   ⟨7454, 7455, 5799, .scale 1056⟩, ⟨7455, 7457, 5800, .base 5799⟩,
   ⟨7458, 7459, 650, .stageTest⟩, ⟨7459, 7460, 1057, .select 650⟩, ⟨7460, 7461, 5803, .scale 1057⟩,
   ⟨7461, 7462, 5804, .base 5803⟩, ⟨7462, 7465, 5802, .displace 5804 192⟩,
   ⟨7733, 7734, 680, .stageTest⟩, ⟨7734, 7735, 1058, .select 680⟩, ⟨7735, 7736, 5865, .scale 1058⟩,
   ⟨7736, 7737, 5866, .base 5865⟩, ⟨7737, 7740, 5864, .displace 5866 192⟩,
   ⟨3582, 3583, 3075, .selectBiasBarrier 481⟩, ⟨5270, 5271, 4235, .selectBiasBarrier 631⟩,
   ⟨3589, 3590, 3078, .unit⟩, ⟨5277, 5278, 4238, .unit⟩] ++
    (List.finRange 6).map probabilityUnitFact

private def AddressFact.active (f : AddressFact) (pc : Nat) : Prop :=
  f.definition < pc ∧ pc ≤ f.lastPc

private instance (f : AddressFact) (pc : Nat) : Decidable (f.active pc) :=
  inferInstanceAs (Decidable (f.definition < pc ∧ pc ≤ f.lastPc))

private def addressRegisters (l : Launch) (warp : Fin 8) (s : TState) : Prop :=
  ∀ f ∈ addressFacts, f.active s.pc →
    s.regs f.reg = some (f.operation.value.word l (physicalStage warp))

private def addressFrame (l : Launch) (warp : Fin 8) (s : TState) : Prop :=
  s.sub ≤ 3 ∧ s.regs 1062 = some (b32 warp.val) ∧
    s.regs 2535 = some (b32 l.sharedBase) ∧ addressRegisters l warp s

private theorem sourceAddress {l : Launch} {warp : Fin 8} {s : TState} {pc : Nat}
    (hFrame : addressRegisters l warp s) (hPc : s.pc = pc) (f : AddressFact)
    (hf : f ∈ addressFacts) (ha : f.active pc) :
    ∃ stage : Bool, s.regs f.reg = some (f.operation.value.word l stage) :=
  ⟨physicalStage warp, hFrame f hf (hPc.symm ▸ ha)⟩

private def AddressFact.decoded (f : AddressFact) : Bool :=
  !Assumptions.swExp2Sites.contains f.definition &&
  !Assumptions.tcLdDataflowSites.contains f.definition &&
  !Assumptions.delayedTmemSites.contains f.definition &&
  (match f.operation with | .displace _ off => off ≤ 320 | _ => true) &&
  match f.operation.operand with
  | none => true
  | some (reg, value) =>
    addressFacts.any (fun p =>
      decide (p.reg = reg ∧ p.operation.value = value ∧ p.active f.definition))

private def addressInstructionKey : Instr → Option (Sum IntInstr MoveInstr)
  | ⟨none, .int op⟩ => some (.inl op)
  | ⟨none, .move op⟩ => some (.inr op)
  | _ => none

private def addressInstructionOfKey : Sum IntInstr MoveInstr → Instr
  | .inl op => ⟨none, .int op⟩
  | .inr op => ⟨none, .move op⟩

private theorem addressInstructionKey_exact {i : Instr} {key : Sum IntInstr MoveInstr}
    (hk : addressInstructionKey i = some key) : i = addressInstructionOfKey key := by
  obtain ⟨guard, op⟩ := i
  cases guard
  · cases op <;> simp only [addressInstructionKey, Option.some.injEq, reduceCtorEq] at hk
    all_goals subst key; rfl
  · cases hk

private theorem addressDefinitionCode {f : AddressFact} (hf : f ∈ addressFacts) :
    kernel.code[f.definition]? = some ⟨none, f.operation.instruction f.reg⟩ := by
  let expected (j : AddressFact) : Instr := ⟨none, j.operation.instruction j.reg⟩
  have hAudit : addressFacts.all (fun j => decide
      ((kernel.code[j.definition]?.bind addressInstructionKey) =
        addressInstructionKey (expected j))) = true := by
    decide +kernel
  have hKey := of_decide_eq_true (List.all_eq_true.mp hAudit f hf)
  obtain ⟨key, hk⟩ : ∃ key, addressInstructionKey (expected f) = some key := by
    cases hOp : f.operation <;> simp [expected, hOp, addressInstructionKey, AddressOp.instruction]
  rw [hk] at hKey
  obtain ⟨ins, hCode, hIns⟩ := Option.bind_eq_some_iff.mp hKey
  rw [addressInstructionKey_exact hIns, ← addressInstructionKey_exact hk] at hCode
  exact hCode

private theorem addressDefinitions : addressFacts.all AddressFact.decoded = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem localDefResult {l : Launch} {g pc : Nat} {s u : TState} {op : Op}
    (hPc : s.pc = pc) (hf : s.fault = none)
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (ht : Tau kernel [] l g s u) : execLocal l g s op = .ok u := by
  unfold Tau at ht
  have hx : execLocalA [] l g s op = execLocal l g s op := rfl
  simp only [out, hPc, hf, hc, guardHolds, pure, Except.pure, hl, ↓reduceIte, hx] at ht
  split at ht
  · rename_i v h
    obtain rfl := Out.tau.inj ht
    exact h
  · contradiction

private theorem computeStagePred {l : Launch} {g d : Nat} {warp : Fin 8} {s u : TState}
    (hw : s.regs 1062 = some (b32 warp.val))
    (h : execLocal l g s (AddressOp.stageTest.instruction d) = .ok u) :
    u.regs d = some (AddressValue.predicate.word l (physicalStage warp)) := by
  have hRead := readBits_b32 (L := l) (g := g) hw (by have := warp.isLt; omega)
  unfold AddressOp.instruction at h
  rw [execLocal_int rfl] at h
  simp only [execInt, DType.width, hRead, bind, Except.bind, pure, Except.pure] at h
  obtain rfl := Except.ok.inj h.symm
  simp only [next, setReg, Function.update_self]
  fin_cases warp <;> rfl

private theorem selectStage {l : Launch} {g d pred : Nat} {s u : TState} {stage : Bool}
    (hPred : s.regs pred = some (.pred stage))
    (h : execLocal l g s ((AddressOp.select pred).instruction d) = .ok u) :
    u.regs d = some (AddressValue.stage.word l stage) := by
  unfold AddressOp.instruction at h
  rw [execLocal_selp rfl] at h
  cases stage <;>
    simp [execMove, readReg, hPred, readValue, readBits, DType.width, Value.bytes, bind,
      Except.bind, pure, Except.pure] at h
  all_goals subst u; exact Function.update_self _ _ _

private theorem selectBiasBarrier {l : Launch} {g d pred : Nat} {s u : TState} {stage : Bool}
    (hPred : s.regs pred = some (.pred stage))
    (h : execLocal l g s ((AddressOp.selectBiasBarrier pred).instruction d) = .ok u) :
    u.regs d = some (AddressValue.biasBarrier.word l stage) := by
  unfold AddressOp.instruction at h
  rw [execLocal_selp rfl] at h
  cases stage <;>
    simp [execMove, readReg, hPred, readValue, readBits, DType.width, Value.bytes, bind,
      Except.bind, pure, Except.pure] at h
  all_goals subst u; exact Function.update_self _ _ _

private theorem unitWord {l : Launch} {g d : Nat} {s u : TState}
    (h : execLocal l g s (AddressOp.unit.instruction d) = .ok u) :
    u.regs d = some (b32 1) := by
  unfold AddressOp.instruction at h
  rw [execLocal_move rfl] at h
  simp [execMove, readValue, readBits, DType.width, Value.bytes,
    bind, Except.bind, pure, Except.pure] at h
  subst u
  exact Function.update_self _ _ _

private theorem scaleStage {l : Launch} {g d r : Nat} {s u : TState} {stage : Bool}
    (hReg : s.regs r = some (AddressValue.stage.word l stage))
    (h : execLocal l g s ((AddressOp.scale r).instruction d) = .ok u) :
    u.regs d = some (AddressValue.bytes.word l stage) := by
  unfold AddressOp.instruction at h
  rw [execLocal_int rfl] at h
  cases stage <;> simp only [execInt, DType.width, readBits, readReg, hReg,
    bind, Except.bind, pure, Except.pure] at h
  all_goals obtain rfl := Except.ok.inj h.symm
  all_goals exact Function.update_self _ _ _

private theorem addStageBase {l : Launch} {g d r : Nat} {s u : TState} {stage : Bool}
    (hBase : s.regs 2535 = some (b32 l.sharedBase))
    (hWord : s.regs r = some (AddressValue.bytes.word l stage))
    (hBound : l.sharedBase + stageOffset stage < 2 ^ 32)
    (h : execLocal l g s ((AddressOp.base r).instruction d) = .ok u) :
    u.regs d = some ((AddressValue.shared 0).word l stage) := by
  have hA : l.sharedBase < 2 ^ 32 := by omega
  have hB : stageOffset stage < 2 ^ 32 := by cases stage <;> decide
  change s.regs r = some (b32 (stageOffset stage)) at hWord
  unfold AddressOp.instruction at h
  rw [execLocal_int rfl] at h
  simp only [execInt, DType.width, readValue, readReg, hBase, hWord,
    readBits_b32 hBase hA, readBits_b32 hWord hB, b32, bind, Except.bind, pure, Except.pure] at h
  rw [← BitVec.ofNat_add, truncBits_ofNat hBound (by decide)] at h
  obtain rfl := Except.ok.inj h.symm
  exact Function.update_self _ _ _

private theorem addStageDisplacement {l : Launch} {g d r off : Nat} {s u : TState} {stage : Bool}
    (hWord : s.regs r = some ((AddressValue.shared 0).word l stage))
    (hBound : l.sharedBase + (stageOffset stage + off) < 2 ^ 32)
    (h : execLocal l g s ((AddressOp.displace r off).instruction d) = .ok u) :
    u.regs d = some ((AddressValue.shared off).word l stage) := by
  have hA : l.sharedBase + stageOffset stage < 2 ^ 32 := by omega
  have hB : off < 2 ^ 32 := by omega
  change s.regs r = some (b32 (l.sharedBase + (stageOffset stage + 0))) at hWord
  rw [Nat.add_zero] at hWord
  have hImm : readBits l g s 32 (.imm off) = .ok (BitVec.ofNat 64 off) := by
    simp only [readBits, BitVec.ofInt_natCast, truncBits_ofNat hB (by decide), pure, Except.pure]
  unfold AddressOp.instruction at h
  rw [execLocal_int rfl] at h
  simp only [execInt, DType.width, readValue, readReg, hWord, readBits_b32 hWord hA,
    hImm, b32, bind, Except.bind, pure, Except.pure] at h
  rw [← BitVec.ofNat_add, Nat.add_assoc, truncBits_ofNat hBound (by decide)] at h
  obtain rfl := Except.ok.inj h.symm
  exact Function.update_self _ _ _

section
variable {p : Params} {l : Launch} {m : Mem0}

private theorem definesSoftmaxAddress (hp : Pre p l m) {g : Nat} {s u : TState} {f : AddressFact}
    (hF : f ∈ addressFacts) (hPc : s.pc = f.definition) (hf : s.fault = none) {warp : Fin 8}
    (hWarp : s.regs 1062 = some (b32 warp.val)) (hBase : s.regs 2535 = some (b32 l.sharedBase))
    (hRegs : addressRegisters l warp s) (ht : Tau kernel Assumptions.all l g s u) :
    u.regs f.reg = some (f.operation.value.word l (physicalStage warp)) := by
  have hd := List.all_eq_true.mp addressDefinitions f hF
  simp only [AddressFact.decoded, Bool.and_eq_true, List.contains_eq_mem,
    Bool.not_eq_true', decide_eq_false_iff_not] at hd
  have hc := addressDefinitionCode hF
  have hCore : Assumptions.coreOp (f.operation.instruction f.reg) = true := by
    cases f.operation <;> rfl
  have hn : Tau kernel [] l g s u := by
    unfold Tau at ht ⊢
    rw [← Assumptions.out_all_eq_nil (hPc.symm ▸ hd.1.1.1.1)
      (hPc.symm ▸ hd.1.1.1.2) (hPc.symm ▸ hd.1.1.2) (hPc.symm ▸ hc) hCore]
    exact ht
  have hLocal : (f.operation.instruction f.reg).isLocal = true := by cases f.operation <;> rfl
  have hU := localDefResult hPc hf hc hLocal hn
  have hOperand {reg value} (hArg : f.operation.operand = some (reg, value)) :
      s.regs reg = some (value.word l (physicalStage warp)) := by
    have hFound := hd.2
    rw [hArg] at hFound
    obtain ⟨other, hMem, h⟩ := List.any_eq_true.mp hFound
    obtain ⟨hR, hV, ha⟩ := of_decide_eq_true h
    have hReg := hRegs other hMem (hPc.symm ▸ ha)
    simpa only [hR, hV] using hReg
  have hBound (stage : Bool) (off : Nat) (hOff : off ≤ 320) :
      l.sharedBase + (stageOffset stage + off) < 2 ^ 32 := by
    have := hp.shared.2.1
    cases stage <;> simp only [stageOffset, Bool.false_eq_true, ↓reduceIte] <;> omega
  let stage := physicalStage warp
  cases hOp : f.operation with
  | stageTest => exact computeStagePred hWarp (hOp ▸ hU)
  | unit => exact unitWord (hOp ▸ hU)
  | select pred =>
    exact selectStage (hOperand (reg := pred) (by rw [hOp]; rfl)) (hOp ▸ hU)
  | selectBiasBarrier pred =>
    exact selectBiasBarrier (hOperand (reg := pred) (by rw [hOp]; rfl)) (hOp ▸ hU)
  | scale r => exact scaleStage (hOperand (reg := r) (by rw [hOp]; rfl)) (hOp ▸ hU)
  | base r =>
    exact addStageBase hBase (hOperand (reg := r) (by rw [hOp]; rfl))
      (by simpa using hBound stage 0 (by decide)) (hOp ▸ hU)
  | displace r off =>
    have hOff : off ≤ 320 := by simpa [hOp] using hd.1.2
    exact addStageDisplacement (hOperand (reg := r) (by rw [hOp]; rfl))
      (hBound stage off hOff) (hOp ▸ hU)

private def addressWrites (op : Op) : List Nat := writesRegs op ++ scoreEventWrites op

private def addressStepCode (pc : Nat) (op : Op) : Bool :=
  (op.isLocal || scoreEventOp op) &&
  [2535, 1062].all (fun reg => !(addressWrites op).contains reg) &&
  addressFacts.all (fun f => !decide (f.active pc) || !(addressWrites op).contains f.reg) &&
  match op with
  | .bra target _ => 3103 ≤ target && target ≤ 7742 &&
      addressFacts.all (fun f => !decide (f.active target) || decide (f.active pc))
  | .brx .. => false
  | _ => true

private theorem addressStepCodeAt {pc : Nat} {i : Instr}
    (hLo : 3103 ≤ pc) (hHi : pc < 7742) (hc : kernel.code[pc]? = some i) :
    addressStepCode pc i.op = true := by
  let code := ((kernel.code.drop 3103).take (7742 - 3103)).zipIdx 3103
  have hAll : code.all (fun (i, pc) => addressStepCode pc i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, pc)
  apply List.mem_of_getElem? (i := pc - 3103)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem softmaxSegmentAddresses {l : Launch} {warp : Fin 8} {s u : TState}
    {seg : SegMatch CuteSlot} (hSite : s.pc ∈ Assumptions.swExp2Sites)
    (hMatch : cuteExp2.matchAt kernel s.pc = some seg)
    (hRun : Assumptions.execSwExp2 seg s = .ok u)
    (hFrame : addressFrame l warp s) : 3103 ≤ u.pc ∧ u.pc ≤ 7742 ∧ addressFrame l warp u := by
  have hAll : Assumptions.swExp2Sites.all (fun pc => match cuteExp2.matchAt kernel pc with
      | none => false
      | some seg => (3103 ≤ seg.stop && seg.stop ≤ 7742) &&
          [2535, 1062].all (fun r => !(scoreSegmentWrites seg).contains r) &&
          addressFacts.all (fun f => !decide (f.active seg.stop) ||
            (decide (f.active pc) && !(scoreSegmentWrites seg).contains f.reg))) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hCode := List.all_eq_true.mp hAll _ hSite
  rw [hMatch] at hCode
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hCode
  obtain ⟨hPc, hSub, _, hKeep⟩ := scoreSegmentFrame hRun
  have hRoot (r : Nat) (hr : r ∈ [2535, 1062]) : u.regs r = s.regs r :=
    hKeep r (by simpa using List.all_eq_true.mp hCode.1.2 r hr)
  refine ⟨hPc.symm ▸ hCode.1.1.1, hPc.symm ▸ hCode.1.1.2, hSub.symm ▸ Nat.zero_le _,
    (hRoot 1062 (by decide)).trans hFrame.2.1, (hRoot 2535 (by decide)).trans hFrame.2.2.1, ?_⟩
  intro f hf ha
  rw [hPc] at ha
  have h := List.all_eq_true.mp hCode.2 f hf
  have hFact : f.active s.pc ∧ f.reg ∉ scoreSegmentWrites seg := by simpa [ha] using h
  exact (hKeep f.reg hFact.2).trans (hFrame.2.2.2 f hf hFact.1)

private theorem softmaxAddressStep (hp : Pre p l m) {g : Nat} {warp : Fin 8} {s u : TState}
    {e : Option Event} (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742) (hFrame : addressFrame l warp s)
    (hw : WStep kernel Assumptions.all l g s e u) :
    3103 ≤ u.pc ∧ u.pc ≤ 7742 ∧ addressFrame l warp u := by
  have hFall (hNext : u.pc = s.pc + 1) {f : AddressFact} (ha : f.active u.pc) :
      s.pc = f.definition ∨ f.active s.pc := by
    unfold AddressFact.active at ha ⊢
    omega
  have finish {i : Instr} (hc : kernel.code[s.pc]? = some i)
      (hPc : 3103 ≤ u.pc ∧ u.pc ≤ 7742) (hSub : u.sub ≤ 3)
      (hKeep : ∀ r, r ∉ addressWrites i.op → u.regs r = s.regs r)
      (hEntry : ∀ f ∈ addressFacts, f.active u.pc → s.pc = f.definition ∨ f.active s.pc)
      (hNew : ∀ f ∈ addressFacts, s.pc = f.definition →
        u.regs f.reg = some (f.operation.value.word l (physicalStage warp))) :
      3103 ≤ u.pc ∧ u.pc ≤ 7742 ∧ addressFrame l warp u := by
    have hCode := addressStepCodeAt hLo hHi hc
    simp only [addressStepCode, Bool.and_eq_true] at hCode
    have hRoot (r : Nat) (hr : r ∈ [2535, 1062]) : u.regs r = s.regs r :=
      hKeep r (by simpa using List.all_eq_true.mp hCode.1.1.2 r hr)
    refine ⟨hPc.1, hPc.2, hSub, (hRoot 1062 (by decide)).trans hFrame.2.1,
      (hRoot 2535 (by decide)).trans hFrame.2.2.1, ?_⟩
    intro f hf ha
    rcases hEntry f hf ha with h | h
    · exact hNew f hf h
    · have hReg : f.reg ∉ addressWrites i.op := by
        simpa [h] using List.all_eq_true.mp hCode.1.2 f hf
      exact (hKeep f.reg hReg).trans (hFrame.2.2.2 f hf h)
  rcases hw with ⟨_, ht⟩ | ⟨_, _, he⟩
  · obtain ⟨i, hc, hf, hStep⟩ := tauScoreSource ht
    have hNew := fun f hm h => definesSoftmaxAddress hp (f := f) hm h hf
      hFrame.2.1 hFrame.2.2.1 hFrame.2.2.2 ht
    rcases hStep with ⟨rfl, _⟩ | ⟨_, _, he⟩
    · exact finish hc (by change 3103 ≤ s.pc + 1 ∧ s.pc + 1 ≤ 7742; omega)
        (Nat.zero_le _) (fun _ _ => rfl) (fun _ _ ha => hFall rfl ha) hNew
    rcases scoreExecLocal he with hLocal | ⟨seg, hs, hm, hr⟩
    · have hPc := hLocal.pc
      have hCode := addressStepCodeAt hLo hHi hc
      simp only [addressStepCode, Bool.and_eq_true] at hCode
      refine finish hc ?_ (hLocal.sub.symm ▸ hFrame.1)
        (fun r hr => hLocal.regs r (fun h => hr (List.mem_append_left _ h))) ?_ hNew
      · cases hOp : i.op <;> simp only [hOp, nextPc, BrxTarget, or_false] at hPc
        case bra target uni =>
          simp only [hOp, Bool.and_eq_true, decide_eq_true_eq] at hCode
          omega
        case brx => simp [hOp] at hCode
        all_goals omega
      · intro f hf ha
        cases hOp : i.op <;> simp only [hOp, nextPc, BrxTarget, or_false] at hPc
        case bra target uni =>
          have hBra := hCode.2
          simp only [hOp, Bool.and_eq_true, decide_eq_true_eq] at hBra
          have h := List.all_eq_true.mp hBra.2 f hf
          rw [hPc] at ha
          exact .inr (by simpa [ha] using h)
        case brx => simp [hOp] at hCode
        all_goals exact hFall hPc ha
    · exact softmaxSegmentAddresses hs hm hr hFrame
  · obtain ⟨i, hc, hl, _⟩ := estep_event_source he
    have hCode := addressStepCodeAt hLo hHi hc
    simp only [addressStepCode, Bool.and_eq_true, hl, Bool.false_or] at hCode
    have hBase : 2535 ∉ addressWrites i.op := by
      simpa using List.all_eq_true.mp hCode.1.1.2 2535 (by decide)
    have hProg := (scoreEventStep (r := 2535) hc hCode.1.1.1 hFrame.1
      (fun h => hBase (List.mem_append_right _ h)) he).1
    have hPc : u.pc = s.pc + 1 ∨ u.pc = s.pc :=
      hProg.pc.elim (fun h => .inl h.1) (fun h => .inr h.1)
    have keep r (hr : r ∉ addressWrites i.op) : u.regs r = s.regs r :=
      (scoreEventStep hc hCode.1.1.1 hFrame.1 (fun h => hr (List.mem_append_right _ h)) he).2
    refine finish hc (by omega) hProg.sub keep ?_ ?_
    · intro f hf ha
      rcases hPc with h | h
      · exact hFall h ha
      · exact .inr (h ▸ ha)
    · intro f hf h
      rw [h, addressDefinitionCode hf] at hc
      obtain rfl := Option.some.inj hc.symm
      have hLocal : (f.operation.instruction f.reg).isLocal = true := by
        cases f.operation <;> rfl
      change (f.operation.instruction f.reg).isLocal = false at hl
      rw [hLocal] at hl
      cases hl

private theorem softmaxReturnTail {l : Launch} {g : Nat} {warp : Fin 8} {s : TState}
    {events : List Event} {visits : List Visit} (hPc : s.pc = 7742)
    (hWarp : s.regs 1062 = some (b32 warp.val))
    (hWalk : Walk kernel Assumptions.all l g s events visits)
    {e : Event} (he : e ∈ events) (hEnd : e.pc < 7742) : False := by
  by_cases hf : s.fault = none
  · obtain ⟨u, hu, hReturn, hOut⟩ := softExitRun (g := g) warp hPc hf hWarp
    rcases advanceWalkLocals hu hWalk with h | ⟨tail, _, _, hW⟩
    · subst events
      cases he
    · cases hW with
      | stop => cases he
      | tau ht _ => exact (not_tau_of_stops ⟨_, hOut⟩ ht).elim
      | ev hs _ =>
        obtain ⟨tm, ho, hFire⟩ := hs
        obtain rfl := Out.ev.inj (ho.symm.trans hOut)
        cases hFire.2
      | last hs =>
        obtain rfl := List.mem_singleton.mp he
        have h := estep_source_pc hs
        omega
  · obtain ⟨f, hFault⟩ := Option.isSome_iff_exists.mp
      (show s.fault.isSome from by cases h : s.fault <;> simp_all)
    have hOut : out kernel Assumptions.all l g s = .ev (.ub f) := by simp [out, hFault]
    cases hWalk with
    | stop => cases he
    | tau ht _ => exact (not_tau_of_stops ⟨_, hOut⟩ ht).elim
    | ev hs _ =>
      obtain ⟨tm, ho, hFire⟩ := hs
      obtain rfl := Out.ev.inj (ho.symm.trans hOut)
      cases hFire.2
    | last hs =>
      obtain rfl := List.mem_singleton.mp he
      have h := estep_source_pc hs
      omega

theorem softmaxScratchStep {l : Launch} {g : Nat} {s u : TState}
    {event : Option Event} (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742) (hSub : s.sub ≤ 3)
    (hScratch : ScoreScratchState s) (hStep : WStep kernel Assumptions.all l g s event u) :
    ScoreScratchState u := by
  rcases hStep with ⟨rfl, ht⟩ | ⟨_, rfl, he⟩
  · exact scoreScratchTau ht hScratch
  · obtain ⟨ins, hc, hLocal, _⟩ := estep_event_source he
    have hCode := addressStepCodeAt hLo hHi hc
    simp only [addressStepCode, Bool.and_eq_true, hLocal, Bool.false_or] at hCode
    have hBase : 2535 ∉ scoreEventWrites ins.op := by
      have hKeep : 2535 ∉ addressWrites ins.op := by
        simpa using List.all_eq_true.mp hCode.1.1.2 2535 (by decide)
      exact fun hm => hKeep (List.mem_append_right _ hm)
    have hReady : ScoreScratchReady ins.op s := by
      simpa only [ScoreScratchState, hc, hLocal, Bool.false_eq_true, ite_false] using hScratch
    have hNext := scoreEventScratch hc hCode.1.1.1 hSub hBase he hReady
    by_cases hSame : u.pc = s.pc
    · simpa only [hSame, ScoreScratchState, hc, hLocal, Bool.false_eq_true, ite_false, ite_true]
        using hNext
    · exact scratchStateOfClear (by simpa only [hSame, ite_false] using hNext)

/-- A returning event in the softmax body remains at its instruction or advances one. -/
theorem softmaxReturningPc {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742) (hSub : s.sub ≤ 3)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc+1 ∨ u.pc = s.pc := by
  obtain ⟨ins,hc,hNonlocal,_⟩ := estep_event_source he
  have hCode := addressStepCodeAt hLo hHi hc
  simp only [addressStepCode,Bool.and_eq_true,hNonlocal,Bool.false_or] at hCode
  have hBase : 2535 ∉ scoreEventWrites ins.op := by
    have hKeep : 2535 ∉ addressWrites ins.op := by
      simpa using List.all_eq_true.mp hCode.1.1.2 2535 (by decide)
    exact fun hm => hKeep (List.mem_append_right _ hm)
  exact (scoreEventStep hc hCode.1.1.1 hSub hBase he).1.pc.imp And.left And.left

/-- Advance past a returning softmax event on the same actual suffix. -/
theorem afterSoftmaxEvent {l : Launch} {g : Nat} {s u : TState}
    {e : Event} {es : List Event} {ending : Option TState}
    (hStep : EStep kernel Assumptions.all l g s e (some u))
    (hRun : Run kernel Assumptions.all l g s (e::es) ending) :
    Run kernel Assumptions.all l g u es ending := by
  cases hRun with
  | step hLocal he hRest =>
    have hSame := stop_unique hLocal .refl (stops_of_estep he) (stops_of_estep hStep)
    subst s
    exact Option.some.inj (estep_det he hStep) ▸ hRest
  | last hLocal he =>
    have hSame := stop_unique hLocal .refl (stops_of_estep he) (stops_of_estep hStep)
    subst s
    cases estep_det he hStep

private theorem softmaxAddressWalk (hp : Pre p l m) {g : Nat} {warp : Fin 8} {s : TState}
    {events : List Event} {visits : List Visit} {ending : Option TState}
    (hWalk : Walk kernel Assumptions.all l g s events visits)
    (hRun : Run kernel Assumptions.all l g s events ending) (hLo : 3103 ≤ s.pc) (hHi : s.pc ≤ 7742)
    (hFrame : addressFrame l warp s) (hScratch : ScoreScratchState s) {Q : TState → Prop} (hQ : Q s)
    (hStep : ∀ {s u event}, 3103 ≤ s.pc → s.pc < 7742 → s.sub ≤ 3 →
      s.regs 1062 = some (b32 warp.val) → s.regs 2535 = some (b32 l.sharedBase) →
      ScoreScratchState s → Q s →
      WStep kernel Assumptions.all l g s event u → Q u) {index : Nat} {e : Event}
    (he : events[index]? = some e) (hEnd : e.pc < 7742) :
    ∃ t o, t.pc = e.pc ∧ addressFrame l warp t ∧ ScoreScratchState t ∧ Q t ∧
      EStep kernel Assumptions.all l g t e o ∧
      Run kernel Assumptions.all l g t (events.drop index) ending ∧
      TraceReach kernel Assumptions.all l g s (events.take index) t := by
  induction hWalk generalizing index with
  | stop => simp at he
  | @tau s u events visits ht hw ih =>
    by_cases hExit : s.pc = 7742
    · exact (softmaxReturnTail hExit hFrame.2.1 (.tau ht hw) (List.mem_of_getElem? he) hEnd).elim
    let hw' : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl,ht⟩
    obtain ⟨hl,hh,hU⟩ := softmaxAddressStep hp hLo (by omega) hFrame hw'
    have hu := hRun.after_local_nonempty (.single ht) (by intro hn; simp [hn] at he)
    obtain ⟨a,o,ha,hF,hS,hq,hEvent,hRun',hReach⟩ :=
      ih hu hl hh hU (softmaxScratchStep hLo (by omega) hFrame.1 hScratch hw')
        (hStep hLo (by omega) hFrame.1 hFrame.2.1 hFrame.2.2.1 hScratch hQ hw') he
    exact ⟨a,o,ha,hF,hS,hq,hEvent,hRun',.tau ht hReach⟩
  | @ev s u ev events visits hs hw ih =>
    cases index with
    | zero =>
      obtain rfl := Option.some.inj he
      exact ⟨_,_,(estep_source_pc hs).symm,hFrame,hScratch,hQ,hs,hRun,.refl _⟩
    | succ index =>
      by_cases hExit : s.pc = 7742
      · exact (softmaxReturnTail hExit hFrame.2.1 (.ev hs hw) (List.mem_of_getElem? he) hEnd).elim
      let hw' : WStep kernel Assumptions.all l g s (some ev) u := .inr ⟨ev,rfl,hs⟩
      obtain ⟨hl,hh,hU⟩ := softmaxAddressStep hp hLo (by omega) hFrame hw'
      obtain ⟨a,o,ha,hF,hS,hq,hEvent,hRun',hReach⟩ :=
        ih (afterSoftmaxEvent hs hRun) hl hh hU
          (softmaxScratchStep hLo (by omega) hFrame.1 hScratch hw')
          (hStep hLo (by omega) hFrame.1 hFrame.2.1 hFrame.2.2.1 hScratch hQ hw') he
      exact ⟨a,o,ha,hF,hS,hq,hEvent,hRun',.event hs hReach⟩
  | last hs =>
    cases index with
    | zero =>
      obtain rfl := Option.some.inj he
      exact ⟨_,_,(estep_source_pc hs).symm,hFrame,hScratch,hQ,hs,hRun,.refl _⟩
    | succ index => simp at he

/-- A late observation after the register hint has the actual softmax role-entry suffix. -/
theorem softmaxRoleEntrySuffix {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {e : Event}
    (he : X.get (g,index) = some e) (hLate : 173 < e.pc) (hNotHint : e.pc ≠ 3102)
    (hWarp : warpIndex l g < 8) :
    ∃ w : Fin 8, w.val = warpIndex l g ∧ ∃ pos s o, pos ≤ index ∧
      At s 3103 [(1062, b32 w.val), (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop pos) o := by
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨pos, t, o, hIndex, ht, hr⟩ := commonDispatchOfLateEvent hp hX hg he hLate
  have hLen : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hSuffix : (X.tr g).drop pos ≠ [] := by
    intro h
    exact Nat.not_le_of_lt hLen ((List.drop_eq_nil_iff.mp h).trans hIndex)
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  have hPc : registerHintPc warp = 3102 := by
    simp only [registerHintPc, dispatchParamPc, warp]
    split_ifs <;> omega
  obtain ⟨s, _, hReq, hs, hRun⟩ := firstRegisterHintFromCommon hp hg warp ht hr hSuffix
  have hAt : At s 3103 [(1062, b32 warp.val), (2535, b32 l.sharedBase)] := by
    simpa only [hPc] using hs
  have hLt : pos < index := by
    by_contra! h
    have hEq : pos = index := by omega
    rw [hEq] at hReq
    have hSame := congrArg Event.pc (Option.some.inj (hReq.symm.trans he))
    change registerHintPc warp = e.pc at hSame
    exact hNotHint (hSame.symm.trans hPc)
  exact ⟨⟨warpIndex l g, hWarp⟩, rfl, pos+1, s, _, hLt, hAt, hRun⟩

/-- The reached softmax event has its actual role-entry suffix. -/
theorem softmaxBodySuffix {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {e : Event}
    (he : X.get (g,index) = some e) (hLo : 3420 ≤ e.pc) (hHi : e.pc < 7742) :
    ∃ w : Fin 8, w.val = warpIndex l g ∧ ∃ pos s o, pos ≤ index ∧
      At s 3103 [(1062, b32 w.val), (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop pos) o := by
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hWarp : warpIndex l g < 8 := by
    rcases roleBodyPcOfEvent hp hX he (by omega) hHint with h | h
    · omega
    · split_ifs at h <;> omega
  exact softmaxRoleEntrySuffix hp hX he (by omega) (by omega) hWarp

private theorem addressFrameAtRoleEntry {l : Launch} {w : Fin 8} {s : TState}
    (hAt : At s 3103 [(1062, b32 w.val), (2535, b32 l.sharedBase)]) : addressFrame l w s := by
  refine ⟨hAt.2.1.symm ▸ Nat.zero_le _, hAt.2.2.2.2.1, hAt.2.2.2.2.2.1, ?_⟩
  intro f hf ha
  have hDec : addressFacts.all (fun f => !decide (f.active 3103)) = true := by decide
  have hFalse : ¬ f.active 3103 := by simpa using List.all_eq_true.mp hDec f hf
  exact (hFalse (hAt.1 ▸ ha)).elim

/-- A recorded event can be replayed from one chosen role-entry suffix, retaining
the reached path so that later replays can use the same state and trace positions. -/
theorem softmaxRoleEventFromEntryWithScratch {X : Execution} (hp : Pre p l m) {g pos index : Nat}
    (w : Fin 8) {s : TState} {ending : Option TState}
    (hEntry : At s 3103 [(1062,b32 w.val),(2535,b32 l.sharedBase)])
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending) {e : Event}
    (he : X.get (g,index) = some e) (hIndex : pos ≤ index) (hHi : e.pc < 7742) {Q : TState → Prop}
    (hInit : Q s)
    (hStep : ∀ {t u event}, 3103 ≤ t.pc → t.pc < 7742 → t.sub ≤ 3 →
      t.regs 1062 = some (b32 w.val) → t.regs 2535 = some (b32 l.sharedBase) →
      ScoreScratchState t → Q t →
      WStep kernel Assumptions.all l g t event u → Q u) :
    ∃ t o, t.pc = e.pc ∧ t.sub ≤ 3 ∧ t.regs 1062 = some (b32 w.val) ∧
      t.regs 2535 = some (b32 l.sharedBase) ∧ ScoreScratchState t ∧ Q t ∧
      EStep kernel Assumptions.all l g t e o ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop index) ending ∧
      TraceReach kernel Assumptions.all l g s (((X.tr g).drop pos).take (index-pos)) t := by
  obtain ⟨visits,hWalk⟩ := walkFromRun hRun
  have hAtIndex : ((X.tr g).drop pos)[index-pos]? = some e := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le hIndex]
  obtain ⟨t,o,ht,hf,hScratch,hQ,hEvent,hSuffix,hReach⟩ := softmaxAddressWalk hp hWalk hRun
    (by rw [hEntry.1]) (by rw [hEntry.1]; decide) (addressFrameAtRoleEntry hEntry)
    (scratchStateOfClear ⟨hEntry.2.1,hEntry.2.2.1⟩) hInit hStep hAtIndex hHi
  rw [List.drop_drop,Nat.add_sub_of_le hIndex] at hSuffix
  exact ⟨t,o,ht,hf.1,hf.2.1,hf.2.2.1,hScratch,hQ,hEvent,hSuffix,hReach⟩

/-- The first biased score issue already holds the stage's Bias barrier base. -/
theorem repeatedBiasBaseOfScoreStart {X : Execution} (hp : Pre p l m) (w : Fin 8) {g pos j : Nat}
    {s : TState} {ending : Option TState}
    (hs : At s 3103 [(1062,b32 w.val),(2535,b32 l.sharedBase)])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending) {address : Nat}
    {values : List Value} {shape : TcShape}
    (he : X.get (g,j) = some ⟨5112,.tc (.ld address values shape)⟩) (hPos : pos ≤ j) :
    ∃ t o, TraceReach kernel Assumptions.all l g s (((X.tr g).drop pos).take (j-pos)) t ∧
      EStep kernel Assumptions.all l g t ⟨5112,.tc (.ld address values shape)⟩ o ∧
      t.regs 4037 = some (b32 (l.sharedBase+8*(w.val/4))) := by
  obtain ⟨_,hWalk⟩ := walkFromRun hr
  have hAtIndex : ((X.tr g).drop pos)[j-pos]? = some ⟨5112,.tc (.ld address values shape)⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
    exact he
  obtain ⟨t,o,ht,hf,_,_,hEvent,_,hReach⟩ := softmaxAddressWalk hp hWalk hr
    (by rw [hs.1]) (by rw [hs.1]; decide) (addressFrameAtRoleEntry hs)
    (scratchStateOfClear ⟨hs.2.1,hs.2.2.1⟩) (Q := fun _ => True)
    trivial (by simp) hAtIndex (show 5112 < 7742 by decide)
  change t.pc = 5112 at ht
  have hOffset : stageOffset (physicalStage w) = 8*(w.val/4) := by fin_cases w <;> rfl
  have hBase := hf.2.2.2 ⟨5107,5180,4037,.base 4036⟩ (by decide)
    (by rw [ht]; decide)
  change t.regs 4037 = some (b32 (l.sharedBase+stageOffset (physicalStage w))) at hBase
  exact ⟨t,o,hReach,hEvent,by simpa only [hOffset] using hBase⟩
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem softmaxSourceWithSuffix {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 3420 ≤ e.pc) (hHi : e.pc < 7742) {Q : Fin 8 → TState → Prop}
    (hInit : ∀ w t, At t 3103 [(1062, b32 w.val), (2535, b32 l.sharedBase)] → Q w t)
    (hStep : ∀ (w : Fin 8) {s u event}, 3103 ≤ s.pc → s.pc < 7742 → s.sub ≤ 3 →
      s.regs 1062 = some (b32 w.val) → s.regs 2535 = some (b32 l.sharedBase) →
      ScoreScratchState s → Q w s →
      WStep kernel Assumptions.all l g s event u → Q w u) :
    ∃ w : Fin 8, w.val = warpIndex l g ∧ ∃ t o ending,
      t.pc = e.pc ∧ addressFrame l w t ∧ ScoreScratchState t ∧ Q w t ∧
      EStep kernel Assumptions.all l g t e o ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop index) ending := by
  obtain ⟨w,hw,pos,s,ending,hIndex,hAt,hRun⟩ := softmaxBodySuffix hp hX he hLo hHi
  have hF := addressFrameAtRoleEntry hAt
  obtain ⟨_, hWalk⟩ := walkFromRun hRun
  have hAtIndex : ((X.tr g).drop pos)[index-pos]? = some e := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le hIndex]
  obtain ⟨t,o,ht,hf,hScratch,hQ,hEvent,hSuffix,_⟩ := softmaxAddressWalk hp hWalk hRun
    (by rw [hAt.1]) (by rw [hAt.1]; decide) hF
    (scratchStateOfClear ⟨hAt.2.1,hAt.2.2.1⟩) (hInit w s hAt) (hStep w) hAtIndex hHi
  rw [List.drop_drop,Nat.add_sub_of_le hIndex] at hSuffix
  exact ⟨w,hw,t,o,ending,ht,hf,hScratch,hQ,hEvent,hSuffix⟩

private theorem softmaxSourceWith {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 3420 ≤ e.pc) (hHi : e.pc < 7742) {Q : Fin 8 → TState → Prop}
    (hInit : ∀ w t, At t 3103 [(1062, b32 w.val), (2535, b32 l.sharedBase)] → Q w t)
    (hStep : ∀ (w : Fin 8) {s u event}, 3103 ≤ s.pc → s.pc < 7742 → s.sub ≤ 3 →
      s.regs 1062 = some (b32 w.val) → s.regs 2535 = some (b32 l.sharedBase) →
      ScoreScratchState s → Q w s →
      WStep kernel Assumptions.all l g s event u → Q w u) :
    ∃ w : Fin 8, w.val = warpIndex l g ∧ ∃ t o, t.pc = e.pc ∧ addressFrame l w t ∧ Q w t ∧
      EStep kernel Assumptions.all l g t e o := by
  obtain ⟨w,hw,t,o,_,ht,hF,_,hQ,hE,_⟩ :=
    softmaxSourceWithSuffix hp hX he hLo hHi hInit hStep
  exact ⟨w,hw,t,o,ht,hF,hQ,hE⟩

/-- A register invariant transported through the decoded softmax role, from its actual
dispatch to any recorded role event. -/
theorem softmaxRoleEventWith {g j : Nat} {e : Event} (he : X.get (g,j) = some e) (hLo : 3420 ≤ e.pc)
    (hHi : e.pc < 7742) {Q : Fin 8 → TState → Prop}
    (hInit : ∀ w t, At t 3103 [(1062, b32 w.val), (2535, b32 l.sharedBase)] → Q w t)
    (hStep : ∀ (w : Fin 8) {s u event}, 3103 ≤ s.pc → s.pc < 7742 → s.sub ≤ 3 →
      s.regs 1062 = some (b32 w.val) → Q w s →
      WStep kernel Assumptions.all l g s event u → Q w u) :
    ∃ w : Fin 8, w.val = warpIndex l g ∧ ∃ t o, t.pc = e.pc ∧ Q w t ∧
      EStep kernel Assumptions.all l g t e o := by
  obtain ⟨w, hw, t, o, ht, _, hQ, hf⟩ :=
    softmaxSourceWith hp hX he hLo hHi hInit
      (fun w {_ _ _} hL hH hSub hWarp _ _ hQ hw => hStep w hL hH hSub hWarp hQ hw)
  exact ⟨w, hw, t, o, ht, hQ, hf⟩

/-- A softmax role invariant can use the shared base and split-instruction scratch state. -/
theorem softmaxRoleEventWithScratch {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hLo : 3420 ≤ e.pc) (hHi : e.pc < 7742) {Q : Fin 8 → TState → Prop}
    (hInit : ∀ w t, At t 3103 [(1062, b32 w.val), (2535, b32 l.sharedBase)] → Q w t)
    (hStep : ∀ (w : Fin 8) {s u event}, 3103 ≤ s.pc → s.pc < 7742 → s.sub ≤ 3 →
      s.regs 1062 = some (b32 w.val) → s.regs 2535 = some (b32 l.sharedBase) →
      ScoreScratchState s → Q w s →
      WStep kernel Assumptions.all l g s event u → Q w u) :
    ∃ w : Fin 8, w.val = warpIndex l g ∧ ∃ t o, t.pc = e.pc ∧ t.sub ≤ 3 ∧ Q w t ∧
      EStep kernel Assumptions.all l g t e o := by
  obtain ⟨w, hw, t, o, ht, hFrame, hQ, hf⟩ := softmaxSourceWith hp hX he hLo hHi hInit hStep
  exact ⟨w, hw, t, o, ht, hFrame.1, hQ, hf⟩

omit hp hX in
private theorem softmaxReplayInWalk {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g : Nat}
    (Inv : Nat → TState → Prop)
    (hStep : ∀ {s u : TState} {ev : Option Event} {pos : Nat},
      3103 ≤ s.pc → s.pc < 7742 → s.sub ≤ 3 → Inv pos s →
      WStep kernel Assumptions.all l g s ev u →
      (∀ e, ev = some e → X.get (g,pos) = some e) → Inv (pos+ev.toList.length) u)
    {s : TState} {w : Fin 8} {visits : List Visit} {events : List Event}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : 3103 ≤ s.pc) (hHi : s.pc ≤ 7742) (hFrame : addressFrame l w s)
    {base offset : Nat} (hSuffix : (X.tr g).drop base = events)
    (hInv : Inv base s) {target : Event} (he : events[offset]? = some target)
    (hEnd : target.pc < 7742) :
    ∃ t u, Inv (base+offset) t ∧ EStep kernel Assumptions.all l g t target u := by
  induction hw generalizing base offset with
  | stop => simp at he
  | @tau s u events visits ht hw ih =>
    by_cases hExit : s.pc = 7742
    · exact (softmaxReturnTail hExit hFrame.2.1 (.tau ht hw) (List.mem_of_getElem? he) hEnd).elim
    have hW : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl,ht⟩
    obtain ⟨hMin,hMax,hNext⟩ := softmaxAddressStep hp hLo (by omega) hFrame hW
    have hProp := hStep hLo (by omega) hFrame.1 hInv hW (fun _ h => by cases h)
    exact ih hMin hMax hNext hSuffix hProp he
  | @ev s u first events visits hf hw ih =>
    by_cases hExit : s.pc = 7742
    · exact (softmaxReturnTail hExit hFrame.2.1 (.ev hf hw) (List.mem_of_getElem? he) hEnd).elim
    cases offset with
    | zero =>
      obtain rfl := Option.some.inj he
      exact ⟨s,some u,by simpa only [Nat.add_zero] using hInv,hf⟩
    | succ offset =>
      have hCurrent : X.get (g,base) = some first := by
        change (X.tr g)[base]? = _
        rw [← Nat.add_zero base,← List.getElem?_drop,hSuffix,List.getElem?_cons_zero]
      have hTail : (X.tr g).drop (base+1) = events := by
        rw [← List.drop_drop,hSuffix]
        rfl
      have hW : WStep kernel Assumptions.all l g s (some first) u := .inr ⟨first,rfl,hf⟩
      obtain ⟨hMin,hMax,hNext⟩ := softmaxAddressStep hp hLo (by omega) hFrame hW
      have hProp := hStep hLo (by omega) hFrame.1 hInv hW
        (fun _ h => Option.some.inj h ▸ hCurrent)
      rw [show base+(offset+1) = base+1+offset by omega]
      exact ih hMin hMax hNext hTail hProp he
  | @last s first hf =>
    cases offset with
    | zero =>
      obtain rfl := Option.some.inj he
      exact ⟨s,none,by simpa only [Nat.add_zero] using hInv,hf⟩
    | succ offset => simp at he

omit hp hX in
/-- Replay a chosen role suffix while retaining its caller's indexed invariant. -/
theorem softmaxRoleReplayFromEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos index : Nat} (w : Fin 8) {s : TState} {ending : Option TState}
    (hAt : At s 3103 [(1062,b32 w.val),(2535,b32 l.sharedBase)])
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    {target : Event} (he : X.get (g,index) = some target) (hIndex : pos ≤ index)
    (hHi : target.pc < 7742) (Inv : Nat → TState → Prop) (hInv : Inv pos s)
    (hStep : ∀ {t u : TState} {ev : Option Event} {j : Nat},
      3103 ≤ t.pc → t.pc < 7742 → t.sub ≤ 3 → Inv j t →
      WStep kernel Assumptions.all l g t ev u →
      (∀ e, ev = some e → X.get (g,j) = some e) → Inv (j+ev.toList.length) u) :
    ∃ t u, Inv index t ∧ EStep kernel Assumptions.all l g t target u := by
  obtain ⟨_,hWalk⟩ := walkFromRun hRun
  have hAtSuffix : ((X.tr g).drop pos)[index-pos]? = some target := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le hIndex]
  obtain ⟨t,u,hInv,hEvent⟩ := softmaxReplayInWalk hp Inv hStep hWalk
    (by rw [hAt.1]) (by rw [hAt.1]; decide) (addressFrameAtRoleEntry hAt) rfl hInv hAtSuffix hHi
  rw [Nat.add_sub_of_le hIndex] at hInv
  exact ⟨t,u,hInv,hEvent⟩

/-- Replay an exact softmax occurrence and retain a frame indexed by the consumed events. -/
theorem softmaxRoleReplayAt {g index : Nat} {target : Event} (he : X.get (g,index) = some target)
    (hLo : 3420 ≤ target.pc) (hHi : target.pc < 7742) (Inv : Nat → TState → Prop)
    (hInit : ∀ (w : Fin 8) (pos : Nat) (s : TState),
      At s 3103 [(1062,b32 w.val),(2535,b32 l.sharedBase)] → Inv pos s)
    (hStep : ∀ {s u : TState} {ev : Option Event} {pos : Nat},
      3103 ≤ s.pc → s.pc < 7742 → s.sub ≤ 3 → Inv pos s →
      WStep kernel Assumptions.all l g s ev u →
      (∀ e, ev = some e → X.get (g,pos) = some e) → Inv (pos+ev.toList.length) u) :
    ∃ t u, Inv index t ∧ EStep kernel Assumptions.all l g t target u := by
  obtain ⟨w,_,pos,s,_,hIndex,hAt,hRun⟩ := softmaxBodySuffix hp hX he hLo hHi
  exact softmaxRoleReplayFromEntry hp w hAt hRun he hIndex hHi Inv (hInit w pos s hAt) hStep

private theorem softmaxAddressSource {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 3420 ≤ e.pc) (hHi : e.pc < 7742) :
    ∃ warp : Fin 8, ∃ t o, t.pc = e.pc ∧ addressFrame l warp t ∧
      EStep kernel Assumptions.all l g t e o := by
  obtain ⟨w, _, t, o, ht, hF, _, hf⟩ :=
    softmaxSourceWith hp hX he hLo hHi (Q := fun _ _ => True) (by simp) (by simp)
  exact ⟨w, t, o, ht, hF, hf⟩

/-- Each Bias rendezvous uses the named barrier of the issuing softmax stage. -/
theorem actualBiasBarrierStage (repeated : Bool) {g index id : Nat} {count : Option Nat}
    {mode : BarMode}
    (he : X.get (g,index) = some ⟨if repeated then 5271 else 3583, .bar id count mode⟩) :
    warpIndex l g < 8 ∧ id = 11 + warpIndex l g / 4 := by
  let site := if repeated then 5271 else 3583
  let fact : AddressFact := if repeated then ⟨5270, 5271, 4235, .selectBiasBarrier 631⟩
    else ⟨3582, 3583, 3075, .selectBiasBarrier 481⟩
  have hIn : fact ∈ addressFacts := by cases repeated <;> decide
  have hActive : fact.active site := by cases repeated <;> decide
  obtain ⟨w, hw, t, o, ht, hFrame, _, hStep⟩ := softmaxSourceWith hp hX he
    (by change 3420 ≤ site; cases repeated <;> decide)
    (by change site < 7742; cases repeated <;> decide)
    (Q := fun _ _ => True) (by simp) (by simp)
  change t.pc = site at ht
  have hWord : t.regs fact.reg = some (b32 (11 + (physicalStage w).toNat)) := by
    have h := hFrame.2.2.2 fact hIn (ht ▸ hActive)
    cases repeated <;> exact h
  let barrier := 11 + (physicalStage w).toNat
  have hLt : barrier < 16 := by
    dsimp only [barrier]
    cases physicalStage w <;> simp [Bool.toNat]
  have hRead := readBits_b32 (L := l) (g := g) hWord (by omega : barrier < 2^32)
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f,rfl⟩ | ⟨ins,hc,rfl⟩
  · exact Kind.noConfusion (congrArg Event.kind hFire.1)
  · have hCode : kernel.code[site]? = some ⟨none, .barSyncN (.reg fact.reg) (.imm 128) true⟩ := by
      cases repeated
      · exact Flow.code_3583
      · exact Flow.code_5271
    rw [ht, hCode] at hc
    obtain rfl := Option.some.inj hc
    change Fires t.pc (barTmpl l g t (.reg fact.reg) (some (.imm 128)) .sync) _ o at hFire
    have hShape := fires_barTmpl_at hRead rfl hLt (by decide : 128 < 2^31)
      (by decide) (by decide) (by rw [hp.block]; decide) hFire
    have hId := (Kind.bar.inj (congrArg Event.kind hShape)).1
    have hStage : (physicalStage w).toNat = w.val / 4 := by fin_cases w <;> rfl
    exact ⟨hw ▸ w.isLt, hId.trans (by rw [hStage, hw])⟩

/-- Each softmax statistics acquire addresses the correction credit for its own warp group. -/
theorem softmaxStatsCreditWaitAddress {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g,index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [3420, 4874, 6558, 7463, 7738]) :
    target = ⟨.shared, g / l.block, l.sharedBase + (192 + 8 * (warpIndex l g / 4))⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hLo : 3420 ≤ pc := by omega
  have hHi : pc < 7742 := by omega
  obtain ⟨w, hw, t, o, ht, hFrame, _, hStep⟩ :=
    softmaxSourceWith hp hX he hLo hHi (Q := fun _ _ => True) (by simp) (by simp)
  change t.pc = pc at ht
  have hOffset : stageOffset (physicalStage w) = 8 * (w.val / 4) := by
    fin_cases w <;> decide
  rw [← hw, ← hOffset,
    Nat.add_comm 192 (stageOffset (physicalStage w))]
  have hAllowed : initializedMbarOffset (stageOffset (physicalStage w) + 192 + 0) := by
    unfold initializedMbarOffset
    cases physicalStage w <;> decide
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl | rfl | rfl | rfl
  · rw [ht, Flow.code_3420] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2767 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 192))) :=
      hFrame.2.2.2 ⟨3418, 3422, 2767, .displace 2774 192⟩ (by decide) (by rw [ht]; decide)
    exact pollResolvedMbarAddress hp hb hAllowed hFire rfl
  · rw [ht, Flow.code_4874] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 3948 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 192))) :=
      hFrame.2.2.2 ⟨4872, 4876, 3948, .displace 3951 192⟩ (by decide) (by rw [ht]; decide)
    exact pollResolvedMbarAddress hp hb hAllowed hFire rfl
  · rw [ht, Flow.code_6558] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 5119 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 192))) :=
      hFrame.2.2.2 ⟨6557, 6560, 5119, .displace 5121 192⟩ (by decide) (by rw [ht]; decide)
    exact pollResolvedMbarAddress hp hb hAllowed hFire rfl
  · rw [ht, Flow.code_7463] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 5802 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 192))) :=
      hFrame.2.2.2 ⟨7462, 7465, 5802, .displace 5804 192⟩ (by decide) (by rw [ht]; decide)
    exact pollResolvedMbarAddress hp hb hAllowed hFire rfl
  · rw [ht, Flow.code_7738] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 5864 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 192))) :=
      hFrame.2.2.2 ⟨7737, 7740, 5864, .displace 5866 192⟩ (by decide) (by rw [ht]; decide)
    exact pollResolvedMbarAddress hp hb hAllowed hFire rfl

/-- The initial score wait uses its warp group's QK-full object. -/
theorem firstScoreWaitAddress {g index : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨3425, .wait target q ok acq scope⟩) :
    target = ⟨.shared, g / l.block, l.sharedBase + (80 + 8 * (warpIndex l g / 4))⟩ := by
  obtain ⟨w, hw, t, o, ht, hFrame, _, hStep⟩ :=
    softmaxSourceWith hp hX he (show 3420 ≤ 3425 by decide) (show 3425 < 7742 by decide)
      (Q := fun _ _ => True) (by simp) (by simp)
  change t.pc = 3425 at ht
  have hOffset : stageOffset (physicalStage w) = 8 * (w.val / 4) := by
    fin_cases w <;> decide
  rw [← hw, ← hOffset, Nat.add_comm 80 (stageOffset (physicalStage w))]
  have hAllowed : initializedMbarOffset (stageOffset (physicalStage w) + 80 + 0) := by
    unfold initializedMbarOffset
    cases physicalStage w <;> decide
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases (congrArg Event.kind hFire.1)
  rw [ht, Flow.code_3425] at hc
  obtain rfl := Option.some.inj hc.symm
  have hb : t.regs 2769 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 80))) :=
    hFrame.2.2.2 ⟨3291, 3427, 2769, .displace 2774 80⟩ (by decide) (by rw [ht]; decide)
  exact pollResolvedMbarAddress hp hb hAllowed hFire rfl

omit hp hX in
/-- The shared barrier offset within a softmax stage. -/
def softmaxWaitBaseOffset : Nat → Nat
  | 3420 | 4874 | 6558 | 7463 | 7738 => 192
  | 3425 | 5109 | 6676 => 80
  | _ => 320

/-- Each softmax poll uses its instruction's barrier and the issuer's warp stage. -/
theorem softmaxWaitExactAddress {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [3420, 3425, 3498, 4874, 5109, 5181, 6558, 6676, 7463, 7738]) :
    warpIndex l g < 8 ∧ target = ⟨.shared, g / l.block, l.sharedBase +
      (8 * (warpIndex l g / 4) + softmaxWaitBaseOffset pc)⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hLo : 3420 ≤ pc := by omega
  have hHi : pc < 7742 := by omega
  obtain ⟨w, hWarp, t, o, ht, hFrame, _, hStep⟩ :=
    softmaxSourceWith hp hX he hLo hHi (Q := fun _ _ => True) (by simp) (by simp)
  refine ⟨hWarp ▸ w.isLt, ?_⟩
  have hStage : stageOffset (physicalStage w) = 8 * (warpIndex l g / 4) := by
    rw [← hWarp]
    exact (by decide : ∀ w : Fin 8, stageOffset (physicalStage w) = 8 * (w.val / 4)) w
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ht, Flow.code_3420] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2 ⟨3418, 3422, 2767, .displace 2774 192⟩ (by decide)
      (by rw [ht]; decide)
    change t.regs 2767 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 192))) at hb
    have hAddr := pollResolvedMbarAddress hp hb
      (by cases physicalStage w <;> unfold initializedMbarOffset <;> decide) hFire rfl
    simpa only [hStage, softmaxWaitBaseOffset, Nat.add_zero] using hAddr
  · rw [ht, Flow.code_3425] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2 ⟨3291, 3427, 2769, .displace 2774 80⟩ (by decide)
      (by rw [ht]; decide)
    change t.regs 2769 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 80))) at hb
    have hAddr := pollResolvedMbarAddress hp hb
      (by cases physicalStage w <;> unfold initializedMbarOffset <;> decide) hFire rfl
    simpa only [hStage, softmaxWaitBaseOffset, Nat.add_zero] using hAddr
  · rw [ht, Flow.code_3498] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2 ⟨3292, 3500, 2771, .displace 2774 320⟩ (by decide)
      (by rw [ht]; decide)
    change t.regs 2771 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 320))) at hb
    have hAddr := pollResolvedMbarAddress hp hb
      (by cases physicalStage w <;> unfold initializedMbarOffset <;> decide) hFire rfl
    simpa only [hStage, softmaxWaitBaseOffset, Nat.add_zero] using hAddr
  · rw [ht, Flow.code_4874] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2 ⟨4872, 4876, 3948, .displace 3951 192⟩ (by decide)
      (by rw [ht]; decide)
    change t.regs 3948 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 192))) at hb
    have hAddr := pollResolvedMbarAddress hp hb
      (by cases physicalStage w <;> unfold initializedMbarOffset <;> decide) hFire rfl
    simpa only [hStage, softmaxWaitBaseOffset, Nat.add_zero] using hAddr
  · rw [ht, Flow.code_5109] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2 ⟨5108, 5111, 3964, .displace 4037 80⟩ (by decide)
      (by rw [ht]; decide)
    change t.regs 3964 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 80))) at hb
    have hAddr := pollResolvedMbarAddress hp hb
      (by cases physicalStage w <;> unfold initializedMbarOffset <;> decide) hFire rfl
    simpa only [hStage, softmaxWaitBaseOffset, Nat.add_zero] using hAddr
  · rw [ht, Flow.code_5181] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2 ⟨5180, 5183, 3965, .displace 4037 320⟩ (by decide)
      (by rw [ht]; decide)
    change t.regs 3965 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 320))) at hb
    have hAddr := pollResolvedMbarAddress hp hb
      (by cases physicalStage w <;> unfold initializedMbarOffset <;> decide) hFire rfl
    simpa only [hStage, softmaxWaitBaseOffset, Nat.add_zero] using hAddr
  · rw [ht, Flow.code_6558] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2 ⟨6557, 6560, 5119, .displace 5121 192⟩ (by decide)
      (by rw [ht]; decide)
    change t.regs 5119 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 192))) at hb
    have hAddr := pollResolvedMbarAddress hp hb
      (by cases physicalStage w <;> unfold initializedMbarOffset <;> decide) hFire rfl
    simpa only [hStage, softmaxWaitBaseOffset, Nat.add_zero] using hAddr
  · rw [ht, Flow.code_6676] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2 ⟨6675, 6678, 5126, .displace 5187 80⟩ (by decide)
      (by rw [ht]; decide)
    change t.regs 5126 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 80))) at hb
    have hAddr := pollResolvedMbarAddress hp hb
      (by cases physicalStage w <;> unfold initializedMbarOffset <;> decide) hFire rfl
    simpa only [hStage, softmaxWaitBaseOffset, Nat.add_zero] using hAddr
  · rw [ht, Flow.code_7463] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2 ⟨7462, 7465, 5802, .displace 5804 192⟩ (by decide)
      (by rw [ht]; decide)
    change t.regs 5802 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 192))) at hb
    have hAddr := pollResolvedMbarAddress hp hb
      (by cases physicalStage w <;> unfold initializedMbarOffset <;> decide) hFire rfl
    simpa only [hStage, softmaxWaitBaseOffset, Nat.add_zero] using hAddr
  · rw [ht, Flow.code_7738] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2 ⟨7737, 7740, 5864, .displace 5866 192⟩ (by decide)
      (by rw [ht]; decide)
    change t.regs 5864 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 192))) at hb
    have hAddr := pollResolvedMbarAddress hp hb
      (by cases physicalStage w <;> unfold initializedMbarOffset <;> decide) hFire rfl
    simpa only [hStage, softmaxWaitBaseOffset, Nat.add_zero] using hAddr

/-- A softmax credit poll and the role's other polls name disjoint barrier offsets. -/
theorem softmaxWaitAddressClass {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [3420, 3425, 3498, 4874, 5109, 5181, 6558, 6676, 7463, 7738]) :
    ∃ offset ∈ (if pc ∈ [3420, 4874, 6558, 7463, 7738] then [192, 200] else [80, 88, 320, 328]),
      target = ⟨.shared, g / l.block, l.sharedBase + offset⟩ := by
  obtain ⟨hWarp, hAddr⟩ := softmaxWaitExactAddress hp hX he hSite
  refine ⟨_, ?_, hAddr⟩
  have hCheck : ∀ n : Fin 2, [3420, 3425, 3498, 4874, 5109, 5181, 6558, 6676, 7463, 7738].all
      (fun site => (if site ∈ [3420, 4874, 6558, 7463, 7738] then [192, 200] else
        [80, 88, 320, 328]).contains (8 * n.val + softmaxWaitBaseOffset site)) = true := by decide
  have hMember := List.all_eq_true.mp (hCheck ⟨warpIndex l g / 4, by omega⟩) _ hSite
  exact List.contains_iff_mem.mp hMember

/-- Every softmax poll names an initialized barrier in its CTA. -/
theorem softmaxWaitAddress {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g,index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [3420, 3425, 3498, 4874, 5109, 5181, 6558, 6676, 7463, 7738]) :
    ∃ offset ∈ [80, 88, 192, 200, 320, 328],
      target = ⟨.shared, g / l.block, l.sharedBase + offset⟩ := by
  obtain ⟨o, ho, hLoc⟩ := softmaxWaitAddressClass hp hX he hSite
  refine ⟨o, ?_, hLoc⟩
  split_ifs at ho <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢ <;> tauto

/-- Only the Bias release sites can arrive on the two Bias-empty objects. -/
theorem softmaxArriveAddressClass {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc ∈ [3590, 4847, 4867, 5278, 6532, 6552, 7437, 7457]) :
    ∃ offset ∈ (if pc ∈ [3590, 5278] then [336, 344] else [96, 104, 112, 120]),
      target = ⟨.shared, g / l.block, l.sharedBase + offset⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hLo : 3420 ≤ pc := by omega
  have hHi : pc < 7742 := by omega
  obtain ⟨_, t, o, ht, hFrame, hStep⟩ := softmaxAddressSource hp hX he hLo hHi
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ht, Flow.code_3590] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨stage, hb⟩ := sourceAddress hFrame.2.2.2 ht
      ⟨3588, 3590, 3077, .base 3076⟩ (by decide) (by decide)
    change t.regs 3077 = some (b32 (l.sharedBase + (stageOffset stage + 0))) at hb
    refine ⟨_, ?_, arriveResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · cases stage <;> decide
    · cases stage <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_4847] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨stage, hb⟩ := sourceAddress hFrame.2.2.2 ht
      ⟨3853, 4847, 3217, .base 3216⟩ (by decide) (by decide)
    change t.regs 3217 = some (b32 (l.sharedBase + (stageOffset stage + 0))) at hb
    refine ⟨_, ?_, arriveResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · cases stage <;> decide
    · cases stage <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_4867] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨stage, hb⟩ := sourceAddress hFrame.2.2.2 ht
      ⟨4865, 4867, 3946, .base 3945⟩ (by decide) (by decide)
    change t.regs 3946 = some (b32 (l.sharedBase + (stageOffset stage + 0))) at hb
    refine ⟨_, ?_, arriveResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · cases stage <;> decide
    · cases stage <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_5278] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨stage, hb⟩ := sourceAddress hFrame.2.2.2 ht
      ⟨5276, 5278, 4237, .base 4236⟩ (by decide) (by decide)
    change t.regs 4237 = some (b32 (l.sharedBase + (stageOffset stage + 0))) at hb
    refine ⟨_, ?_, arriveResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · cases stage <;> decide
    · cases stage <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_6532] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨stage, hb⟩ := sourceAddress hFrame.2.2.2 ht
      ⟨6530, 6532, 5097, .base 5096⟩ (by decide) (by decide)
    change t.regs 5097 = some (b32 (l.sharedBase + (stageOffset stage + 0))) at hb
    refine ⟨_, ?_, arriveResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · cases stage <;> decide
    · cases stage <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_6552] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨stage, hb⟩ := sourceAddress hFrame.2.2.2 ht
      ⟨6550, 6552, 5117, .base 5116⟩ (by decide) (by decide)
    change t.regs 5117 = some (b32 (l.sharedBase + (stageOffset stage + 0))) at hb
    refine ⟨_, ?_, arriveResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · cases stage <;> decide
    · cases stage <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_7437] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨stage, hb⟩ := sourceAddress hFrame.2.2.2 ht
      ⟨6674, 7437, 5187, .base 5186⟩ (by decide) (by decide)
    change t.regs 5187 = some (b32 (l.sharedBase + (stageOffset stage + 0))) at hb
    refine ⟨_, ?_, arriveResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · cases stage <;> decide
    · cases stage <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_7457] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨stage, hb⟩ := sourceAddress hFrame.2.2.2 ht
      ⟨7455, 7457, 5800, .base 5799⟩ (by decide) (by decide)
    change t.regs 5800 = some (b32 (l.sharedBase + (stageOffset stage + 0))) at hb
    refine ⟨_, ?_, arriveResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · cases stage <;> decide
    · cases stage <;> unfold initializedMbarOffset <;> decide

/-- Every softmax arrive names an initialized barrier in its CTA. -/
theorem softmaxArriveAddress {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc ∈ [3590, 4847, 4867, 5278, 6532, 6552, 7437, 7457]) :
    ∃ offset ∈ [96, 104, 112, 120, 336, 344],
      target = ⟨.shared, g / l.block, l.sharedBase + offset⟩ := by
  obtain ⟨off, ho, hLoc⟩ := softmaxArriveAddressClass hp hX he hSite
  refine ⟨off, ?_, hLoc⟩
  split_ifs at ho <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢ <;> tauto

omit hp hX in
private theorem unitArriveOperandsAt {l : Launch} {g : Nat} {t : TState} {site : Nat}
    {base reg outReg : Nat} {offset : Int} {e : Event} {o : Option TState} {target : Loc}
    {tx n : Nat} {rel : Bool} {scope : MbarScope}
    (hUnit : t.regs reg = some (b32 1))
    (hf : Fires site (eventTmpl Assumptions.all l g t
      (.mbarArrive base offset (.imm 0) (.reg reg) false true .cta (some outReg))) e o)
    (he : e.kind = .arrive target tx n rel scope) :
    tx = 0 ∧ n = 1 ∧ rel = true ∧ scope = .cta := by
  have hWide : (Assumptions.all.any (·.clusterScopeMbar t.pc)) = false := rfl
  have hZero : readBits l g t 32 (.imm 0) = .ok 0#64 := rfl
  have hOne := readBits_b32 (L := l) (g := g) hUnit (by decide)
  simp only [eventTmpl, tmaTmpl, hWide, widenMbarScope, Bool.false_eq_true, ↓reduceIte,
    bind, Except.bind, pure, Except.pure, hZero, hOne] at hf
  cases hm : mbarLoc l g t base offset with
  | error fault =>
    simp [hm, ofExec, Fires] at hf
    rw [hf.1] at he
    cases he
  | ok loc =>
    simp [hm, ofExec, Fires] at hf
    rw [hf.1] at he
    exact ⟨(Kind.arrive.inj he).2.1.symm, (Kind.arrive.inj he).2.2.1.symm,
      (Kind.arrive.inj he).2.2.2.1.symm, (Kind.arrive.inj he).2.2.2.2.symm⟩

/-- Each real release of a Bias buffer contributes a single zero-transaction credit. -/
theorem biasEmptyArriveFacts {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get (g,index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc ∈ [3590, 5278]) :
    tx = 0 ∧ n = 1 ∧ rel = true ∧ scope = .cta ∧ warpIndex l g < 8 ∧
      target = ⟨.shared, g / l.block, l.sharedBase + (336 + 8 * (warpIndex l g / 4))⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hLo : 3420 ≤ pc := by omega
  have hHi : pc < 7742 := by omega
  obtain ⟨w, hw, t, o, ht, hFrame, _, hStep⟩ :=
    softmaxSourceWith hp hX he hLo hHi (Q := fun _ _ => True) (by simp) (by simp)
  change t.pc = pc at ht
  have hOff : stageOffset (physicalStage w) = 8 * (w.val / 4) := by fin_cases w <;> decide
  have hAllowed : initializedMbarOffset (stageOffset (physicalStage w) + 0 + 336) := by
    unfold initializedMbarOffset
    cases physicalStage w <;> decide
  rw [← hw, ← hOff, Nat.add_comm 336 (stageOffset (physicalStage w))]
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl
  · rw [ht, Flow.code_3590] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨_, hUnit⟩ := sourceAddress hFrame.2.2.2 ht
      ⟨3589, 3590, 3078, .unit⟩ (by decide) (by decide)
    obtain ⟨hT, hN, hR, hS⟩ := unitArriveOperandsAt hUnit hFire rfl
    have hBase := hFrame.2.2.2 ⟨3588, 3590, 3077, .base 3076⟩ (by decide)
      (by rw [ht]; decide)
    have hTarget := arriveResolvedMbarAddress hp hBase hAllowed hFire rfl
    exact ⟨hT, hN, hR, hS, w.isLt, by simpa only [Nat.add_zero] using hTarget⟩
  · rw [ht, Flow.code_5278] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨_, hUnit⟩ := sourceAddress hFrame.2.2.2 ht
      ⟨5277, 5278, 4238, .unit⟩ (by decide) (by decide)
    obtain ⟨hT, hN, hR, hS⟩ := unitArriveOperandsAt hUnit hFire rfl
    have hBase := hFrame.2.2.2 ⟨5276, 5278, 4237, .base 4236⟩ (by decide)
      (by rw [ht]; decide)
    have hTarget := arriveResolvedMbarAddress hp hBase hAllowed hFire rfl
    exact ⟨hT, hN, hR, hS, w.isLt, by simpa only [Nat.add_zero] using hTarget⟩

/-- Every softmax poll names an initialized barrier in its CTA. -/
theorem softmaxWaitInitObject {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [3420, 3425, 3498, 4874, 5109, 5181, 6558, 6676, 7463, 7738]) :
    ∃ i : Fin 34, target = initObject l (g / l.block) i := by
  obtain ⟨off, hOff, rfl⟩ := softmaxWaitAddress hp hX he hSite
  apply initObjectOfOffset
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
  rcases hOff with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold initializedMbarOffset <;> decide

end
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Both initial and recurring Bias-ready polls target the actual softmax stage buffer. -/
theorem biasReadyWaitAddress (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g,index) = some ⟨pc, .wait target q ok acq scope⟩) (hSite : pc ∈ [3498, 5181]) :
    target = ⟨.shared, g / l.block, l.sharedBase + (320 + 8 * (warpIndex l g / 4))⟩ := by
  have hSite' : pc = 3498 ∨ pc = 5181 := by simpa using hSite
  obtain ⟨w, hw, t, o, ht, hFrame, _, hStep⟩ :=
    softmaxSourceWith hp hX he (by dsimp; omega) (by dsimp; omega)
      (Q := fun _ _ => True) (by simp) (by simp)
  change t.pc = pc at ht
  have hOffset : stageOffset (physicalStage w) = 8 * (w.val / 4) := by fin_cases w <;> decide
  rw [← hw, ← hOffset, Nat.add_comm 320 (stageOffset (physicalStage w))]
  have hAllowed₁ : initializedMbarOffset (stageOffset (physicalStage w) + 320 + 0) := by
    unfold initializedMbarOffset
    cases physicalStage w <;> decide
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases (congrArg Event.kind hFire.1)
  rcases hSite' with rfl | rfl
  · rw [ht, Flow.code_3498] at hc
    obtain rfl := Option.some.inj hc.symm
    have hBase : t.regs 2771 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 320))) :=
      hFrame.2.2.2 ⟨3292, 3500, 2771, .displace 2774 320⟩ (by decide) (by rw [ht]; decide)
    exact pollResolvedMbarAddress hp hBase hAllowed₁ hFire rfl
  · rw [ht, Flow.code_5181] at hc
    obtain rfl := Option.some.inj hc.symm
    have hBase : t.regs 3965 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 320))) :=
      hFrame.2.2.2 ⟨5180, 5183, 3965, .displace 4037 320⟩ (by decide) (by rw [ht]; decide)
    exact pollResolvedMbarAddress hp hBase hAllowed₁ hFire rfl

private def probabilityBaseFact (i : Fin 6) : AddressFact :=
  (#v[⟨3853, 4847, 3217, .base 3216⟩, ⟨4865, 4867, 3946, .base 3945⟩,
    ⟨6530, 6532, 5097, .base 5096⟩, ⟨6550, 6552, 5117, .base 5116⟩,
    ⟨6674, 7437, 5187, .base 5186⟩, ⟨7455, 7457, 5800, .base 5799⟩]
    : Vector AddressFact 6)[i]

private def probabilityInstruction (s : ProbabilityArrivalSite) : Instr :=
  ⟨none, .mbarArrive s.base s.offset (.imm 0) (.reg s.count) false true .cta (some s.state)⟩

private def probabilityKey : Instr → Option (Nat × Int × Nat × Nat)
  | ⟨none, .mbarArrive base offset (.imm 0) (.reg count) false true .cta (some state)⟩ =>
    some (base, offset, count, state)
  | _ => none

private theorem probabilityCode (i : Fin 6) :
    kernel.code[(probabilityArrivalSite i).pc]? = some (probabilityInstruction
      (probabilityArrivalSite i)) := by
  have hAudit : (List.finRange 6).all (fun j =>
      let site := probabilityArrivalSite j
      decide (kernel.code[site.pc]?.bind probabilityKey =
        some (site.base, (site.offset : Int), site.count, site.state))) = true := by
    decide +kernel
  have hKey := of_decide_eq_true (List.all_eq_true.mp hAudit i (List.mem_finRange _))
  obtain ⟨ins, hc, hk⟩ := Option.bind_eq_some_iff.mp hKey
  unfold probabilityKey at hk
  split at hk
  · rename_i base off count state
    have hFields := Option.some.inj hk
    rcases Prod.mk.inj hFields with ⟨hb, hOther⟩
    rcases Prod.mk.inj hOther with ⟨ho, hOther⟩
    rcases Prod.mk.inj hOther with ⟨hn, hs⟩
    simpa only [probabilityInstruction, hb, ho, hn, hs] using hc
  · cases hk

private theorem probabilityFactsChecked (i : Fin 6) : let b := probabilityBaseFact i
    let u := probabilityUnitFact i
    let row := probabilityArrivalSite i
    b ∈ addressFacts ∧ b.active row.pc ∧ b.reg = row.base ∧ b.operation.value = .shared 0 ∧
      u ∈ addressFacts ∧ u.active row.pc := by
  have h : ∀ i : Fin 6, let b := probabilityBaseFact i
      let u := probabilityUnitFact i
      let row := probabilityArrivalSite i
      b ∈ addressFacts ∧ b.active row.pc ∧ b.reg = row.base ∧ b.operation.value = .shared 0 ∧
        u ∈ addressFacts ∧ u.active row.pc := by decide
  exact h i

private theorem probabilityOffsetAllowed (b : Bool) (i : Fin 6) :
    initializedMbarOffset (stageOffset b + 0 + (probabilityArrivalSite i).offset) := by
  unfold initializedMbarOffset
  have h : ∀ (x : Bool) (j : Fin 6),
      (stageOffset x + 0 + (probabilityArrivalSite j).offset) % 8 = 0 ∧
      ((stageOffset x + 0 + (probabilityArrivalSite j).offset) ≤ 232 ∨
        320 ≤ (stageOffset x + 0 + (probabilityArrivalSite j).offset) ∧
          (stageOffset x + 0 + (probabilityArrivalSite j).offset) ≤ 344) := by decide
  exact h b i

/-- Every real probability publication issues one zero-transaction credit on the object's
physical stage. The two notification rounds use separate objects. -/
theorem probabilityArriveFacts (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (site : Fin 6) {g index : Nat} {target : Loc} {tx count : Nat} {rel : Bool} {scope : MbarScope}
    (he : X.get (g, index) =
      some ⟨(probabilityArrivalSite site).pc, .arrive target tx count rel scope⟩) :
    tx = 0 ∧ count = 1 ∧ rel = true ∧ scope = .cta ∧ warpIndex l g < 8 ∧
      target = ⟨.shared, g / l.block,
        l.sharedBase + ((probabilityArrivalSite site).offset + 8 * (warpIndex l g / 4))⟩ := by
  let s := probabilityArrivalSite site
  have hBounds : 3420 ≤ s.pc ∧ s.pc < 7742 :=
    (by decide : ∀ i : Fin 6, 3420 ≤ (probabilityArrivalSite i).pc ∧
      (probabilityArrivalSite i).pc < 7742) site
  obtain ⟨w, hWarp, t, o, hAt, hFrame, _, hStep⟩ := softmaxSourceWith hp hX he
    hBounds.1 hBounds.2 (Q := fun _ _ => True) (by simp) (by simp)
  change t.pc = s.pc at hAt
  obtain ⟨hb, hba, hReg, hv, hu, hua⟩ := probabilityFactsChecked site
  have hBase := hFrame.2.2.2 (probabilityBaseFact site) hb (hAt.symm ▸ hba)
  rw [hReg, hv] at hBase
  have hUnit : t.regs s.count = some (b32 1) :=
    hFrame.2.2.2 (probabilityUnitFact site) hu (hAt.symm ▸ hua)
  have hOffset : stageOffset (physicalStage w) = 8 * (w.val / 4) := by fin_cases w <;> decide
  have hAllowed := probabilityOffsetAllowed (physicalStage w) site
  obtain ⟨template, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases (congrArg Event.kind hFire.1)
  change kernel.code[t.pc]? = some ins at hc
  rw [hAt, probabilityCode site] at hc
  obtain rfl := Option.some.inj hc.symm
  obtain ⟨hTx, hCount, hRel, hScope⟩ := unitArriveOperandsAt hUnit hFire rfl
  have hAddress := arriveResolvedMbarAddress hp hBase hAllowed hFire rfl
  rw [← hWarp, ← hOffset, Nat.add_comm s.offset (stageOffset (physicalStage w))]
  exact ⟨hTx, hCount, hRel, hScope, w.isLt, by simpa only [Nat.add_zero] using hAddress⟩

/-- Each real score-ready wait targets the issuing softmax stage. -/
theorem scoreReadyWaitStage (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g,index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [3425, 5109, 6676]) :
    warpIndex l g < 8 ∧ target =
      ⟨.shared, g / l.block, l.sharedBase + (80 + 8 * (warpIndex l g / 4))⟩ := by
  have hs : pc = 3425 ∨ pc = 5109 ∨ pc = 6676 := by simpa using hSite
  obtain ⟨w, hWarp, t, o, ht, hFrame, _, hStep⟩ := softmaxSourceWith hp hX he
    (by dsimp; omega) (by dsimp; omega) (Q := fun _ _ => True) (by simp) (by simp)
  have hOff : stageOffset (physicalStage w) = 8 * (w.val / 4) := by fin_cases w <;> decide
  have hw : warpIndex l g < 8 := hWarp ▸ w.isLt
  refine ⟨hw, ?_⟩
  rw [← hWarp, ← hOff, Nat.add_comm 80]
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hs with rfl | rfl | rfl
  · rw [ht, Flow.code_3425] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2
      ⟨3291, 3427, 2769, .displace 2774 80⟩ (by decide) (ht.symm ▸ (by decide : _))
    change t.regs 2769 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 80))) at hb
    exact pollResolvedMbarAddress hp hb (by fin_cases w <;> unfold initializedMbarOffset <;> decide)
      hFire rfl
  · rw [ht, Flow.code_5109] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2
      ⟨5108, 5111, 3964, .displace 4037 80⟩ (by decide) (ht.symm ▸ (by decide : _))
    change t.regs 3964 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 80))) at hb
    exact pollResolvedMbarAddress hp hb (by fin_cases w <;> unfold initializedMbarOffset <;> decide)
      hFire rfl
  · rw [ht, Flow.code_6676] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2.2
      ⟨6675, 6678, 5126, .displace 5187 80⟩ (by decide) (ht.symm ▸ (by decide : _))
    change t.regs 5126 = some (b32 (l.sharedBase + (stageOffset (physicalStage w) + 80))) at hb
    exact pollResolvedMbarAddress hp hb (by fin_cases w <;> unfold initializedMbarOffset <;> decide)
      hFire rfl

/-- The ordinary score-ready waits target the score buffers, disjoint from Bias-ready. -/
theorem scoreReadyWaitOffset (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g,index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [3425, 5109, 6676]) :
    ∃ offset ∈ [80, 88], target = ⟨.shared, g / l.block, l.sharedBase + offset⟩ := by
  obtain ⟨hWarp, hLoc⟩ := scoreReadyWaitStage hp hX he hSite
  refine ⟨80 + 8 * (warpIndex l g / 4), ?_, hLoc⟩
  have hs : warpIndex l g / 4 = 0 ∨ warpIndex l g / 4 = 1 := by omega
  rcases hs with h | h <;> simp [h]

private theorem returningScoreSuffix {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {warp : Fin 8} {s : TState} {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : 3103 ≤ s.pc) (hHi : s.pc ≤ 7742)
    (hFrame : addressFrame l warp s) (hScratch : ScoreScratchState s)
    {index : Nat} {e : Event} (he : events[index]? = some e) (hEnd : e.pc < 7742)
    (hLater : index + 1 < events.length) :
    ∃ t u rest, t.sub ≤ 3 ∧ u.sub ≤ 3 ∧ ScoreScratchState u ∧
      EStep kernel Assumptions.all l g t e (some u) ∧
      Walk kernel Assumptions.all l g u (events.drop (index+1)) rest := by
  induction hw generalizing index with
  | stop => simp at he
  | @tau s u es vs ht hw ih =>
    by_cases hExit : s.pc = 7742
    · exact (softmaxReturnTail hExit hFrame.2.1 (.tau ht hw) (List.mem_of_getElem? he) hEnd).elim
    obtain ⟨hl, hh, hu⟩ := softmaxAddressStep hp hLo (by omega) hFrame (.inl ⟨rfl, ht⟩)
    exact ih hl hh hu (softmaxScratchStep hLo (by omega) hFrame.1 hScratch (.inl ⟨rfl, ht⟩))
      he hLater
  | @ev s u ev es vs hs hw ih =>
    by_cases hExit : s.pc = 7742
    · exact (softmaxReturnTail hExit hFrame.2.1 (.ev hs hw) (List.mem_of_getElem? he) hEnd).elim
    obtain ⟨hl, hh, hu⟩ := softmaxAddressStep hp hLo (by omega) hFrame (.inr ⟨_, rfl, hs⟩)
    have hU := softmaxScratchStep hLo (by omega) hFrame.1 hScratch (.inr ⟨_, rfl, hs⟩)
    cases index with
    | zero =>
      obtain rfl : ev = e := Option.some.inj he
      exact ⟨s, u, vs, hFrame.1, hu.1, hU, hs, hw⟩
    | succ j =>
      exact ih hl hh hu hU he (by simp only [List.length_cons] at hLater; omega)
  | last => simp at hLater

/-- The actual continuation of a recorded softmax event with another event in its trace.
The returned scratch frame belongs to this occurrence even when an event repeats. -/
theorem softmaxAfterRecordedEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e) (hLo : 3420 ≤ e.pc)
    (hHi : e.pc < 7742) (hNext : index+1 < (X.tr g).length) :
    ∃ t u rest, t.sub ≤ 3 ∧ u.sub ≤ 3 ∧ ScoreScratchState u ∧
      EStep kernel Assumptions.all l g t e (some u) ∧
      Walk kernel Assumptions.all l g u ((X.tr g).drop (index+1)) rest := by
  obtain ⟨w, _, pos, s, _, hIndex, hAt, hRun⟩ := softmaxBodySuffix hp hX he hLo hHi
  have hF := addressFrameAtRoleEntry hAt
  obtain ⟨_, hw⟩ := walkFromRun hRun
  have hGet : ((X.tr g).drop pos)[index-pos]? = some e := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le hIndex]
  have hLater : index-pos+1 < ((X.tr g).drop pos).length := by
    rw [List.length_drop]
    omega
  obtain ⟨t, u, rest, ht, hu, hScratch, hEvent, hw⟩ := returningScoreSuffix hp hw
    (by rw [hAt.1]) (by rw [hAt.1]; decide) hF
    (scratchStateOfClear ⟨hAt.2.1, hAt.2.2.1⟩) hGet hHi hLater
  rw [List.drop_drop, show pos+(index-pos+1) = index+1 by omega] at hw
  exact ⟨t, u, rest, ht, hu, hScratch, hEvent, hw⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
