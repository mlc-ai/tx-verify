-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaMbarAddress
public import Kernels.TmlFa4Fwd.Proof.MmaPoll
public import Kernels.TmlFa4Fwd.Proof.MmaCommit
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
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Lemmas.Step.CtaBar
import Lemmas.Flow.TcTmpl
import Kernels.TmlFa4Fwd.Flow.Code.Part035
import Kernels.TmlFa4Fwd.Flow.Code.Part036
import Kernels.TmlFa4Fwd.Flow.Code.Part038
import Kernels.TmlFa4Fwd.Flow.Code.Part039
import Kernels.TmlFa4Fwd.Flow.Code.Part041

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue

noncomputable section

section
variable {l : Launch}

private theorem coreLocalResult {g pc : Nat} {s u us : TState} {op : Op} (hPc : s.pc = pc)
    (hf : s.fault = none) (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hx : execLocal l g s op = .ok us) (ht : Tau kernel [] l g s u) : u = us := by
  have hx' : execLocalA [] l g s op = .ok us := hx
  have hOut : out kernel [] l g s = .tau us := by
    simp only [out, hPc, hf, hc, guardHolds, pure, Except.pure, hl, ↓reduceIte, hx']
  exact Out.tau.inj (ht.symm.trans hOut)

/-- Increment a decoded three-slot index, leaving a value in one through three. -/
theorem bumpSlot {g pc d r : Nat} {s u : TState} (hPc : s.pc = pc) (hf : s.fault = none)
    (hc : kernel.code[pc]? = some ⟨none,
      .int ⟨.add, .int .s 32, false, [some d], [.reg r, .imm 1]⟩⟩) (n : Fin 3)
    (hWord : s.regs r = some (b32 n.val)) (ht : Tau kernel [] l g s u) :
    u.regs d = some (b32 (n.val + 1)) := by
  have h := coreLocalResult hPc hf hc rfl (us := next (setReg s d (b32 (n.val + 1)))) ?_ ht
  · subst u
    exact Function.update_self _ _ _
  · rw [execLocal_int rfl]
    fin_cases n <;> simp only [execInt, DType.width, hWord, readValue, readBits, readReg,
      bind, Except.bind, pure, Except.pure] <;> rfl

/-- Compare the incremented slot with the ring size. -/
theorem compareBump {g pc d r : Nat} {s u : TState} (hPc : s.pc = pc) (hf : s.fault = none)
    (hc : kernel.code[pc]? = some ⟨none,
      .int ⟨.setp .eq none, .int .b 32, false, [some d], [.reg r, .imm 3]⟩⟩) (n : Fin 3)
    (hWord : s.regs r = some (b32 (n.val + 1))) (ht : Tau kernel [] l g s u) :
    u.regs d = some (.pred (n.val + 1 == 3)) := by
  have hx : execLocal l g s (.int ⟨.setp .eq none, .int .b 32, false, [some d],
      [.reg r, .imm 3]⟩) = .ok (next (setReg s d (.pred (n.val + 1 == 3)))) := by
    rw [execLocal_int rfl]
    fin_cases n <;> simp only [execInt, DType.width, hWord, readBits, readReg,
      bind, Except.bind, pure, Except.pure] <;> rfl
  obtain rfl := coreLocalResult hPc hf hc rfl hx ht
  exact Function.update_self _ _ _

/-- Use the wrap predicate to normalize the incremented slot into the three-slot ring. -/
theorem selectSlot {g pc d r q : Nat} {s u : TState} (hPc : s.pc = pc) (hf : s.fault = none)
    (hc : kernel.code[pc]? = some ⟨none,
      .int ⟨.selp, .int .b 32, false, [some d], [.imm 0, .reg r, .reg q]⟩⟩) (n : Fin 3)
    (hWord : s.regs r = some (b32 (n.val + 1))) (hPred : s.regs q = some (.pred (n.val + 1 == 3)))
    (ht : Tau kernel [] l g s u) :
    ∃ k : Fin 3, u.regs d = some (b32 k.val) := by
  let k : Fin 3 := ⟨(n.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
  have hx : execLocal l g s (.int ⟨.selp, .int .b 32, false, [some d],
      [.imm 0, .reg r, .reg q]⟩) = .ok (next (setReg s d (b32 k.val))) := by
    rw [execLocal_selp rfl]
    fin_cases n
    · have h := show s.regs q = some (.pred false) from hPred
      have hw := show s.regs r = some (b32 1) from hWord
      simp [execMove, DType.width, h, hw, readValue, readReg, Value.bytes, bind, Except.bind,
        pure, Except.pure, k, b32]
    · have h := show s.regs q = some (.pred false) from hPred
      have hw := show s.regs r = some (b32 2) from hWord
      simp [execMove, DType.width, h, hw, readValue, readReg, Value.bytes, bind, Except.bind,
        pure, Except.pure, k, b32]
    · have h := show s.regs q = some (.pred true) from hPred
      simp [execMove, DType.width, h, readValue, readReg, readBits, Value.bytes, bind, Except.bind,
        pure, Except.pure, k, b32]
      rfl
  obtain rfl := coreLocalResult hPc hf hc rfl hx ht
  exact ⟨k, Function.update_self _ _ _⟩

/-- Scale the three-slot index to the barrier's byte stride. -/
theorem bytesOfSlot {g pc d r : Nat} {s u : TState} (hPc : s.pc = pc) (hf : s.fault = none)
    (hc : kernel.code[pc]? = some ⟨none,
      .int ⟨.shl, .int .b 32, false, [some d], [.reg r, .imm 3]⟩⟩) (n : Fin 3)
    (hWord : s.regs r = some (b32 n.val)) (ht : Tau kernel [] l g s u) :
    u.regs d = some (b32 (8 * n.val)) := by
  have hx : execLocal l g s (.int ⟨.shl, .int .b 32, false, [some d],
      [.reg r, .imm 3]⟩) = .ok (next (setReg s d (b32 (8 * n.val)))) := by
    rw [execLocal_int rfl]
    fin_cases n <;> simp only [execInt, DType.width, hWord, readBits, readReg,
      bind, Except.bind, pure, Except.pure] <;> rfl
  obtain rfl := coreLocalResult hPc hf hc rfl hx ht
  exact Function.update_self _ _ _

/-- Add a verified byte index to the shared base register. -/
theorem slotAddress {g pc d r : Nat} {s u : TState} (hPc : s.pc = pc) (hf : s.fault = none)
    (hc : kernel.code[pc]? = some ⟨none,
      .int ⟨.add, .int .s 32, false, [some d], [.reg 2535, .reg r]⟩⟩)
    (hBase : s.regs 2535 = some (b32 l.sharedBase)) (n : Fin 3)
    (hWord : s.regs r = some (b32 (8 * n.val))) (hBound : l.sharedBase + 8 * n.val < 2 ^ 32)
    (ht : Tau kernel [] l g s u) :
    u.regs d = some (b32 (l.sharedBase + 8 * n.val)) := by
  have hA : l.sharedBase < 2 ^ 32 := by omega
  have hB : 8 * n.val < 2 ^ 32 := by omega
  have hx : execLocal l g s (.int ⟨.add, .int .s 32, false, [some d],
      [.reg 2535, .reg r]⟩) = .ok (next (setReg s d (b32 (l.sharedBase + 8 * n.val)))) := by
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, readValue, readReg, hBase, hWord,
      readBits_b32 hBase hA, readBits_b32 hWord hB, b32, bind, Except.bind, pure, Except.pure]
    rw [← BitVec.ofNat_add, truncBits_ofNat hBound (by decide)]
  obtain rfl := coreLocalResult hPc hf hc rfl hx ht
  exact Function.update_self _ _ _
end

/-- Add an immediate displacement to an indexed shared address. -/
theorem slotDisplacedAddress {l : Launch} {g pc d r off : Nat} {s u : TState}
    (hPc : s.pc = pc) (hf : s.fault = none)
    (hc : kernel.code[pc]? = some ⟨none,
      .int ⟨.add, .int .s 32, false, [some d], [.reg r, .imm off]⟩⟩)
    (n : Fin 3) (hWord : s.regs r = some (b32 (l.sharedBase + 8 * n.val)))
    (hBound : l.sharedBase + (8 * n.val + off) < 2 ^ 32) (ht : Tau kernel [] l g s u) :
    u.regs d = some (b32 (l.sharedBase + (8 * n.val + off))) := by
  have hA : l.sharedBase + 8 * n.val < 2 ^ 32 := by omega
  have hB : off < 2 ^ 32 := by omega
  have hImm : readBits l g s 32 (.imm off) = .ok (BitVec.ofNat 64 off) := by
    simp only [readBits, BitVec.ofInt_natCast, truncBits_ofNat hB (by decide), pure, Except.pure]
  have hx : execLocal l g s (.int ⟨.add, .int .s 32, false, [some d],
      [.reg r, .imm off]⟩) = .ok (next (setReg s d (b32 (l.sharedBase + (8 * n.val + off))))) := by
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, readValue, readReg, hWord,
      readBits_b32 hWord hA, hImm, b32, bind, Except.bind, pure, Except.pure]
    rw [← BitVec.ofNat_add, Nat.add_assoc, truncBits_ofNat hBound (by decide)]
  obtain rfl := coreLocalResult hPc hf hc rfl hx ht
  exact Function.update_self _ _ _

/-- Register forms used in decoded three-slot address calculations. -/
inductive RingValue
  | slot (reg : Nat)
  | bumped (reg : Nat)
  | compared (reg pred : Nat)
  | byteOffset (reg : Nat)
  | address (reg displacement : Nat)
  deriving DecidableEq

/-- The registers holding a ring operand and any predicate correlated with it. -/
def RingValue.registers : RingValue → List Nat
  | .slot r | .bumped r | .byteOffset r | .address r _ => [r]
  | .compared r q => [r, q]

/-- The word for a specific slot and decoded operand form. -/
def RingValue.argument (l : Launch) (n : Fin 3) : RingValue → Value
  | .slot _ => b32 n.val
  | .bumped _ | .compared .. => b32 (n.val + 1)
  | .byteOffset _ => b32 (8 * n.val)
  | .address _ d => b32 (l.sharedBase + (8 * n.val + d))

/-- A decoded ring operand carries a register word for some slot. -/
def RingValue.matches (l : Launch) (s : TState) (v : RingValue) : Prop :=
  ∃ n : Fin 3,
    s.regs (v.registers.headD 0) = some (v.argument l n) ∧
    match v with
    | .compared _ q => s.regs q = some (.pred (n.val + 1 == 3))
    | _ => True

/-- Preserving the operand registers preserves their ring interpretation. -/
theorem RingValue.preserved {l : Launch} {s u : TState} {v : RingValue}
    (h : v.matches l s) (hKeep : ∀ r ∈ v.registers, u.regs r = s.regs r) : v.matches l u := by
  cases v <;> simp only [RingValue.matches, RingValue.registers, List.headD_cons] at h ⊢
  all_goals obtain ⟨n, hn, hTail⟩ := h
  all_goals refine ⟨n, (hKeep _ (by simp [RingValue.registers])).trans hn, ?_⟩
  case compared => exact (hKeep _ (by simp [RingValue.registers])).trans hTail
  all_goals trivial

/-- A ring operand and the program-counter range where it is used. -/
structure RingFact where
  value : RingValue
  firstPc : Nat
  lastPc : Nat
  definitions : List Nat
  deriving DecidableEq

def ringFacts : List RingFact :=
  [⟨.slot 7207, 2281, 2638, [2280, 2287, 2526]⟩,
   ⟨.byteOffset 2575, 2292, 2292, [2291]⟩,
   ⟨.address 1191 0, 2293, 2462, [2292]⟩,
   ⟨.address 2568 32, 2294, 2296, [2293]⟩,
   ⟨.bumped 2584, 2345, 2346, [2344]⟩,
   ⟨.compared 2584 389, 2346, 2346, [2345]⟩,
   ⟨.slot 1192, 2347, 2524, [2346]⟩,
   ⟨.byteOffset 2586, 2350, 2350, [2349]⟩,
   ⟨.address 1193 0, 2351, 2523, [2350]⟩,
   ⟨.address 2571 32, 2352, 2354, [2351]⟩,
   ⟨.bumped 2605, 2525, 2526, [2524]⟩,
   ⟨.compared 2605 398, 2526, 2526, [2525]⟩,
   ⟨.byteOffset 2619, 2543, 2543, [2542]⟩,
   ⟨.address 1194 0, 2544, 2638, [2543]⟩,
   ⟨.address 2609 32, 2545, 2547, [2544]⟩]

/-- The live program counters of a ring operand. -/
def RingFact.active (f : RingFact) (pc : Nat) : Prop :=
  f.firstPc ≤ pc ∧ pc ≤ f.lastPc

instance (f : RingFact) (pc : Nat) : Decidable (f.active pc) :=
  inferInstanceAs (Decidable (f.firstPc ≤ pc ∧ pc ≤ f.lastPc))

def ringRegisters (l : Launch) (s : TState) : Prop :=
  ∀ f ∈ ringFacts, f.active s.pc → f.value.matches l s

/-- The local address frame established on entry by MMA and preserved by its actual steps. -/
def RingAddressFrame (l : Launch) (s : TState) : Prop :=
  RoleShape s ∧ s.regs 1062 = some (b32 12) ∧ s.regs 2535 = some (b32 l.sharedBase) ∧
    ringRegisters l s

private def ringLocalSource (pc : Nat) (i : Instr) (f : RingFact) : Bool :=
  if f.definitions.contains pc then i.guard.isNone && i.op.isLocal
  else !decide (f.active pc) || f.value.registers.all (fun r => !(mmaWrites i.op).contains r)

private def ringBranch (pc : Nat) (op : Op) (f : RingFact) : Bool :=
  match op with
  | .bra target _ => !decide (f.active target) || decide (f.active pc)
  | .brx .. => false
  | _ => true

private def ringCode (pc : Nat) (i : Instr) : Bool :=
  !(mmaWrites i.op).contains 2535 &&
  ringFacts.all (fun f =>
    ringLocalSource pc i f &&
    (!decide (f.active (pc + 1)) || f.definitions.contains pc || decide (f.active pc)) &&
    ringBranch pc i.op f)

private theorem ringCodeAt {pc : Nat} {i : Instr}
    (hLo : 1907 ≤ pc) (hHi : pc < 2768) (hc : kernel.code[pc]? = some i) :
    ringCode pc i = true := by
  let code := ((kernel.code.drop 1907).take (2768 - 1907)).zipIdx 1907
  have hAll : code.all (fun (ins, site) => ringCode site ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, pc)
  apply List.mem_of_getElem? (i := pc - 1907)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem ringAt {l : Launch} {s : TState} {pc : Nat}
    (hFrame : ringRegisters l s) (hPc : s.pc = pc) (f : RingFact)
    (hf : f ∈ ringFacts) (ha : f.active pc) : f.value.matches l s :=
  hFrame f hf (hPc.symm ▸ ha)

private theorem literalSlot {l : Launch} {g pc d : Nat} {s u : TState}
    (hPc : s.pc = pc) (hf : s.fault = none)
    (hc : kernel.code[pc]? = some ⟨none,
      .move ⟨.scalar, .int .b 32, [some d], [.imm 1]⟩⟩)
    (ht : Tau kernel [] l g s u) : u.regs d = some (b32 1) := by
  have hx : execLocal l g s (.move ⟨.scalar, .int .b 32, [some d], [.imm 1]⟩) =
      .ok (next (setReg s d (b32 1))) := by
    rw [execLocal_move rfl]
    simp [execMove, readValue, readBits, DType.width, Value.bytes, b32,
      bind, Except.bind, pure, Except.pure]
    rfl
  obtain rfl := coreLocalResult hPc hf hc rfl hx ht
  exact Function.update_self _ _ _

private theorem definesRingValue {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} {f : RingFact} (hF : f ∈ ringFacts)
    (hDef : s.pc ∈ f.definitions) (hf : s.fault = none)
    (hb : s.regs 2535 = some (b32 l.sharedBase)) (hRegs : ringRegisters l s)
    (ht : Tau kernel [] l g s u) : f.value.matches l u := by
  have hBounds (n : Fin 3) : l.sharedBase + 8 * n.val < 2 ^ 32 ∧
      l.sharedBase + (8 * n.val + 32) < 2 ^ 32 := by
    have := hp.shared.2.1
    have := n.isLt
    omega
  simp only [ringFacts, List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hDef
  · rcases hDef with hPc | hPc | hPc
    · exact ⟨1, literalSlot hPc hf Flow.code_2280 ht, trivial⟩
    · exact ⟨1, literalSlot hPc hf Flow.code_2287 ht, trivial⟩
    · obtain ⟨n, hn, hPred⟩ := ringAt hRegs hPc
        ⟨.compared 2605 398, 2526, 2526, [2525]⟩ (by decide) (by decide)
      obtain ⟨k, hk⟩ := selectSlot hPc hf Flow.code_2526 n hn hPred ht
      exact ⟨k, hk, trivial⟩
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.slot 7207, 2281, 2638, [2280, 2287, 2526]⟩ (by decide) (by decide)
    exact ⟨n, bytesOfSlot hDef hf Flow.code_2291 n hn ht, trivial⟩
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.byteOffset 2575, 2292, 2292, [2291]⟩ (by decide) (by decide)
    refine ⟨n, ?_, trivial⟩
    simpa [RingValue.registers, RingValue.argument] using
      slotAddress hDef hf Flow.code_2292 hb n hn (hBounds n).1 ht
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.address 1191 0, 2293, 2462, [2292]⟩ (by decide) (by decide)
    refine ⟨n, slotDisplacedAddress hDef hf Flow.code_2293 n ?_ (hBounds n).2 ht, trivial⟩
    simpa [RingValue.registers, RingValue.argument] using hn
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.slot 7207, 2281, 2638, [2280, 2287, 2526]⟩ (by decide) (by decide)
    exact ⟨n, bumpSlot hDef hf Flow.code_2344 n hn ht, trivial⟩
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.bumped 2584, 2345, 2346, [2344]⟩ (by decide) (by decide)
    have hKeep := tau_core_regs (hDef.symm ▸ Flow.code_2345) ht
      (show 2584 ∉ writesRegs (.int ⟨.setp .eq none, .int .b 32, false, [some 389],
        [.reg 2584, .imm 3]⟩) by decide)
    exact ⟨n, hKeep.trans hn, compareBump hDef hf Flow.code_2345 n hn ht⟩
  · obtain ⟨n, hn, hPred⟩ := ringAt hRegs hDef
      ⟨.compared 2584 389, 2346, 2346, [2345]⟩ (by decide) (by decide)
    obtain ⟨k, hk⟩ := selectSlot hDef hf Flow.code_2346 n hn hPred ht
    exact ⟨k, hk, trivial⟩
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.slot 1192, 2347, 2524, [2346]⟩ (by decide) (by decide)
    exact ⟨n, bytesOfSlot hDef hf Flow.code_2349 n hn ht, trivial⟩
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.byteOffset 2586, 2350, 2350, [2349]⟩ (by decide) (by decide)
    refine ⟨n, ?_, trivial⟩
    simpa [RingValue.registers, RingValue.argument] using
      slotAddress hDef hf Flow.code_2350 hb n hn (hBounds n).1 ht
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.address 1193 0, 2351, 2523, [2350]⟩ (by decide) (by decide)
    refine ⟨n, slotDisplacedAddress hDef hf Flow.code_2351 n ?_ (hBounds n).2 ht, trivial⟩
    simpa [RingValue.registers, RingValue.argument] using hn
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.slot 1192, 2347, 2524, [2346]⟩ (by decide) (by decide)
    exact ⟨n, bumpSlot hDef hf Flow.code_2524 n hn ht, trivial⟩
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.bumped 2605, 2525, 2526, [2524]⟩ (by decide) (by decide)
    have hKeep := tau_core_regs (hDef.symm ▸ Flow.code_2525) ht
      (show 2605 ∉ writesRegs (.int ⟨.setp .eq none, .int .b 32, false, [some 398],
        [.reg 2605, .imm 3]⟩) by decide)
    exact ⟨n, hKeep.trans hn, compareBump hDef hf Flow.code_2525 n hn ht⟩
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.slot 7207, 2281, 2638, [2280, 2287, 2526]⟩ (by decide) (by decide)
    exact ⟨n, bytesOfSlot hDef hf Flow.code_2542 n hn ht, trivial⟩
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.byteOffset 2619, 2543, 2543, [2542]⟩ (by decide) (by decide)
    refine ⟨n, ?_, trivial⟩
    simpa [RingValue.registers, RingValue.argument] using
      slotAddress hDef hf Flow.code_2543 hb n hn (hBounds n).1 ht
  · obtain ⟨n, hn, _⟩ := ringAt hRegs hDef
      ⟨.address 1194 0, 2544, 2638, [2543]⟩ (by decide) (by decide)
    refine ⟨n, slotDisplacedAddress hDef hf Flow.code_2544 n ?_ (hBounds n).2 ht, trivial⟩
    simpa [RingValue.registers, RingValue.argument] using hn

private theorem ringAddressStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} {e : Option Event} (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hFrame : RingAddressFrame l s) (hw : WStep kernel Assumptions.all l g s e u) :
    (1907 ≤ u.pc ∧ u.pc < 2768 ∨ u.pc = 3099 ∧ u.fault = none) ∧ RingAddressFrame l u := by
  obtain ⟨hPc, hShape, hWarp⟩ := mmaCutStep hLo hHi hw ⟨hFrame.1, hFrame.2.1⟩
  have hKeepBase : u.regs 2535 = s.regs 2535 := by
    apply mmaStepReg (by omega) hHi _ hw
    intro i hc
    have h := ringCodeAt hLo hHi hc
    simp only [ringCode, Bool.and_eq_true] at h
    simpa using h.1
  refine ⟨by simpa using hPc, hShape, hWarp, hKeepBase.trans hFrame.2.2.1, ?_⟩
  intro f hF hActive
  have decoded {i : Instr} (hc : kernel.code[s.pc]? = some i) :
      (ringLocalSource s.pc i f &&
       (!decide (f.active (s.pc + 1)) || f.definitions.contains s.pc || decide (f.active s.pc)) &&
       ringBranch s.pc i.op f) = true := by
    have h := ringCodeAt hLo hHi hc
    simp only [ringCode, Bool.and_eq_true] at h
    exact List.all_eq_true.mp h.2 f hF
  have hPreserve (hNot : s.pc ∉ f.definitions) (hBefore : f.active s.pc) :
      f.value.matches l u := by
    apply RingValue.preserved (hFrame.2.2.2 f hF hBefore)
    intro r hr
    apply mmaStepReg (by omega) hHi _ hw
    intro i hc
    have h := decoded hc
    simp only [Bool.and_eq_true, ringLocalSource, List.contains_eq_mem, decide_eq_true_eq,
      ite_eq_right hNot, hBefore, decide_true, Bool.not_true, Bool.false_or] at h
    simpa using List.all_eq_true.mp h.1.1 r hr
  have hFall {i : Instr} (hc : kernel.code[s.pc]? = some i) (hNot : s.pc ∉ f.definitions)
      (hNext : u.pc = s.pc + 1) : f.active s.pc := by
    rw [hNext] at hActive
    have h := decoded hc
    simp only [Bool.and_eq_true] at h
    simpa [hActive, hNot] using h.1.2
  rcases hw with ⟨_, ht⟩ | ⟨ev, _, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← out_eq_core (by omega) hHi]
    obtain ⟨i, hc, hf, _⟩ := Softmax.tauScoreSource ht
    by_cases hDef : s.pc ∈ f.definitions
    · exact definesRingValue hp hF hDef hf hFrame.2.2.1 hFrame.2.2.2 ht'
    apply hPreserve hDef
    rcases tau_core_frame hc ht' with rfl | hf
    · exact hFall hc hDef rfl
    have hNext := hf.pc
    have hB := decoded hc
    simp only [Bool.and_eq_true] at hB
    cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hNext
    case bra target uni =>
      rw [hNext] at hActive
      simpa [ringBranch, ho, hActive] using hB.2
    case brx => simp [ringBranch, ho] at hB
    all_goals exact hFall hc hDef hNext
  · obtain ⟨i, hc, hl, _⟩ := estep_event_source he
    have hNot : s.pc ∉ f.definitions := by
      intro hDef
      have h := decoded hc
      simp [ringLocalSource, hl, hDef] at h
    apply hPreserve hNot
    have hE : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tm, hOut, hFire⟩ := he
      exact ⟨tm, by rwa [← out_eq_core (by omega) hHi], hFire⟩
    rcases (estep_return_pc hE (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h ▸ hActive
    · exact hFall hc hNot h

private theorem ringAddressWalk {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {events : List Event} {visits : List Visit}
    (hWalk : Walk kernel Assumptions.all l g s events visits)
    (hPc : 1907 ≤ s.pc ∧ s.pc < 2768) (hF : RingAddressFrame l s)
    {e : Event} (hm : e ∈ events) (hEnd : e.pc < 2768) :
    ∃ t o, t.pc = e.pc ∧ RingAddressFrame l t ∧ EStep kernel Assumptions.all l g t e o := by
  induction hWalk with
  | stop => cases hm
  | @tau s u events visits ht hw ih =>
    obtain ⟨hPc, hF'⟩ := ringAddressStep hp hPc.1 hPc.2 hF (.inl ⟨rfl, ht⟩)
    rcases hPc with h | h
    · exact ih h hF' hm
    · have hRet := mmaEpilogueExitEvents h.1 h.2 (.inl rfl) hF'.2.1 hw _ hm
      omega
  | @ev s u ev events visits he hw ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, _, (estep_source_pc he).symm, hF, he⟩
    · obtain ⟨hPc, hF'⟩ := ringAddressStep hp hPc.1 hPc.2 hF (.inr ⟨_, rfl, he⟩)
      rcases hPc with h | h
      · exact ih h hF' hm
      · have hRet := mmaEpilogueExitEvents h.1 h.2 (.inl rfl) hF'.2.1 hw _ hm
        omega
  | last he =>
    obtain rfl := List.mem_singleton.mp hm
    exact ⟨_, _, (estep_source_pc he).symm, hF, he⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem ringMbarSource {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 2294 ≤ e.pc) (hHi : e.pc < 2768) :
    ∃ t o, t.pc = e.pc ∧ RingAddressFrame l t ∧ EStep kernel Assumptions.all l g t e o := by
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hWarp : warpIndex l g = 12 := by
    rcases roleBodyPcOfEvent hp hX he (by omega) hHint with h | h
    · omega
    · split_ifs at h <;> omega
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨pos, t, o, hIndex, ht, hr⟩ := commonDispatchOfLateEvent hp hX hg he (by omega)
  have hLen : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hSuffix : (X.tr g).drop pos ≠ [] := by
    intro h
    exact Nat.not_le_of_lt hLen ((List.drop_eq_nil_iff.mp h).trans hIndex)
  obtain ⟨s, inst, hReq, hs, hRun⟩ := firstRegisterHintFromCommon hp hg
    (⟨12, by decide⟩ : Fin 16) (by simpa [hWarp] using ht) hr hSuffix
  have hAt : At s 1908 [(1062, b32 12), (2535, b32 l.sharedBase)] := hs
  have hLt : pos < index := by
    by_contra! h
    have hEq : pos = index := by omega
    rw [hEq] at hReq
    have hSame := congrArg Event.pc (Option.some.inj (hReq.symm.trans he))
    change 1907 = e.pc at hSame
    omega
  have hF : RingAddressFrame l s := by
    refine ⟨⟨hAt.2.1.symm ▸ Nat.zero_le _, hAt.2.2.1, fun _ => hAt.2.1⟩,
      hAt.2.2.2.2.1, hAt.2.2.2.2.2.1, ?_⟩
    intro f hf ha
    exfalso
    rw [hAt.1] at ha
    simp only [ringFacts, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact (by decide : ¬ RingFact.active _ 1908) ha
  obtain ⟨_, hWalk⟩ := walkFromRun hRun
  have hm : e ∈ (X.tr g).drop (pos + 1) := by
    apply List.mem_of_getElem? (i := index - (pos + 1))
    rw [List.getElem?_drop, Nat.add_sub_of_le hLt]
    exact he
  exact ringAddressWalk hp hWalk ⟨by rw [hAt.1]; decide, by rw [hAt.1]; decide⟩ hF hm hHi

/-- A ring-indexed MMA poll uses one of the three physical ready slots. -/
theorem mmaRingWaitAddress {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [2294, 2352, 2545]) :
    ∃ slot : Fin 3, target = ⟨.shared, g / l.block, l.sharedBase + (8 * slot.val + 32)⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hl : 2294 ≤ pc := by omega
  have hh : pc < 2768 := by omega
  obtain ⟨t, o, ht, hFrame, hStep⟩ := ringMbarSource hp hX he hl hh
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl | rfl
  · rw [ht, Flow.code_2294] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨n, hb, _⟩ := ringAt hFrame.2.2.2 ht
      ⟨.address 2568 32, 2294, 2296, [2293]⟩ (by decide) (by decide)
    change t.regs 2568 = some (b32 (l.sharedBase + (8 * n.val + 32))) at hb
    exact ⟨n, pollResolvedMbarAddress hp hb
      (by unfold initializedMbarOffset; fin_cases n <;> decide) hFire rfl⟩
  · rw [ht, Flow.code_2352] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨n, hb, _⟩ := ringAt hFrame.2.2.2 ht
      ⟨.address 2571 32, 2352, 2354, [2351]⟩ (by decide) (by decide)
    change t.regs 2571 = some (b32 (l.sharedBase + (8 * n.val + 32))) at hb
    exact ⟨n, pollResolvedMbarAddress hp hb
      (by unfold initializedMbarOffset; fin_cases n <;> decide) hFire rfl⟩
  · rw [ht, Flow.code_2545] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨n, hb, _⟩ := ringAt hFrame.2.2.2 ht
      ⟨.address 2609 32, 2545, 2547, [2544]⟩ (by decide) (by decide)
    change t.regs 2609 = some (b32 (l.sharedBase + (8 * n.val + 32))) at hb
    exact ⟨n, pollResolvedMbarAddress hp hb
      (by unfold initializedMbarOffset; fin_cases n <;> decide) hFire rfl⟩

/-- Every MMA poll indexed by the three-slot ring names an initialized CTA object. -/
theorem mmaRingWaitInitObject {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [2294, 2352, 2545]) :
    ∃ i : Fin 34, target = initObject l (g / l.block) i := by
  obtain ⟨slot, rfl⟩ := mmaRingWaitAddress hp hX he hSite
  apply initObjectOfOffset
  unfold initializedMbarOffset
  fin_cases slot <;> decide

/-- Every MMA commit indexed by the three-slot ring names an initialized CTA object. -/
theorem mmaRingCommitAddress {g index pc : Nat} {spec : TcCommit.Spec} {rank : Fin 16}
    {target : Loc} (he : X.get (g, index) = some ⟨pc, .tc (.commit spec)⟩)
    (hSite : pc ∈ [2462, 2523, 2638]) (hTarget : TcCommit.target spec rank = some target) :
    ∃ stage : Fin 3, target = ⟨.shared, g / l.block, l.sharedBase + (8 * stage.val + 56)⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hl : 2294 ≤ pc := by omega
  have hh : pc < 2768 := by omega
  obtain ⟨t, o, ht, hFrame, hStep⟩ := ringMbarSource hp hX he hl hh
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  have hg := Step.CtaBar.thread_lt_of_get hX he
  rcases hSite with rfl | rfl | rfl
  · rw [ht, Flow.code_2462] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨n, hb, _⟩ := ringAt hFrame.2.2.2 ht
      ⟨.address 1191 0, 2293, 2462, [2292]⟩ (by decide) (by decide)
    change t.regs 1191 = some (b32 (l.sharedBase + (8 * n.val + 0))) at hb
    refine ⟨n, ?_⟩
    simpa only [Nat.add_zero] using
      (commitExactAddress hp hg hb
        (by unfold initializedMbarOffset; fin_cases n <;> decide) hFire rfl hTarget)
  · rw [ht, Flow.code_2523] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨n, hb, _⟩ := ringAt hFrame.2.2.2 ht
      ⟨.address 1193 0, 2351, 2523, [2350]⟩ (by decide) (by decide)
    change t.regs 1193 = some (b32 (l.sharedBase + (8 * n.val + 0))) at hb
    refine ⟨n, ?_⟩
    simpa only [Nat.add_zero] using
      (commitExactAddress hp hg hb
        (by unfold initializedMbarOffset; fin_cases n <;> decide) hFire rfl hTarget)
  · rw [ht, Flow.code_2638] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨n, hb, _⟩ := ringAt hFrame.2.2.2 ht
      ⟨.address 1194 0, 2544, 2638, [2543]⟩ (by decide) (by decide)
    change t.regs 1194 = some (b32 (l.sharedBase + (8 * n.val + 0))) at hb
    refine ⟨n, ?_⟩
    simpa only [Nat.add_zero] using
      (commitExactAddress hp hg hb
        (by unfold initializedMbarOffset; fin_cases n <;> decide) hFire rfl hTarget)

/-- Every actual MMA poll, in any scheduler iteration, names an initialized CTA barrier. -/
theorem mmaWaitInitObject {g index : Nat} (site : Fin 14) {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope}
    (he : X.get (g, index) = some ⟨(waitSite site).pc, .wait target q ok acq scope⟩) :
    ∃ i : Fin 34, target = initObject l (g / l.block) i := by
  fin_cases site
  all_goals first
    | exact mmaFixedWaitInitObject hp hX he (by decide)
    | exact mmaRingWaitInitObject hp hX he (by decide)

end

theorem ringFrameAtEntry {l : Launch} {s : TState}
    (hs : At s 1908 [(1062, b32 12), (2535, b32 l.sharedBase)]) :
    RingAddressFrame l s := by
  refine ⟨⟨by rw [hs.2.1]; decide, hs.2.2.1, fun _ => hs.2.1⟩, hs.2.2.2.2.1,
    hs.2.2.2.2.2.1, ?_⟩
  intro f hf ha
  exfalso
  rw [hs.1] at ha
  simp only [ringFacts, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact (by decide : ¬ RingFact.active _ 1908) ha

theorem ringFrameStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768) (hFrame : RingAddressFrame l s)
    (hw : WStep kernel Assumptions.all l g s e u) :
    (1907 ≤ u.pc ∧ u.pc < 2768 ∨ u.pc = 3099 ∧ u.fault = none) ∧ RingAddressFrame l u :=
  ringAddressStep hp hLo hHi hFrame hw

/-- The only register carrying the un-displaced shared address across each recurring release. -/
structure RingCarrier where
  calcPc : Nat
  releasePc : Nat
  base : Nat
  waitBase : Nat

def ringCarrier : Fin 3 → RingCarrier
  | 0 => ⟨2293, 2462, 1191, 2568⟩
  | 1 => ⟨2351, 2523, 1193, 2571⟩
  | 2 => ⟨2544, 2638, 1194, 2609⟩

/-- The address frame identifies the common, undisplaced base at each live point. -/
theorem ringCarrierValue (i : Fin 3) {l : Launch} {s : TState}
    (hF : RingAddressFrame l s) (hLo : (ringCarrier i).calcPc ≤ s.pc)
    (hHi : s.pc ≤ (ringCarrier i).releasePc) :
    ∃ stage : Fin 3, s.regs (ringCarrier i).base = some (b32 (l.sharedBase + 8 * stage.val)) := by
  have hAt (f : RingFact) (hm : f ∈ ringFacts) (hs : f.active s.pc) :=
    hF.2.2.2 f hm hs
  fin_cases i
  · obtain ⟨n, h, _⟩ := hAt ⟨.address 1191 0, 2293, 2462, [2292]⟩ (by decide) ⟨hLo, hHi⟩
    exact ⟨n, by simpa [RingValue.argument, RingValue.registers, ringCarrier] using h⟩
  · obtain ⟨n, h, _⟩ := hAt ⟨.address 1193 0, 2351, 2523, [2350]⟩ (by decide) ⟨hLo, hHi⟩
    exact ⟨n, by simpa [RingValue.argument, RingValue.registers, ringCarrier] using h⟩
  · obtain ⟨n, h, _⟩ := hAt ⟨.address 1194 0, 2544, 2638, [2543]⟩ (by decide) ⟨hLo, hHi⟩
    exact ⟨n, by simpa [RingValue.argument, RingValue.registers, ringCarrier] using h⟩

theorem ringCarrierCalcCode (i : Fin 3) :
    let c := ringCarrier i
    kernel.code[c.calcPc]? = some ⟨none,
      .int ⟨.add, .int .s 32, false, [some c.waitBase], [.reg c.base, .imm 32]⟩⟩ := by
  fin_cases i
  · exact Flow.code_2293
  · exact Flow.code_2351
  · exact Flow.code_2544

/-- The single ready address calculation preserves the carrier and derives its displaced word. -/
theorem ringCarrierReadyStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (i : Fin 3) {g : Nat} {s u : TState} (hPc : s.pc = (ringCarrier i).calcPc)
    (hF : RingAddressFrame l s) (ht : Tau kernel [] l g s u) :
    ∃ stage : Fin 3,
      u.regs (ringCarrier i).base = some (b32 (l.sharedBase + 8 * stage.val)) ∧
      u.regs (ringCarrier i).waitBase = some (b32 (l.sharedBase + (8 * stage.val + 32))) := by
  let c := ringCarrier i
  obtain ⟨stage, hStage⟩ := ringCarrierValue i hF hPc.ge
    (hPc.trans_le (by fin_cases i <;> decide))
  have hf : s.fault = none := by
    cases h : s.fault
    · rfl
    · simp [Tau, out, h] at ht
  have hBound : l.sharedBase + (8 * stage.val + 32) < 2 ^ 32 := by
    have hBase := hp.shared.2.1
    have hn := stage.isLt
    omega
  have hc := ringCarrierCalcCode i
  have bne : c.base ∉ writesRegs (.int ⟨.add, .int .s 32, false,
      [some c.waitBase], [.reg c.base, .imm 32]⟩) := by
    fin_cases i <;> decide
  have hc' : kernel.code[s.pc]? = some ⟨none,
      .int ⟨.add, .int .s 32, false, [some c.waitBase], [.reg c.base, .imm 32]⟩⟩ := by
    rw [hPc]
    exact hc
  exact ⟨stage, (tau_core_regs hc' ht bne).trans hStage,
    slotDisplacedAddress hPc hf hc stage hStage hBound ht⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
