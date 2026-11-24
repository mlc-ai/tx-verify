-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderMbarAddress
public import Kernels.TmlFa4Fwd.Proof.MmaRingAddress
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
import Kernels.TmlFa4Fwd.Flow.Code.Part005
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part015
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018
import Kernels.TmlFa4Fwd.Flow.Code.Part020
import Kernels.TmlFa4Fwd.Flow.Code.Part021
import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Kernels.TmlFa4Fwd.Flow.Code.Part025
import Kernels.TmlFa4Fwd.Flow.Code.Part027
import Kernels.TmlFa4Fwd.Flow.Code.Part029

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open Mma Prologue Epilogue Softmax

noncomputable section

private inductive LoaderSlotOp
  | literal (reg : Nat) (slot : Fin 3)
  | bump (reg src : Nat)
  | compare (reg pred : Nat)
  | select (reg src pred : Nat)
  | scale (reg src : Nat)
  | base (reg src : Nat)
  | displace (reg src offset : Nat)

private def LoaderSlotOp.output : LoaderSlotOp → RingValue
  | .literal r _ | .select r _ _ => .slot r
  | .bump r _ => .bumped r
  | .compare r q => .compared r q
  | .scale r _ => .byteOffset r
  | .base r _ => .address r 0
  | .displace r _ off => .address r off

private def LoaderSlotOp.input : LoaderSlotOp → Option RingValue
  | .literal .. => none
  | .bump _ r | .scale _ r => some (.slot r)
  | .compare r _ => some (.bumped r)
  | .select _ r q => some (.compared r q)
  | .base _ r => some (.byteOffset r)
  | .displace _ r _ => some (.address r 0)

private def LoaderSlotOp.instruction : LoaderSlotOp → Op
  | .literal r slot => .move ⟨.scalar, .int .b 32, [some r], [.imm slot.val]⟩
  | .bump r src => .int ⟨.add, .int .s 32, false, [some r], [.reg src, .imm 1]⟩
  | .compare r q => .int ⟨.setp .eq none, .int .b 32, false, [some q], [.reg r, .imm 3]⟩
  | .select r src q => .int ⟨.selp, .int .b 32, false, [some r], [.imm 0, .reg src, .reg q]⟩
  | .scale r src => .int ⟨.shl, .int .b 32, false, [some r], [.reg src, .imm 3]⟩
  | .base r src => .int ⟨.add, .int .s 32, false, [some r], [.reg 2535, .reg src]⟩
  | .displace r src off => .int ⟨.add, .int .s 32, false, [some r], [.reg src, .imm off]⟩

private def loaderRingWritesAt : List (Nat × LoaderSlotOp) :=
  [(371, .literal 7179 0),
   (910, .literal 7179 2),
   (914, .literal 7179 2),
   (957, .scale 1977 7179),
   (958, .base 1122 1977),
   (959, .displace 1976 1122 56),
   (1138, .bump 2037 7179),
   (1139, .compare 2037 185),
   (1140, .select 1139 2037 185),
   (1203, .scale 2065 1139),
   (1204, .base 1141 2065),
   (1205, .displace 2063 1141 56),
   (1343, .bump 2116 1139),
   (1344, .compare 2116 198),
   (1345, .select 7179 2116 198),
   (1427, .scale 2139 7179),
   (1428, .base 1151 2139),
   (1429, .displace 2138 1151 56),
   (1603, .bump 2195 7179),
   (1604, .compare 2195 228),
   (1605, .select 1170 2195 228),
   (1608, .scale 2197 1170),
   (1609, .base 1171 2197),
   (1610, .displace 2140 1171 56),
   (1736, .bump 2237 1170),
   (1737, .compare 2237 229),
   (1738, .select 7179 2237 229),
   (1863, .scale 2293 7179),
   (1864, .base 2294 2293),
   (1865, .displace 2288 2294 56),
   (1869, .bump 2295 7179),
   (1870, .compare 2295 259),
   (1871, .select 2296 2295 259),
   (1874, .scale 2298 2296),
   (1875, .base 2299 2298),
   (1876, .displace 2289 2299 56),
   (1880, .bump 2300 2296),
   (1881, .compare 2300 260),
   (1882, .select 2301 2300 260),
   (1885, .scale 2303 2301),
   (1886, .base 2304 2303),
   (1887, .displace 2291 2304 56)]

/-- The live register intervals for the loader ring operands. -/
def loaderRingFacts : List RingFact :=
  [⟨.slot 7179, 372, 1869, [371, 910, 914, 1345, 1738]⟩,
   ⟨.byteOffset 1977, 958, 958, [957]⟩,
   ⟨.address 1122 0, 959, 1137, [958]⟩,
   ⟨.address 1976 56, 960, 962, [959]⟩,
   ⟨.bumped 2037, 1139, 1139, [1138]⟩,
   ⟨.compared 2037 185, 1140, 1140, [1139]⟩,
   ⟨.slot 1139, 1141, 1343, [1140]⟩,
   ⟨.byteOffset 2065, 1204, 1204, [1203]⟩,
   ⟨.address 1141 0, 1205, 1342, [1204]⟩,
   ⟨.address 2063 56, 1206, 1208, [1205]⟩,
   ⟨.bumped 2116, 1344, 1344, [1343]⟩,
   ⟨.compared 2116 198, 1345, 1345, [1344]⟩,
   ⟨.byteOffset 2139, 1428, 1428, [1427]⟩,
   ⟨.address 1151 0, 1429, 1602, [1428]⟩,
   ⟨.address 2138 56, 1430, 1432, [1429]⟩,
   ⟨.bumped 2195, 1604, 1604, [1603]⟩,
   ⟨.compared 2195 228, 1605, 1605, [1604]⟩,
   ⟨.slot 1170, 1606, 1736, [1605]⟩,
   ⟨.byteOffset 2197, 1609, 1609, [1608]⟩,
   ⟨.address 1171 0, 1610, 1735, [1609]⟩,
   ⟨.address 2140 56, 1611, 1613, [1610]⟩,
   ⟨.bumped 2237, 1737, 1737, [1736]⟩,
   ⟨.compared 2237 229, 1738, 1738, [1737]⟩,
   ⟨.byteOffset 2293, 1864, 1864, [1863]⟩,
   ⟨.address 2294 0, 1865, 1865, [1864]⟩,
   ⟨.address 2288 56, 1866, 1868, [1865]⟩,
   ⟨.bumped 2295, 1870, 1870, [1869]⟩,
   ⟨.compared 2295 259, 1871, 1871, [1870]⟩,
   ⟨.slot 2296, 1872, 1880, [1871]⟩,
   ⟨.byteOffset 2298, 1875, 1875, [1874]⟩,
   ⟨.address 2299 0, 1876, 1876, [1875]⟩,
   ⟨.address 2289 56, 1877, 1879, [1876]⟩,
   ⟨.bumped 2300, 1881, 1881, [1880]⟩,
   ⟨.compared 2300 260, 1882, 1882, [1881]⟩,
   ⟨.slot 2301, 1883, 1885, [1882]⟩,
   ⟨.byteOffset 2303, 1886, 1886, [1885]⟩,
   ⟨.address 2304 0, 1887, 1887, [1886]⟩,
   ⟨.address 2291 56, 1888, 1890, [1887]⟩]

/-- Every live ring operand is represented by an initialized slot. -/
def loaderRingRegisters (l : Launch) (s : TState) : Prop :=
  ∀ f ∈ loaderRingFacts, f.active s.pc → f.value.matches l s

/-- The shared base and dispatch warp retained over the loader body. -/
def loaderRingRoots (l : Launch) (warp : Fin 2) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]

/-- The loader role frame, including all currently live ring operands. -/
def LoaderRingFrame (l : Launch) (warp : Fin 2) (s : TState) : Prop :=
  RingShape s ∧ Holds s.regs (loaderRingRoots l warp) ∧ loaderRingRegisters l s

private theorem liveRingFact {l : Launch} {s : TState} {pc : Nat}
    (hFrame : loaderRingRegisters l s) (hPc : s.pc = pc) (f : RingFact)
    (hf : f ∈ loaderRingFacts) (ha : f.active pc) : f.value.matches l s :=
  hFrame f hf (hPc.symm ▸ ha)

private theorem loaderRingWriteCode {pc : Nat} {op : LoaderSlotOp}
    (hw : (pc, op) ∈ loaderRingWritesAt) :
    kernel.code[pc]? = some ⟨none, op.instruction⟩ := by
  simp only [loaderRingWritesAt, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h |
    h | h
  all_goals cases h
  · exact Flow.code_371
  · exact Flow.code_910
  · exact Flow.code_914
  · exact Flow.code_957
  · exact Flow.code_958
  · exact Flow.code_959
  · exact Flow.code_1138
  · exact Flow.code_1139
  · exact Flow.code_1140
  · exact Flow.code_1203
  · exact Flow.code_1204
  · exact Flow.code_1205
  · exact Flow.code_1343
  · exact Flow.code_1344
  · exact Flow.code_1345
  · exact Flow.code_1427
  · exact Flow.code_1428
  · exact Flow.code_1429
  · exact Flow.code_1603
  · exact Flow.code_1604
  · exact Flow.code_1605
  · exact Flow.code_1608
  · exact Flow.code_1609
  · exact Flow.code_1610
  · exact Flow.code_1736
  · exact Flow.code_1737
  · exact Flow.code_1738
  · exact Flow.code_1863
  · exact Flow.code_1864
  · exact Flow.code_1865
  · exact Flow.code_1869
  · exact Flow.code_1870
  · exact Flow.code_1871
  · exact Flow.code_1874
  · exact Flow.code_1875
  · exact Flow.code_1876
  · exact Flow.code_1880
  · exact Flow.code_1881
  · exact Flow.code_1882
  · exact Flow.code_1885
  · exact Flow.code_1886
  · exact Flow.code_1887

private theorem loaderRingDefined {f : RingFact} (hf : f ∈ loaderRingFacts)
    {pc : Nat} (hPc : pc ∈ f.definitions) :
    ∃ op, (pc, op) ∈ loaderRingWritesAt ∧ op.output = f.value := by
  have hAll : loaderRingFacts.all (fun f => f.definitions.all (fun pc =>
      loaderRingWritesAt.any (fun (site, op) => decide (site = pc ∧ op.output = f.value)))) =
      true := by decide
  obtain ⟨⟨site, op⟩, hm, h⟩ := List.any_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp hAll f hf) pc hPc)
  obtain ⟨rfl, hout⟩ := of_decide_eq_true h
  exact ⟨op, hm, hout⟩

private theorem loaderRingRequired {l : Launch} {s : TState} {pc : Nat} {op : LoaderSlotOp}
    (hw : (pc, op) ∈ loaderRingWritesAt) (hPc : s.pc = pc)
    (hRegs : loaderRingRegisters l s) {value : RingValue} (hNeed : op.input = some value) :
    value.matches l s := by
  have hAll : loaderRingWritesAt.all (fun (pc, op) =>
      match op.input with
      | none => true
      | some value =>
        loaderRingFacts.any (fun f => decide (f.value = value ∧ f.active pc))) = true := by decide
  have hSpec := List.all_eq_true.mp hAll (pc, op) hw
  change (match op.input with
    | none => true
    | some v => loaderRingFacts.any (fun f => decide (f.value = v ∧ f.active pc))) = true at hSpec
  rw [hNeed] at hSpec
  obtain ⟨fact, hm, h⟩ := List.any_eq_true.mp hSpec
  obtain ⟨hEq, ha⟩ := of_decide_eq_true h
  exact hEq ▸ liveRingFact hRegs hPc fact hm ha

private theorem loaderRingDisplacement {pc r src off : Nat}
    (hw : (pc, LoaderSlotOp.displace r src off) ∈ loaderRingWritesAt) : off ≤ 56 := by
  have hAll : loaderRingWritesAt.all (fun (_, op) =>
      match op with | .displace _ _ off => off ≤ 56 | _ => true) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hAll _ hw)

private theorem loaderLiteralSlot {l : Launch} {g pc r : Nat} {s u : TState}
    (hPc : s.pc = pc) (hf : s.fault = none) (slot : Fin 3)
    (hc : kernel.code[pc]? = some ⟨none, (LoaderSlotOp.literal r slot).instruction⟩)
    (ht : Tau kernel [] l g s u) : u.regs r = some (b32 slot.val) := by
  let op := (LoaderSlotOp.literal r slot).instruction
  have hl : op.isLocal = true := rfl
  have hx : execLocalA [] l g s op = .ok (next (setReg s r (b32 slot.val))) := by
    change execLocal l g s (.move ⟨.scalar, .int .b 32, [some r], [.imm slot.val]⟩) = _
    rw [execLocal_move rfl]
    fin_cases slot <;> simp [execMove, readValue, readBits, DType.width,
      Value.bytes, b32, bind, Except.bind, pure, Except.pure] <;> rfl
  have hOut : out kernel [] l g s = .tau (next (setReg s r (b32 slot.val))) := by
    change kernel.code[pc]? = some ⟨none, op⟩ at hc
    simp only [out, hPc, hf, hc, guardHolds, hl, ↓reduceIte, pure, Except.pure, hx]
  obtain rfl := Out.tau.inj (ht.symm.trans hOut)
  exact Function.update_self _ _ _

private theorem loaderRingDefinedValue {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g pc : Nat} {s u : TState} {op : LoaderSlotOp}
    (hw : (pc, op) ∈ loaderRingWritesAt) (hPc : s.pc = pc) (hf : s.fault = none)
    (hb : s.regs 2535 = some (b32 l.sharedBase)) (hRegs : loaderRingRegisters l s)
    (ht : Tau kernel [] l g s u) : op.output.matches l u := by
  have hc := loaderRingWriteCode hw
  have need {v : RingValue} (hNeed : op.input = some v) : v.matches l s :=
    loaderRingRequired hw hPc hRegs hNeed
  cases op with
  | literal r slot => exact ⟨slot, loaderLiteralSlot hPc hf slot hc ht, trivial⟩
  | bump r src =>
    obtain ⟨n, hn, _⟩ := need (v := .slot src) rfl
    exact ⟨n, bumpSlot hPc hf hc n hn ht, trivial⟩
  | compare r q =>
    obtain ⟨n, hn, _⟩ := need (v := .bumped r) rfl
    have hNe : r ≠ q := by
      have hAll : loaderRingWritesAt.all (fun (_, op) =>
          match op with | .compare r q => r != q | _ => true) = true := by decide
      simpa using List.all_eq_true.mp hAll _ hw
    have hKeep := tau_core_regs (hPc.symm ▸ hc) ht
      (show r ∉ writesRegs (LoaderSlotOp.compare r q).instruction by
        simp [LoaderSlotOp.instruction, writesRegs, hNe])
    exact ⟨n, hKeep.trans hn, compareBump hPc hf hc n hn ht⟩
  | select r src q =>
    obtain ⟨n, hn, hPred⟩ := need (v := .compared src q) rfl
    obtain ⟨k, hk⟩ := selectSlot hPc hf hc n hn hPred ht
    exact ⟨k, hk, trivial⟩
  | scale r src =>
    obtain ⟨n, hn, _⟩ := need (v := .slot src) rfl
    exact ⟨n, bytesOfSlot hPc hf hc n hn ht, trivial⟩
  | base r src =>
    obtain ⟨n, hn, _⟩ := need (v := .byteOffset src) rfl
    have hBound : l.sharedBase + 8 * n.val < 2 ^ 32 := by
      have := n.isLt
      have := hp.shared.2.1
      omega
    refine ⟨n, ?_, trivial⟩
    simpa [LoaderSlotOp.output, RingValue.registers, RingValue.argument] using
      slotAddress hPc hf hc hb n hn hBound ht
  | displace r src off =>
    obtain ⟨n, hn, _⟩ := need (v := .address src 0) rfl
    have hBound : l.sharedBase + (8 * n.val + off) < 2 ^ 32 := by
      have := n.isLt
      have := hp.shared.2.1
      have := loaderRingDisplacement hw
      omega
    refine ⟨n, slotDisplacedAddress hPc hf hc n ?_ hBound ht, trivial⟩
    simpa [RingValue.registers, RingValue.argument] using hn

private def loaderRingLocalSource (pc : Nat) (i : Instr) (f : RingFact) : Bool :=
  if f.definitions.contains pc then i.guard.isNone && i.op.isLocal
  else !decide (f.active pc) ||
    f.value.registers.all (fun r => !(loaderRingWrites i.op).contains r)

private def loaderRingBranch (pc : Nat) (op : Op) (f : RingFact) : Bool :=
  match op with
  | .bra target _ => !decide (f.active target) || decide (f.active pc)
  | .brx .. => false
  | _ => true

private def loaderRingLocationCode (pc : Nat) (i : Instr) : Bool :=
  loaderRingFacts.all (fun f =>
    loaderRingLocalSource pc i f &&
    (!decide (f.active (pc + 1)) || f.definitions.contains pc || decide (f.active pc)) &&
    loaderRingBranch pc i.op f)

private theorem loaderRingLocationCodeAt {pc : Nat} {i : Instr}
    (hLo : 174 ≤ pc) (hHi : pc < 1901) (hc : kernel.code[pc]? = some i) :
    loaderRingLocationCode pc i = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hAll : code.all (fun (ins, site) => loaderRingLocationCode site ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, pc)
  apply List.mem_of_getElem? (i := pc - 174)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

/-- An actual loader step preserves the live ring operand frame. -/
theorem loaderRingStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {warp : Fin 2} {s u : TState} {e : Option Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hFrame : LoaderRingFrame l warp s) (hw : WStep kernel Assumptions.all l g s e u) :
    174 ≤ u.pc ∧ u.pc ≤ 1901 ∧ LoaderRingFrame l warp u := by
  have hCode (bound : Nat) : ((kernel.code.drop 174).take (1901 - 174)).all
      (fun i => loaderPipelineCutOp 174 1901 bound
        ((loaderRingRoots l warp).map Prod.fst) i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨hl, hh, hShape, hRoots⟩ := pipelineCutStep
    (by decide : 174 ≤ 174) (by decide : 1901 ≤ 1901) ⟨hLo, hHi⟩
    (hCode u.pc) hw hFrame.1 hFrame.2.1
  refine ⟨hl, hh.resolve_right (Nat.lt_irrefl _), hShape, hRoots, ?_⟩
  intro f hF hActive
  have decoded {i : Instr} (hc : kernel.code[s.pc]? = some i) :
      (loaderRingLocalSource s.pc i f &&
       (!decide (f.active (s.pc + 1)) || f.definitions.contains s.pc || decide (f.active s.pc)) &&
       loaderRingBranch s.pc i.op f) = true :=
    List.all_eq_true.mp (loaderRingLocationCodeAt hLo hHi hc) f hF
  have hPreserve (hNot : s.pc ∉ f.definitions) (hBefore : f.active s.pc) :
      f.value.matches l u := by
    apply RingValue.preserved (hFrame.2.2 f hF hBefore)
    intro r hr
    apply loaderPipelineStepRegs hLo hHi _ hw
    intro i hc
    have h := decoded hc
    simp only [Bool.and_eq_true, loaderRingLocalSource, List.contains_eq_mem, decide_eq_true_eq,
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
      rwa [← loaderOutCore (by omega) (by omega)]
    obtain ⟨i, hc, hf, _⟩ := tauScoreSource ht
    by_cases hDef : s.pc ∈ f.definitions
    · obtain ⟨op, hw, hout⟩ := loaderRingDefined hF hDef
      exact hout ▸ loaderRingDefinedValue hp hw rfl hf hFrame.2.1.1 hFrame.2.2 ht'
    apply hPreserve hDef
    rcases tau_core_frame hc ht' with rfl | hf
    · exact hFall hc hDef rfl
    have hNext := hf.pc
    have hB := decoded hc
    simp only [Bool.and_eq_true] at hB
    cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hNext
    case bra target uni =>
      rw [hNext] at hActive
      simpa [loaderRingBranch, ho, hActive] using hB.2
    case brx => simp [loaderRingBranch, ho] at hB
    all_goals exact hFall hc hDef hNext
  · obtain ⟨i, hc, hl, _⟩ := estep_event_source he
    have hNot : s.pc ∉ f.definitions := by
      intro hDef
      have h := decoded hc
      simp [loaderRingLocalSource, hl, hDef] at h
    apply hPreserve hNot
    have hE : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tm, hOut, hFire⟩ := he
      exact ⟨tm, by rwa [← loaderOutCore (by omega) (by omega)], hFire⟩
    rcases (estep_return_pc hE (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h ▸ hActive
    · exact hFall hc hNot h

private theorem loaderRingWalk {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {warp : Fin 2} {s : TState} {events : List Event} {visits : List Visit}
    (hWalk : Walk kernel Assumptions.all l g s events visits)
    (hLo : 174 ≤ s.pc) (hHi : s.pc ≤ 1901)
    (hFrame : LoaderRingFrame l warp s) {e : Event} (he : e ∈ events) (hEnd : e.pc < 1901) :
    ∃ t o, t.pc = e.pc ∧ LoaderRingFrame l warp t ∧ EStep kernel Assumptions.all l g t e o := by
  induction hWalk with
  | stop => cases he
  | @tau s u events visits ht hw ih =>
    by_cases hExit : s.pc = 1901
    · obtain ⟨_, _, hf, _⟩ := tauScoreSource ht
      have hAt := pipelineAtCut hExit hFrame.1 hFrame.2.1 hf
        ⟨_, Flow.code_1901, rfl⟩
      have hRet := loaderTailEventPcs warp hAt (.tau ht hw) e he
      omega
    obtain ⟨hl, hh, hF'⟩ := loaderRingStep hp hLo (by omega) hFrame (.inl ⟨rfl, ht⟩)
    exact ih hl hh hF' he
  | @ev s u ev events visits hs hw ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, _, (estep_source_pc hs).symm, hFrame, hs⟩
    · by_cases hExit : s.pc = 1901
      · have hf : s.fault = none := by
          obtain ⟨tm, hout, hFire⟩ := hs
          cases h : s.fault
          · rfl
          · simp only [out, h, Out.ev.injEq] at hout
            subst tm
            cases hFire.2
        have hAt := pipelineAtCut hExit hFrame.1 hFrame.2.1 hf ⟨_, Flow.code_1901, rfl⟩
        have hRet := loaderTailEventPcs warp hAt (.ev hs hw) e (List.mem_cons_of_mem _ he)
        omega
      obtain ⟨hl, hh, hF'⟩ := loaderRingStep hp hLo (by omega) hFrame (.inr ⟨_, rfl, hs⟩)
      exact ih hl hh hF' he
  | last hs =>
    obtain rfl := List.mem_singleton.mp he
    exact ⟨_, _, (estep_source_pc hs).symm, hFrame, hs⟩

/-- The initialized loader frame at common role dispatch. -/
theorem loaderRingFrameAtDispatch {l : Launch} {warp : Fin 2} {t : TState}
    (hAt : At t 174 (loaderRingRoots l warp)) : LoaderRingFrame l warp t := by
  refine ⟨ringShapeOfAt hAt, hAt.2.2.2.2, ?_⟩
  intro f hf ha
  have hDec : loaderRingFacts.all (fun f => !decide (f.active 174)) = true := by decide
  have hFalse : ¬ f.active 174 := by simpa using List.all_eq_true.mp hDec f hf
  exact (hFalse (hAt.1 ▸ ha)).elim

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem loaderRingSource {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 960 ≤ e.pc) (hHi : e.pc < 1901) :
    ∃ warp : Fin 2, ∃ t o, t.pc = e.pc ∧ LoaderRingFrame l warp t ∧
      EStep kernel Assumptions.all l g t e o := by
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hWarp : 14 ≤ warpIndex l g := by
    rcases roleBodyPcOfEvent hp hX he (by omega) hHint with h | h
    · omega
    · split_ifs at h <;> omega
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWord : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hWarp
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨pos, t, o, hIndex, ht, hr⟩ := commonDispatchOfLateEvent hp hX hg he (by omega)
  have hAt : At t 174 (loaderRingRoots l warp) :=
    ht.mono ⟨ht.2.2.2.2.2.1, hWord.symm ▸ ht.2.2.2.2.1, trivial⟩
  have hF := loaderRingFrameAtDispatch hAt
  obtain ⟨_, hWalk⟩ := walkFromRun hr
  have hm : e ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := index - pos)
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  obtain ⟨t, o, ht, hf, hStep⟩ := loaderRingWalk hp hWalk
    (by rw [hAt.1]) (by rw [hAt.1]; decide) hF hm hHi
  exact ⟨warp, t, o, ht, hf, hStep⟩

/-- Every indexed loader wait names the verified slot of its three-stage ring. -/
theorem loaderRingWaitAddress {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [960, 1206, 1430, 1611, 1866, 1877, 1888]) :
    ∃ off ∈ [56, 64, 72], target = ⟨.shared, g / l.block, l.sharedBase + off⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hLo : 960 ≤ pc := by omega
  have hHi : pc < 1901 := by omega
  obtain ⟨_, t, o, ht, hFrame, hStep⟩ := loaderRingSource hp hX he hLo hHi
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ht, Flow.code_960] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨k, hb, _⟩ := liveRingFact hFrame.2.2 ht
      ⟨.address 1976 56, 960, 962, [959]⟩ (by decide) (by decide)
    change t.regs 1976 = some (b32 (l.sharedBase + (8 * k.val + 56))) at hb
    refine ⟨_, ?_, pollResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · fin_cases k <;> decide
    · fin_cases k <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_1206] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨k, hb, _⟩ := liveRingFact hFrame.2.2 ht
      ⟨.address 2063 56, 1206, 1208, [1205]⟩ (by decide) (by decide)
    change t.regs 2063 = some (b32 (l.sharedBase + (8 * k.val + 56))) at hb
    refine ⟨_, ?_, pollResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · fin_cases k <;> decide
    · fin_cases k <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_1430] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨k, hb, _⟩ := liveRingFact hFrame.2.2 ht
      ⟨.address 2138 56, 1430, 1432, [1429]⟩ (by decide) (by decide)
    change t.regs 2138 = some (b32 (l.sharedBase + (8 * k.val + 56))) at hb
    refine ⟨_, ?_, pollResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · fin_cases k <;> decide
    · fin_cases k <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_1611] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨k, hb, _⟩ := liveRingFact hFrame.2.2 ht
      ⟨.address 2140 56, 1611, 1613, [1610]⟩ (by decide) (by decide)
    change t.regs 2140 = some (b32 (l.sharedBase + (8 * k.val + 56))) at hb
    refine ⟨_, ?_, pollResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · fin_cases k <;> decide
    · fin_cases k <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_1866] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨k, hb, _⟩ := liveRingFact hFrame.2.2 ht
      ⟨.address 2288 56, 1866, 1868, [1865]⟩ (by decide) (by decide)
    change t.regs 2288 = some (b32 (l.sharedBase + (8 * k.val + 56))) at hb
    refine ⟨_, ?_, pollResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · fin_cases k <;> decide
    · fin_cases k <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_1877] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨k, hb, _⟩ := liveRingFact hFrame.2.2 ht
      ⟨.address 2289 56, 1877, 1879, [1876]⟩ (by decide) (by decide)
    change t.regs 2289 = some (b32 (l.sharedBase + (8 * k.val + 56))) at hb
    refine ⟨_, ?_, pollResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · fin_cases k <;> decide
    · fin_cases k <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_1888] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨k, hb, _⟩ := liveRingFact hFrame.2.2 ht
      ⟨.address 2291 56, 1888, 1890, [1887]⟩ (by decide) (by decide)
    change t.regs 2291 = some (b32 (l.sharedBase + (8 * k.val + 56))) at hb
    refine ⟨_, ?_, pollResolvedMbarAddress hp hb ?_ hFire rfl⟩
    · fin_cases k <;> decide
    · fin_cases k <;> unfold initializedMbarOffset <;> decide

/-- Every indexed loader async names the verified slot of its three-stage ring. -/
theorem loaderRingAsyncAddress {g index pc : Nat} {target : Loc}
    (he : X.get (g, index) = some ⟨pc, .asyncArrive target true⟩)
    (hSite : pc ∈ [1137, 1342, 1602, 1735]) :
    ∃ off ∈ [32, 40, 48], target = ⟨.shared, g / l.block, l.sharedBase + off⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hLo : 960 ≤ pc := by omega
  have hHi : pc < 1901 := by omega
  obtain ⟨_, t, o, ht, hFrame, hStep⟩ := loaderRingSource hp hX he hLo hHi
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl | rfl | rfl
  · rw [ht, Flow.code_1137] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨k, hb, _⟩ := liveRingFact hFrame.2.2 ht
      ⟨.address 1122 0, 959, 1137, [958]⟩ (by decide) (by decide)
    change t.regs 1122 = some (b32 (l.sharedBase + (8 * k.val + 0))) at hb
    refine ⟨_, ?_, loaderAsyncArrivalResolvedAddress hp hb ?_ hFire rfl⟩
    · fin_cases k <;> decide
    · fin_cases k <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_1342] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨k, hb, _⟩ := liveRingFact hFrame.2.2 ht
      ⟨.address 1141 0, 1205, 1342, [1204]⟩ (by decide) (by decide)
    change t.regs 1141 = some (b32 (l.sharedBase + (8 * k.val + 0))) at hb
    refine ⟨_, ?_, loaderAsyncArrivalResolvedAddress hp hb ?_ hFire rfl⟩
    · fin_cases k <;> decide
    · fin_cases k <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_1602] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨k, hb, _⟩ := liveRingFact hFrame.2.2 ht
      ⟨.address 1151 0, 1429, 1602, [1428]⟩ (by decide) (by decide)
    change t.regs 1151 = some (b32 (l.sharedBase + (8 * k.val + 0))) at hb
    refine ⟨_, ?_, loaderAsyncArrivalResolvedAddress hp hb ?_ hFire rfl⟩
    · fin_cases k <;> decide
    · fin_cases k <;> unfold initializedMbarOffset <;> decide
  · rw [ht, Flow.code_1735] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨k, hb, _⟩ := liveRingFact hFrame.2.2 ht
      ⟨.address 1171 0, 1610, 1735, [1609]⟩ (by decide) (by decide)
    change t.regs 1171 = some (b32 (l.sharedBase + (8 * k.val + 0))) at hb
    refine ⟨_, ?_, loaderAsyncArrivalResolvedAddress hp hb ?_ hFire rfl⟩
    · fin_cases k <;> decide
    · fin_cases k <;> unfold initializedMbarOffset <;> decide

/-- Every loader poll, including the recurring and drain acquires, names an initialized object. -/
theorem loaderWaitInitObject {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893,
      960, 1206, 1430, 1611, 1866, 1877, 1888]) :
    ∃ i : Fin 34, target = initObject l (g / l.block) i := by
  change pc ∈ [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893] ++
    [960, 1206, 1430, 1611, 1866, 1877, 1888] at hSite
  rcases List.mem_append.mp hSite with hFixed | hRing
  · obtain ⟨off, hOff, rfl⟩ := loaderFixedWaitAddress hp hX he hFixed
    apply initObjectOfOffset
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    rcases hOff with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold initializedMbarOffset <;> decide
  · obtain ⟨off, hOff, rfl⟩ := loaderRingWaitAddress hp hX he hRing
    apply initObjectOfOffset
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    rcases hOff with rfl | rfl | rfl <;> unfold initializedMbarOffset <;> decide

/-- All actual nonincrementing loader copy arrivals name one of the three ready barriers. -/
theorem loaderAsyncAddress {g index pc : Nat} {target : Loc}
    (he : X.get (g, index) = some ⟨pc, .asyncArrive target true⟩)
    (hSite : pc ∈ [674, 904, 1137, 1342, 1602, 1735]) :
    ∃ off ∈ [32, 40, 48], target = ⟨.shared, g / l.block, l.sharedBase + off⟩ := by
  change pc ∈ [674, 904] ++ [1137, 1342, 1602, 1735] at hSite
  rcases List.mem_append.mp hSite with hFixed | hRing
  · obtain ⟨off, hOff, hAddr⟩ := loaderFixedAsyncAddress hp hX he hFixed
    exact ⟨off, List.mem_append_left [48] hOff, hAddr⟩
  · exact loaderRingAsyncAddress hp hX he hRing

/-- All six actual copy arrival sites address an initialized ready barrier in their CTA. -/
theorem loaderAsyncInitObject {g index pc : Nat} {target : Loc}
    (he : X.get (g, index) = some ⟨pc, .asyncArrive target true⟩)
    (hSite : pc ∈ [674, 904, 1137, 1342, 1602, 1735]) :
    ∃ i : Fin 34, target = initObject l (g / l.block) i := by
  obtain ⟨off, hOff, rfl⟩ := loaderAsyncAddress hp hX he hSite
  apply initObjectOfOffset
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
  rcases hOff with rfl | rfl | rfl <;> unfold initializedMbarOffset <;> decide

/-- The completion barrier of each actual loader TMA input is an initialized CTA object. -/
theorem loaderTensorInitObject {g index map : Nat} (site : Fin 14) {spec : TensorCopy.Spec}
    (he : X.get (g, index) = some ⟨(inputSite site).pc, .tensorIssue map spec⟩) :
    ∃ i : Fin 34, spec.mbar = initObject l (g / l.block) i := by
  obtain ⟨off, hOff, hAddr⟩ := loaderTensorAddress hp hX site he
  rw [hAddr]
  apply initObjectOfOffset
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
  rcases hOff with rfl | rfl | rfl | rfl <;> unfold initializedMbarOffset <;> decide

end
end PTX.Kernels.TmlFa4Fwd.Loader
