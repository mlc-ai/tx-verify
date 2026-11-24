-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterWindow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ActualSuffix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Lemmas.Isa.Rule

@[expose] public section

/-! # The softmax mask return follows its concrete ring address -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The same slot-value register is retained between its creation and the mask return. -/
private theorem slot_window : stableRegisterWindow 477 262 571 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem no_branch_to_return : kernel.branchTarget 571 = false := by
  decide +kernel

variable {t : TState}

/-- Recover the address of an audited arrival, including the final local address add. -/
theorem arrival_in_register_window {e : Event} {o : Option TState} {before tail : List Event}
    {r base off value lo hi : Nat} (hWindow : stableRegisterWindow r lo hi = true)
    (hAdd : kernel.code[hi - 1]? = some ⟨none,
      .int ⟨.add, .int .s 32, false, [some base], [.reg r, .imm (Int.ofNat off)]⟩⟩)
    (hArrive : kernel.code[hi]? = some
      ⟨none, .mbarArrive base 0 (.imm 0) (.imm 1) false true .cta none⟩)
    (hNoParam : hi - 1 ∉ paramAdds) (hNoPrefetch : hi - 1 ∉ prefetchTensorMapSites)
    (hNoShared : hi - 1 ∉ Assumptions.sharedBitsSites) (hBranch : kernel.branchTarget hi = false)
    (hFirst : lo ≤ t.pc) (hLast : t.pc < hi) (hr : t.regs r = some (b32 value))
    (hLimit : value + off < 2 ^ 32) (hAlign : (value + off) % 8 = 0) (hTag : e.pc = hi)
    (hPrev : ∀ f ∈ before, f.pc ≠ hi)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    e.kind = .arrive ⟨.shared, ctaOf L g, value + off⟩ 0 1 true .cta := by
  obtain ⟨v, u, out, hPc, hReg, hTau, m, hOut, hFire⟩ :=
    register_before_window_end hWindow hAdd rfl hBranch hFirst hLast hTag hPrev hRun
  have hFault : v.fault = none := by
    cases h : v.fault with
    | none => rfl
    | some f => simp [Tau, PTX.out, h] at hTau
  let add : IntInstr :=
    ⟨.add, .int .s 32, false, [some base], [.reg r, .imm (Int.ofNat off)]⟩
  have hRules := Thread.asms_localRule_int (L := L) (g := g) (t := v)
    (i := add) (hPc ▸ hNoParam) (hPc ▸ hNoPrefetch) (hPc ▸ hNoShared) rfl
  have hExec : execLocalA Assumptions.all L g v (.int add) =
      .ok (PTX.next (setReg v base (b32 (value + off)))) := by
    rw [execLocalA_noSegment (Proof.asms_segment_free v), execLocalRule_of_none hRules,
      execLocal_int rfl]
    simp only [add, execInt, DType.width, readValue, readBits, readReg, hReg, hr, b32,
      bind, Except.bind, pure, Except.pure]
    have hCast : BitVec.ofInt 64 (Int.ofNat off) = BitVec.ofNat 64 off := rfl
    rw [hCast, Wg2.trunc32_add_word (by omega) hLimit]
  have hNext := out_tau (K := kernel) hFault (hPc ▸ hAdd) rfl rfl hExec
  unfold Tau at hTau
  rw [hNext] at hTau
  obtain rfl := Out.tau.inj hTau
  have hPc' : (PTX.next (setReg v base (b32 (value + off)))).pc = hi := by
    change v.pc + 1 = hi
    omega
  have hFault' : (PTX.next (setReg v base (b32 (value + off)))).fault = none := hFault
  rw [out_event hFault' (hPc' ▸ hArrive) rfl rfl] at hOut
  cases hOut
  have hAddr : (PTX.next (setReg v base (b32 (value + off)))).regs base =
      some (b32 (value + off)) := by simp [PTX.next, setReg]
  have hm := mbarLoc_b32 (L := L) (g := g) hAddr hLimit hAlign
  exact RingEvents.fired_unit_arrive hm hFire

/-- The first actual softmax mask return in this block releases its selected slot,
independently of the bytes read between the mask acquire and the release. -/
theorem softmax_return_in_register_window {e : Event} {o : Option TState} {before tail : List Event}
    (hpre : Pre P L mem0) (slot : Fin 4) (hFirst : 262 ≤ t.pc) (hLast : t.pc < 571)
    (hr : t.regs 477 = some (b32 (L.sharedBase + 8 * slot.val)))
    (hTag : e.pc = Wg0.Site.validFree.pc) (hPrev : ∀ f ∈ before, f.pc ≠ Wg0.Site.validFree.pc)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    e.kind = .arrive ⟨.shared, ctaOf L g, L.sharedBase + (222872 + 8 * slot.val)⟩
      0 1 true .cta := by
  have hSlot := slot.isLt
  have hBase := sharedBase_lt hpre
  have hOffset : L.sharedBase + 8 * slot.val + 222872 =
      L.sharedBase + (222872 + 8 * slot.val) := by omega
  rw [← hOffset]
  exact arrival_in_register_window slot_window Flow.code_570 Flow.code_571
    (by decide) (by decide) (by decide) no_branch_to_return hFirst hLast hr (by omega)
    (by rw [hOffset]; exact Wg0.ringAddr_mod8 hpre (off := 222872) (by decide)) hTag hPrev hRun

/-- A block's probability publication cannot be reached without its mask release. -/
theorem mask_return_before_probability_publication {pub : Event} {before tail : List Event}
    {o : Option TState} (hHead : t.pc = 264) (hTag : pub.pc = Wg0.Site.soReady.pc)
    (hRun : Run kernel Assumptions.all L g t (before ++ pub :: tail) o) :
    ∃ ret ∈ before, ret.pc = Wg0.Site.validFree.pc := by
  by_contra! hNo
  obtain ⟨v, r, _, hLo, hHi, _, hLocal, hFired⟩ :=
    register_at_event_in_window slot_window Flow.code_570 rfl
      (by rw [hHead]; decide) (by rw [hHead]; decide) hNo hRun
  have hBounds := local_path_in_register_window slot_window ⟨hLo, hHi.le⟩ hLocal
  have hPc := estep_source_pc hFired
  rw [hTag] at hPc
  change 1122 = r.pc at hPc
  have hUpper : r.pc ≤ 571 := hBounds.2
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
