-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantPollControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxMaskControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterRegion

@[expose] public section

/-! # The dequantizer's actual back edge and epilogue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private def tailTarget (pc : Nat) : Prop := pc = 2667 ∨ 3605 ≤ pc
private instance (pc : Nat) : Decidable (tailTarget pc) :=
  inferInstanceAs (Decidable (pc = 2667 ∨ 3605 ≤ pc))

private def tailRegs : List Nat := [513, 457, 2988]

set_option maxRecDepth 100000 in
private theorem tail_audit : kernel.code.zipIdx.all (fun (ins, pc) =>
    !decide (3605 ≤ pc) || (closesControlRegion tailTarget pc ins &&
      tailRegs.all fun r => decide (r ∉ writesRegs ins.op))) = true := by decide +kernel

private theorem tail_step {t u : TState} (ht : 3605 ≤ t.pc)
    (hStep : Tau kernel Assumptions.all L g t u) :
    tailTarget u.pc ∧ u.fault = none ∧ ∀ r ∈ tailRegs, u.regs r = t.regs r := by
  have hFault := tau_fault_free hStep
  unfold Tau out at hStep
  split at hStep
  · cases hStep
  split at hStep
  · cases hStep
  rename_i ins hc
  have ha := List.all_eq_true.mp tail_audit (ins, t.pc) (List.mem_zipIdx_iff_getElem?.mpr hc)
  simp only [ht, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at ha
  split at hStep
  · cases hStep
  · rename_i hGuard
    cases hStep
    refine ⟨control_fallthrough ha.1 ?_, hFault, fun _ _ => rfl⟩
    cases hg : ins.guard
    · rw [hg] at hGuard
      change Except.ok true = Except.ok false at hGuard
      cases hGuard
    · rfl
  split at hStep
  · split at hStep
    · rename_i v hv
      cases hStep
      have hf := local_frame hv
      exact ⟨control_local_step rfl ha.1 hf, hf.fault.trans hFault, fun r hr =>
        hf.regs r (of_decide_eq_true (List.all_eq_true.mp ha.2 r hr))⟩
    · cases hStep
  · cases hStep

private theorem tail_path {t u : TState} (ht : 3605 ≤ t.pc)
    (hPath : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u) :
    (∃ v, v.pc = 2667 ∧ (∀ r ∈ tailRegs, v.regs r = t.regs r) ∧
      v.fault = none ∧ Relation.ReflTransGen (Tau kernel Assumptions.all L g) t v) ∨
      (3605 ≤ u.pc ∧ ∀ r ∈ tailRegs, u.regs r = t.regs r) := by
  induction hPath with
  | refl => exact .inr ⟨ht, fun _ _ => rfl⟩
  | @tail v w hBefore hStep ih =>
    rcases ih with h | ⟨hv, hRegs⟩
    · exact .inl h
    · obtain ⟨hp, hFault, hKeep⟩ := tail_step hv hStep
      have hReg (r : Nat) (hr : r ∈ tailRegs) := (hKeep r hr).trans (hRegs r hr)
      rcases hp with hp | hp
      · exact .inl ⟨w, hp, hReg, hFault, hBefore.tail hStep⟩
      · exact .inr ⟨hp, hReg⟩

private def epilogue (pc : Nat) : Prop := 3610 ≤ pc
private instance (pc : Nat) : Decidable (epilogue pc) := inferInstanceAs (Decidable (3610 ≤ pc))

set_option maxRecDepth 100000 in
private theorem epilogue_closed : controlRegionClosed epilogue = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem bookkeeping_local : kernel.code.zipIdx.all (fun (ins, pc) =>
    !decide (3605 ≤ pc ∧ pc < 3610) || ins.op.isLocal) = true := by decide +kernel

private theorem returning_tail_is_epilogue {t u : TState} {e : Event} (ht : 3605 ≤ t.pc)
    (he : EStep kernel Assumptions.all L g t e (some u)) : epilogue t.pc := by
  obtain ⟨ins, hc, hl, _⟩ := estep_event_source he
  by_contra! hn
  have hLt : t.pc < 3610 := Nat.lt_of_not_ge hn
  have h := List.all_eq_true.mp bookkeeping_local (ins, t.pc)
    (List.mem_zipIdx_iff_getElem?.mpr hc)
  simp [ht, hLt, hl] at h

/-- After advancing its slot and phase, a continuing trace either begins the next raw poll
or has only epilogue events. -/
theorem dequant_route_after_advance {t : TState} {block : Nat} {e : Event}
    {tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hAt : AtVector t 3605 (dequantHeadFacts L g block) t.sub t.acc)
    (hRun : Run kernel Assumptions.all L g t (e :: tail) o) :
    (∃ u, AtVector u 2677 (dequantPollFacts L g block) u.sub u.acc ∧
      Run kernel Assumptions.all L g u (e :: tail) o) ∨
      (∀ f ∈ e :: tail, 3605 ≤ f.pc) := by
  have ht : 3605 ≤ t.pc := hAt.1.symm ▸ le_rfl
  have restart (v : TState)
      (hPc : v.pc = 2667) (hKeep : ∀ r ∈ tailRegs, v.regs r = t.regs r)
      (hFault : v.fault = none)
      (hPrefix : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t v) :
      ∃ u, AtVector u 2677 (dequantPollFacts L g block) u.sub u.acc ∧
        Run kernel Assumptions.all L g u (e :: tail) o := by
    have hv : AtVector v 2667 (dequantHeadFacts L g block) v.sub v.acc := by
      refine ⟨hPc, rfl, rfl, hFault, ?_⟩
      have hStart := hAt.2.2.2.2
      exact ⟨(hKeep 513 (by decide)).trans hStart.1, (hKeep 457 (by decide)).trans hStart.2.1,
        (hKeep 2988 (by decide)).trans hStart.2.2.1, trivial⟩
    obtain ⟨u, hu, hPoll⟩ := dequant_loop_poll_setup hpre hv
    exact ⟨u, ⟨hPoll.1, rfl, rfl, hPoll.2.2.2.1, hPoll.2.2.2.2⟩,
      after_softmax_local_prefix (hPrefix.trans (run_rtg hu)) hRun⟩
  have close {v u : TState} (hv : 3605 ≤ v.pc)
      (he : EStep kernel Assumptions.all L g v e (some u))
      (hr : Run kernel Assumptions.all L g u tail o) : ∀ f ∈ e :: tail, 3605 ≤ f.pc := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · rwa [estep_source_pc he]
    · have hepi := control_region_event epilogue_closed (returning_tail_is_epilogue hv he) he
      have hBound := run_in_control_region epilogue_closed hepi hr f hf
      change 3610 ≤ f.pc at hBound
      omega
  cases hRun with
  | step hTau he hr =>
    rcases tail_path ht hTau with ⟨v, hp, hRegs, hf, hPrefix⟩ | ⟨hv, _⟩
    · exact .inl (restart v hp hRegs hf hPrefix)
    · exact .inr (close hv he hr)
  | last hTau he =>
    rcases tail_path ht hTau with ⟨v, hp, hRegs, hf, hPrefix⟩ | ⟨hv, _⟩
    · exact .inl (restart v hp hRegs hf hPrefix)
    · right
      intro f hm
      obtain rfl := List.mem_singleton.mp hm
      rwa [estep_source_pc he]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
