-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxMaskControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterRegion
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ActualSuffix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxTmemStore
import Lemmas.Flow.WaitTmpl

@[expose] public section

/-! # The final PV wait in a concrete softmax epilogue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private def epilogue (pc : Nat) : Prop := 1147 ≤ pc
private instance (pc : Nat) : Decidable (epilogue pc) :=
  inferInstanceAs (Decidable (1147 ≤ pc))

private def pvRegion (first last pc : Nat) : Bool := decide (first ≤ pc ∧ pc ≤ last)

set_option maxRecDepth 100000 in
private theorem epilogue_closed : controlRegionClosed epilogue = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem slot_audit :
    registerRegionChecked 2953 (pvRegion 1147 1179) [207, 1146] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem shift_audit : registerRegionChecked 1738 (pvRegion 1180 1181) [1179] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem base_audit : registerRegionChecked 1739 (pvRegion 1181 1181) [1180] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem sum_audit : registerRegionChecked 1740 (pvRegion 1182 1182) [1181] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem addr_audit : registerRegionChecked 1736 (pvRegion 1183 1186) [1182] = true := by
  decide +kernel

private def PvWaitState (L : Launch) (slot : Nat) (t : TState) : Prop :=
  epilogue t.pc ∧
  (pvRegion 1147 1179 t.pc = true → t.regs 2953 = some (b32 slot)) ∧
  (pvRegion 1180 1181 t.pc = true → t.regs 1738 = some (b32 (8 * slot))) ∧
  (pvRegion 1181 1181 t.pc = true → t.regs 1739 = some (b32 L.sharedBase)) ∧
  (pvRegion 1182 1182 t.pc = true → t.regs 1740 = some (b32 (L.sharedBase + 8 * slot))) ∧
  (pvRegion 1183 1186 t.pc = true →
    t.regs 1736 = some (b32 (L.sharedBase + (222936 + 8 * slot))))

private theorem pv_wait_tau {slot : Nat} {t u : TState}
    (hpre : Pre P L mem0) (hSlot : slot < 2) (hOld : PvWaitState L slot t)
    (hTau : Tau kernel Assumptions.all L g t u) : PvWaitState L slot u := by
  have hBase := sharedBase_lt hpre
  have hFault := tau_fault_free hTau
  refine ⟨control_region_tau epilogue_closed hOld.1 hTau,
    register_region_tau (property := (· = some (b32 slot)))
      slot_audit hOld.2.1 ?_ hTau,
    register_region_tau (property := (· = some (b32 (8 * slot))))
      shift_audit hOld.2.2.1 ?_ hTau,
    register_region_tau (property := (· = some (b32 L.sharedBase)))
      base_audit hOld.2.2.2.1 ?_ hTau,
    register_region_tau (property := (· = some (b32 (L.sharedBase + 8 * slot))))
      sum_audit hOld.2.2.2.2.1 ?_ hTau,
    register_region_tau (property := (· = some (b32 (L.sharedBase + (222936 + 8 * slot)))))
      addr_audit hOld.2.2.2.2.2 ?_ hTau⟩
  · intro hUpdate _
    have hLower : 1147 ≤ t.pc := hOld.1
    have : t.pc = 207 ∨ t.pc = 1146 := by simpa using hUpdate
    omega
  · intro hUpdate _
    have hPc := List.mem_singleton.mp hUpdate
    have hReg := hOld.2.1 (by rw [hPc]; decide)
    have hAt : AtVector t 1179 [(2953, b32 slot)] t.sub t.acc :=
      ⟨hPc, rfl, rfl, hFault, hReg, trivial⟩
    obtain ⟨v, hRun, hv⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 1180 [(1738, b32 (8 * slot))] t.sub t.acc := by
      seg_fp hAt using norm_bits [b32]
    exact (one_step_matches hTau hRun) ▸ hv.2.2.2.2.1
  · intro hUpdate _
    have hPc := List.mem_singleton.mp hUpdate
    have hAt : AtVector t 1180 [] t.sub t.acc := ⟨hPc, rfl, rfl, hFault, trivial⟩
    obtain ⟨v, hRun, hv⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 1181 [(1739, b32 L.sharedBase)] t.sub t.acc := by
      seg_fp hAt using norm_bits [b32]
    exact (one_step_matches hTau hRun) ▸ hv.2.2.2.2.1
  · intro hUpdate _
    have hPc := List.mem_singleton.mp hUpdate
    have hShift := hOld.2.2.1 (by rw [hPc]; decide)
    have hReg := hOld.2.2.2.1 (by rw [hPc]; decide)
    have hAt : AtVector t 1181 [(1739, b32 L.sharedBase), (1738, b32 (8 * slot))] t.sub t.acc :=
      ⟨hPc, rfl, rfl, hFault, hReg, hShift, trivial⟩
    obtain ⟨v, hRun, hv⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 1182 [(1740, b32 (L.sharedBase + 8 * slot))] t.sub t.acc := by
      seg_fp hAt using norm_bits [b32]
    exact (one_step_matches hTau hRun) ▸ hv.2.2.2.2.1
  · intro hUpdate _
    have hPc := List.mem_singleton.mp hUpdate
    have hReg := hOld.2.2.2.2.1 (by rw [hPc]; decide)
    have hAt : AtVector t 1182 [(1740, b32 (L.sharedBase + 8 * slot))] t.sub t.acc :=
      ⟨hPc, rfl, rfl, hFault, hReg, trivial⟩
    obtain ⟨v, hRun, hv⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 1183 [(1736, b32 (L.sharedBase + (222936 + 8 * slot)))] t.sub t.acc := by
      seg_fp hAt using norm_bits [b32, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    exact (one_step_matches hTau hRun) ▸ hv.2.2.2.2.1

set_option maxRecDepth 100000 in
private theorem pv_wait_event {slot : Nat} {t u : TState} {e : Event}
    (hOld : PvWaitState L slot t) (he : EStep kernel Assumptions.all L g t e (some u)) :
    PvWaitState L slot u :=
  ⟨control_region_event epilogue_closed hOld.1 he,
    register_region_event (property := (· = some (b32 slot)))
      slot_audit (register_updates_local (by decide +kernel)) hOld.2.1 he,
    register_region_event (property := (· = some (b32 (8 * slot))))
      shift_audit (register_updates_local (by decide +kernel)) hOld.2.2.1 he,
    register_region_event (property := (· = some (b32 L.sharedBase)))
      base_audit (register_updates_local (by decide +kernel)) hOld.2.2.2.1 he,
    register_region_event (property := (· = some (b32 (L.sharedBase + 8 * slot))))
      sum_audit (register_updates_local (by decide +kernel)) hOld.2.2.2.2.1 he,
    register_region_event (property := (· = some (b32 (L.sharedBase + (222936 + 8 * slot)))))
      addr_audit (register_updates_local (by decide +kernel)) hOld.2.2.2.2.2 he⟩

private def PvParityState (phase : Nat) (t : TState) : Prop :=
  (pvRegion 1147 1148 t.pc = true →
    t.regs 452 = some (.bits 16 (BitVec.ofNat 64 phase))) ∧
  (pvRegion 1149 1149 t.pc = true → t.regs 1724 = some (b32 phase)) ∧
  (pvRegion 1150 1186 t.pc = true → t.regs 2954 = some (b32 phase))

set_option maxRecDepth 100000 in
private theorem phase_input_audit :
    registerRegionChecked 452 (pvRegion 1147 1148) [1146] = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem phase_cast_audit :
    registerRegionChecked 1724 (pvRegion 1149 1149) [1148] = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem phase_audit :
    registerRegionChecked 2954 (pvRegion 1150 1186) [207, 1149] = true := by decide +kernel

private theorem pv_parity_tau {phase : Nat} {t u : TState}
    (hPhase : phase < 2) (hIn : epilogue t.pc) (hOld : PvParityState phase t)
    (hTau : Tau kernel Assumptions.all L g t u) : PvParityState phase u := by
  have hFault := tau_fault_free hTau
  refine ⟨register_region_tau (property := (· = some (.bits 16 (BitVec.ofNat 64 phase))))
      phase_input_audit hOld.1 ?_ hTau,
    register_region_tau (property := (· = some (b32 phase))) phase_cast_audit hOld.2.1 ?_ hTau,
    register_region_tau (property := (· = some (b32 phase))) phase_audit hOld.2.2 ?_ hTau⟩
  · intro hUpdate _
    have hPc := List.mem_singleton.mp hUpdate
    change 1147 ≤ t.pc at hIn
    omega
  · intro hUpdate _
    have hp := List.mem_singleton.mp hUpdate
    have hAt : AtVector t 1148 [(452, .bits 16 (BitVec.ofNat 64 phase))] t.sub t.acc :=
      ⟨hp, rfl, rfl, hFault, hOld.1 (by rw [hp]; decide), trivial⟩
    obtain ⟨v, hr, hv⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 1149 [(1724, b32 phase)] t.sub t.acc := by
      seg_fp hAt using norm_bits [b32]
    exact (one_step_matches hTau hr) ▸ hv.2.2.2.2.1
  · intro hUpdate _
    have hp : t.pc = 1149 := by
      change 1147 ≤ t.pc at hIn
      have : t.pc = 207 ∨ t.pc = 1149 := by simpa using hUpdate
      omega
    have hAt : AtVector t 1149 [(1724, b32 phase)] t.sub t.acc :=
      ⟨hp, rfl, rfl, hFault, hOld.2.1 (by rw [hp]; decide), trivial⟩
    obtain ⟨v, hr, hv⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 1150 [(2954, b32 phase)] t.sub t.acc := by
      seg_fp hAt using norm_bits [b32, Wg0.land255]
    exact (one_step_matches hTau hr) ▸ hv.2.2.2.2.1

set_option maxRecDepth 100000 in
private theorem pv_parity_event {phase : Nat} {t u : TState} {e : Event}
    (hOld : PvParityState phase t) (he : EStep kernel Assumptions.all L g t e (some u)) :
    PvParityState phase u :=
  ⟨register_region_event (property := (· = some (.bits 16 (BitVec.ofNat 64 phase))))
      phase_input_audit (register_updates_local (by decide +kernel)) hOld.1 he,
    register_region_event (property := (· = some (b32 phase)))
      phase_cast_audit (register_updates_local (by decide +kernel)) hOld.2.1 he,
    register_region_event (property := (· = some (b32 phase)))
      phase_audit (register_updates_local (by decide +kernel)) hOld.2.2 he⟩

/-- Every actual PV wait in the epilogue names the last block's slot, including retries. -/
theorem pv_wait_shape_in_epilogue {t : TState} {slot phase : Nat} {events : List Event}
    {e : Event} {o : Option TState} {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hpre : Pre P L mem0) (hSlot : slot < 2)
    (hPc : t.pc = 1147) (hReg : t.regs 2953 = some (b32 slot)) (hPhase : phase < 2)
    (hPhaseInput : t.regs 452 = some (.bits 16 (BitVec.ofNat 64 phase)))
    (hRun : Run kernel Assumptions.all L g t events o) (he : e ∈ events)
    (hTag : e.pc = 1184) (hk : e.kind = .wait m p ok acq sc) :
    m = ⟨.shared, ctaOf L g, L.sharedBase + (222936 + 8 * slot)⟩ ∧ p = phase ∧ acq = true := by
  have hStart : PvWaitState L slot t := by
    refine ⟨by rw [hPc]; exact Nat.le_refl _, fun _ => hReg, ?_, ?_, ?_, ?_⟩
    all_goals rw [hPc]; nofun
  have hPhaseStart : PvParityState phase t := by
    refine ⟨fun _ => hPhaseInput, ?_, ?_⟩
    all_goals rw [hPc]; nofun
  obtain ⟨v, result, ⟨hState, hParity⟩, hStep⟩ := actual_event_invariant
    (valid := fun u => PvWaitState L slot u ∧ PvParityState phase u)
    (fun h hs => ⟨pv_wait_tau hpre hSlot h.1 hs, pv_parity_tau hPhase h.1.1 h.2 hs⟩)
    (fun h hs => ⟨pv_wait_event h.1 hs, pv_parity_event h.2 hs⟩)
    ⟨hStart, hPhaseStart⟩ hRun he
  have hv : v.pc = 1184 := (estep_source_pc hStep).symm.trans hTag
  have hAddr := hState.2.2.2.2.2 (by rw [hv]; decide)
  have hm := mbarLoc_b32 (L := L) (g := g) (t := v) (base := 1736)
    hAddr (Wg0.ringAddr_lt hpre (buf := slot) (by omega))
    (Wg0.ringAddr_mod8 hpre (off := 222936) (by decide))
  cases result with
  | none =>
    obtain ⟨_, _, hf⟩ := hStep
    have hEnd := fires_none_ends hf
    simp [Ends, hk] at hEnd
  | some u =>
    obtain ⟨ins, hc, _, hf⟩ := estep_event_source hStep
    rw [hv, Flow.code_1184] at hc
    obtain rfl := Option.some.inj hc
    have hBits := readBits_b32 (L := L) (g := g)
      (hParity.2.2 (by rw [hv]; decide)) (by omega : phase < 2 ^ 32)
    obtain ⟨scope, hTemplate⟩ := eventTmpl_mbarWait_next (A := Assumptions.all) hm hBits
    rw [hTemplate] at hf
    obtain ⟨_, hEvent, _⟩ := fires_wait_next hf
    obtain ⟨hLoc, hPhaseEq, _, hAcq, _⟩ :=
      Kind.wait.inj (hk.symm.trans (congrArg Event.kind hEvent))
    exact ⟨hLoc, by simpa [Nat.mod_eq_of_lt hPhase, show phase < 2 ^ 64 by omega] using hPhaseEq,
      hAcq⟩

set_option maxRecDepth 100000 in
private theorem before_epilogue_window : stableRegisterWindow 2953 264 1122 = true := by
  decide +kernel

/-- The last block's PV slot is recovered directly from an actual softmax loop trace. -/
theorem pv_wait_shape_in_trace {t : TState} {block total : Nat} {e : Event}
    {before tail : List Event} {o : Option TState}
    {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hpre : Pre P L mem0) (hBlock : block < total) (hLimit : total < 2 ^ 31)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hTag : e.pc = 1184) (hk : e.kind = .wait m p ok acq sc)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    m = ⟨.shared, ctaOf L g, L.sharedBase + (222936 + 8 * ((total - 1) % 2))⟩ ∧
      p = (total - 1) / 2 % 2 ∧ acq = true := by
  let seen := before.takeWhile (!isProbabilityPublication ·)
  let later := before.dropWhile (!isProbabilityPublication ·)
  have hSplit : before = seen ++ later := List.takeWhile_append_dropWhile.symm
  have hPrefix : ∀ f ∈ seen, f.pc ≠ 1122 := by
    intro f hf
    have h := List.all_eq_true.mp List.all_takeWhile f hf
    exact (show f.pc ≠ Wg0.Site.soReady.pc by
      simpa [isProbabilityPublication, Bool.not_eq_true'] using h)
  cases hLater : later with
  | nil =>
    have hBefore : before = seen := by simpa only [hLater, List.append_nil] using hSplit
    obtain ⟨v, _, _, hFirst, hLast, _, hLocal, hFire⟩ :=
      register_at_event_in_window before_epilogue_window Flow.code_1121 rfl hAt.1.ge
        (hAt.1 ▸ by decide) (fun f hf => hPrefix f (hBefore ▸ hf)) hRun
    have hRegion := local_path_in_register_window before_epilogue_window ⟨hFirst, hLast.le⟩ hLocal
    rw [← estep_source_pc hFire, hTag] at hRegion
    exact ((by decide : ¬ inRegisterWindow 264 1122 1184) hRegion).elim
  | cons pub remaining =>
    have hHead := List.head?_dropWhile_not (!isProbabilityPublication ·) before
    change before.dropWhile (!isProbabilityPublication ·) = pub :: remaining at hLater
    rw [hLater] at hHead
    have hPub : pub.pc = Wg0.Site.soReady.pc := by simpa [isProbabilityPublication] using hHead
    change before = seen ++ before.dropWhile (!isProbabilityPublication ·) at hSplit
    rw [hLater] at hSplit
    have hTrace : before ++ e :: tail = seen ++ pub :: (remaining ++ e :: tail) := by
      rw [hSplit, List.append_assoc, List.cons_append]
    rw [hTrace] at hRun
    have hFacts : Holds t.regs (softmaxLoopFacts block total) := hAt.2.2.2.2.2.2.2.2
    obtain ⟨u, hu, hRegs, hPubRun⟩ := softmax_loop_facts_at_publication
      (by rw [hAt.1]; decide) (by rw [hAt.1]; decide) hFacts hPub hPrefix hRun
    by_cases hMore : block + 1 < total
    · have hNonempty : remaining ≠ [] := by
        intro hNil
        rw [hNil] at hPubRun
        obtain ⟨v, hLocal, hv, hRun'⟩ :=
          softmax_next_head_after_publication hMore hLimit hu hRegs hPubRun (by simp)
        have hFirst := softmax_opening_event_bound hv.1 (after_softmax_local_prefix hLocal hRun')
        rw [hTag] at hFirst
        omega
      obtain ⟨opening, rest, rfl⟩ := List.exists_cons_of_ne_nil hNonempty
      obtain ⟨poll, after, hEq⟩ := List.exists_cons_of_ne_nil
        (show rest ++ e :: tail ≠ [] by simp)
      rw [List.cons_append, hEq] at hPubRun
      obtain ⟨v, hv, hRest⟩ :=
        softmax_next_mask_after_publication hpre hMore hLimit hu hRegs hPubRun
      rw [← hEq] at hRest
      exact pv_wait_shape_in_trace hpre hMore hLimit hv hTag hk hRest
    · have hFinal : total = block + 1 := by omega
      subst total
      have hm : e ∈ remaining ++ e :: tail := List.mem_append_right _ List.mem_cons_self
      have hNonempty := List.ne_nil_of_mem hm
      obtain ⟨v, hLocal, hv, hSlot, hPhase, hReal⟩ :=
        softmax_final_slot_after_publication hLimit hu hRegs hPubRun hNonempty
      obtain ⟨front, after, hEq⟩ := List.exists_cons_of_ne_nil hNonempty
      rw [hEq] at hm hReal
      simpa only [Nat.add_sub_cancel] using
        pv_wait_shape_in_epilogue hpre (Nat.mod_lt _ (by decide)) hv hSlot
          (Nat.mod_lt _ (by decide)) hPhase
          (after_softmax_local_prefix hLocal hReal) hm hTag hk
termination_by before.length
decreasing_by
  simp only [hSplit, List.length_append, List.length_cons]
  omega

set_option maxRecDepth 100000 in
private theorem before_pv_window : stableRegisterWindow 2991 253 1184 = true := by
  decide +kernel

private theorem pv_poll_return {t : TState} {f nextEvent : Event} {rest : List Event}
    {o : Option TState} (hp : t.pc = 1184)
    (hRun : Run kernel Assumptions.all L g t (f :: nextEvent :: rest) o) :
    ∃ m p ok scope,
      f = ⟨1184, .wait m p ok true scope⟩ ∧ t.fault = none ∧
      Run kernel Assumptions.all L g (PTX.next (setReg t 4077 (.pred ok))) (nextEvent :: rest) o :=
  by
    have hStops : Stops kernel Assumptions.all L g t := by
      cases hf : t.fault with
      | none =>
        refine ⟨eventTmpl Assumptions.all L g t
          (.mbarWait 4077 1736 0 (.reg 2954) true .cta), ?_⟩
        simp [out, hf, hp, Flow.code_1184, guardHolds, Op.isLocal, pure, Except.pure]
      | some fault => exact ⟨.ub fault, by simp [out, hf]⟩
    generalize hList : f :: nextEvent :: rest = events at hRun
    cases hRun with
    | nil => cases hList
    | last => simp at hList
    | step hTau hStep hTail =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hList
      rw [stop_unique hTau .refl (stops_of_estep hStep) hStops] at hStep
      have hFault : t.fault = none := by
        obtain ⟨tmpl, ho, hf⟩ := hStep
        cases hErr : t.fault with
        | none => rfl
        | some fault =>
          simp only [out, hErr, Out.ev.injEq] at ho
          subst tmpl
          simp [Fires] at hf
      obtain ⟨ins, hc, _, hf⟩ := estep_event_source hStep
      rw [hp, Flow.code_1184] at hc
      obtain rfl := Option.some.inj hc
      cases hm : mbarLoc L g t 1736 0 with
      | error fault =>
        simp [eventTmpl, tmaTmpl, hm, bind, Except.bind, ofExec, widenMbarScope, Fires] at hf
      | ok m =>
        cases hq : readBits L g t 32 (.reg 2954) with
        | error fault =>
          simp [eventTmpl, tmaTmpl, hm, hq, bind, Except.bind, ofExec, widenMbarScope, Fires] at hf
        | ok q =>
          obtain ⟨scope, hTemplate⟩ := eventTmpl_mbarWait_next (A := Assumptions.all) hm hq
          rw [hTemplate] at hf
          obtain ⟨ok, he, hu⟩ := fires_wait_next hf
          rw [hp] at he
          exact ⟨m, q.toNat % 2, ok, scope, he, hFault, hu ▸ hTail⟩

set_option maxRecDepth 4096 in
private theorem pv_acquire_before_tail {t : TState} {before tail : List Event}
    {e : Event} {o : Option TState}
    (hStart : inRegisterWindow 253 1184 t.pc)
    (hLater : 1184 < e.pc) (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    ∃ j < before.length, ∃ m p sc, before[j]? = some ⟨1184, .wait m p true true sc⟩ := by
  let earlier := before.takeWhile (fun f => f.pc != 1184)
  let rest := before.dropWhile (fun f => f.pc != 1184)
  have hSplit : before = earlier ++ rest := List.takeWhile_append_dropWhile.symm
  have hPrefix : ∀ f ∈ earlier, f.pc ≠ 1184 := by
    intro f hf
    have h := List.all_eq_true.mp List.all_takeWhile f hf
    exact (show f.pc ≠ 1184 by simpa using h)
  cases hRest : rest with
  | nil =>
    have hSame : before = earlier := by simpa only [hRest, List.append_nil] using hSplit
    rw [hSame] at hRun
    exact (Nat.not_le_of_lt hLater (event_before_window_exit before_pv_window
      hStart hPrefix hRun)).elim
  | cons first remaining =>
    have hHead := List.head?_dropWhile_not (fun f : Event => f.pc != 1184) before
    have hDrop : before.dropWhile (fun f : Event => f.pc != 1184) = first :: remaining := hRest
    rw [hDrop] at hHead
    have hTag : first.pc = 1184 := by simpa using hHead
    rw [hSplit, hRest,
      List.append_assoc, List.cons_append] at hRun
    obtain ⟨u, hu, _, hPoll⟩ := resume_register_window_end
      (rs := [2991]) (by simpa using before_pv_window) (by simp)
      hStart.1 hStart.2 hTag hPrefix hRun
    obtain ⟨f, after, hTail⟩ := List.exists_cons_of_ne_nil
      (show remaining ++ e :: tail ≠ [] by simp)
    rw [hTail] at hPoll
    obtain ⟨m, p, ok, sc, hEvent, hFault, hRet⟩ := pv_poll_return hu hPoll
    cases ok with
    | true =>
      refine ⟨earlier.length, by rw [hSplit, hRest]; simp, m, p, sc, ?_⟩
      rw [hSplit, hRest, List.getElem?_append_right le_rfl, Nat.sub_self]
      simpa using hEvent
    | false =>
      let r := PTX.next (setReg u 4077 (.pred false))
      have hr : r.pc = 1185 := by change u.pc + 1 = 1185; omega
      have hPred : r.regs 4077 = some (.pred false) := by simp [r, PTX.next, setReg]
      let v := skip r
      let s := { v with pc := 1184 }
      have hv : v.pc = 1186 := by change r.pc + 1 = 1186; omega
      have hSkip : Tau kernel Assumptions.all L g r v := by
        have hf : r.fault = none := hFault
        simp [Tau, out, hf, hr, Flow.code_1185, guardHolds, readReg, hPred, pure, Except.pure,
          bind, Except.bind, v]
      have hBranch : Tau kernel Assumptions.all L g v s := by
        have hf : v.fault = none := hFault
        have hNone := Thread.asms_localRule_bra (L := L) (g := g) (t := v)
          (target := 1184) (uni := false) (by rw [hv]; decide) (by rw [hv]; decide)
        simp [Tau, out, hf, hv, Flow.code_1186, guardHolds, pure, Except.pure,
          execLocalA_noSegment (Proof.asms_segment_free v), execLocalRule_of_none hNone,
          execLocal, Op.rule, execBranch, Op.isLocal, s]
      have hSuffix := after_softmax_local_prefix
        ((Relation.ReflTransGen.single hSkip).tail hBranch) hRet
      rw [← hTail] at hSuffix
      have hsIn : inRegisterWindow 253 1184 s.pc := by change 253 ≤ 1184 ∧ 1184 ≤ 1184; decide
      obtain ⟨j, hj, m, p, sc, hGet⟩ :=
        pv_acquire_before_tail hsIn hLater hSuffix
      refine ⟨earlier.length + 1 + j, ?_, m, p, sc, ?_⟩
      · rw [hSplit, hRest, List.length_append, List.length_cons]
        omega
      · rw [hSplit, hRest, List.getElem?_append_right (by omega),
          show earlier.length + 1 + j - earlier.length = j + 1 by omega]
        exact hGet
termination_by before.length
decreasing_by
  rw [hSplit, hRest, List.length_append, List.length_cons]
  omega

/-- A run reaching the output after its first mask has acquired its last PV notification. -/
theorem pv_acquire_before_output_in_run {t : TState} {block total : Nat}
    {before tail : List Event} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hBlock : block < total) (hLimit : total < 2 ^ 31)
    (hAt : AtVector t 264 (softmaxMaskFacts L block total) t.sub t.acc)
    (hLater : 1184 < e.pc) (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    ∃ j < before.length, ∃ sc,
      before[j]? = some ⟨1184, .wait
        ⟨.shared, ctaOf L g, L.sharedBase + (222936 + 8 * ((total - 1) % 2))⟩
        ((total - 1) / 2 % 2) true true sc⟩ := by
  obtain ⟨j, hj, m, p, sc, hGet⟩ := pv_acquire_before_tail
    (show inRegisterWindow 253 1184 t.pc by rw [hAt.1]; decide) hLater hRun
  let wait : Event := ⟨1184, .wait m p true true sc⟩
  change before[j]? = some wait at hGet
  have hDrop := List.drop_eq_getElem_cons hj
  rw [(List.getElem?_eq_some_iff.mp hGet).2] at hDrop
  have hSplit : before = before.take j ++ wait :: before.drop (j + 1) := by
    rw [← hDrop]
    exact (List.take_append_drop ..).symm
  rw [hSplit, List.append_assoc, List.cons_append] at hRun
  obtain ⟨rfl, rfl, _⟩ := pv_wait_shape_in_trace hpre hBlock hLimit hAt rfl rfl hRun
  exact ⟨j, hj, sc, hGet⟩

/-- A followed epilogue state has passed all of its lane's body events. -/
theorem body_event_before_followed_epilogue {X : Execution} {j w : Nat} {d : Wg0.D} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hWait : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 d)))
    (hSite : d.site.inEpilogue = true) (he : X.get (g, j) = some e) (hTag : e.pc < 1147) :
    j < w := by
  by_contra! hLe
  have hGet : ((X.tr g).drop w)[j - w]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hLe]
    exact he
  have hMem := List.mem_of_getElem? hGet
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, o, hGood, hRun⟩ := actual_suffix_from_followed hX hg (hs g hg) hWait
    (List.ne_nil_of_mem hMem)
  have hAt : (Wg0.code P L g).AtD d t := hGood.1
  have hPc : t.pc = d.site.pc := hAt.1
  have hIn : epilogue t.pc := by
    rw [hPc]
    have bound (site : Wg0.Site) (h : site.inEpilogue = true) : 1147 ≤ site.pc := by
      cases site <;> simp only [Wg0.Site.inEpilogue, Bool.false_eq_true] at h
      all_goals first | decide | (rename_i tile; revert tile; decide) |
        (rename_i tile chunk; revert tile chunk; decide)
    exact bound d.site hSite
  have hAfter : 1147 ≤ e.pc := run_in_control_region epilogue_closed hIn hRun e hMem
  omega

/-- A concrete rescale store precedes the same lane's final PV wait. -/
theorem rescale_store_before_final_wait {X : Execution} {j w dst : Nat} {d : Wg0.D}
    {words : List Value} {shape : TcShape}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hWait : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 d)))
    (hSite : d.site = .svDone) (hStore : X.TSt (g, j) dst words shape) : j < w := by
  obtain ⟨tag, he⟩ := hStore
  obtain ⟨k, hTag⟩ := actual_tmem_store_site hX he rfl
  apply body_event_before_followed_epilogue hX hs hWait (by rw [hSite]; rfl) he
  rw [hTag]
  exact (show ∀ k : Fin 4, (Wg0.Site.rescaleStore k).pc < 1147 by decide) k

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
