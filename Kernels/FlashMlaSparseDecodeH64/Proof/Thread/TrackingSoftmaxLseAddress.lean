-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxLseSteps
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingStoreExtent
import Lemmas.Flow.EventCont

@[expose] public section

/-! # The LSE destination in a concrete softmax suffix -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame
open Wg0 (eOf qOf)

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def headsRegion (pc : Nat) : Bool := pc == 1160
private def branchRegion (pc : Nat) : Bool := pc == 1161
private def lseLaneRegion (pc : Nat) : Bool := decide (1162 ≤ pc ∧ pc ≤ 1178)
private def addressRegion (pc : Nat) : Prop := 1167 ≤ pc ∧ pc ≤ 1178
private instance (pc : Nat) : Decidable (addressRegion pc) :=
  inferInstanceAs (Decidable (1167 ≤ pc ∧ pc ≤ 1178))

set_option maxRecDepth 100000 in
private theorem heads_audit : registerRegionChecked 1729 headsRegion [1159] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem branch_audit : registerRegionChecked 118 branchRegion [1160] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem lane_audit : registerRegionChecked 459 lseLaneRegion [1161] = true := by
  decide +kernel

private def LseAddressState (P : Params) (L : Launch) (g : Nat) (d : Wg0.D) (t : TState) : Prop :=
  SoftmaxWriteState (fun r => some (Wg0.valueOf P L g d r)) t ∧
    (headsRegion t.pc = true → t.regs 1729 = some (b32 64)) ∧
    (branchRegion t.pc = true → t.regs 118 = some (.pred (decide (64 ≤ tidOf L g % 128)))) ∧
    (lseLaneRegion t.pc = true → tidOf L g % 128 < 64) ∧
    (addressRegion t.pc → ∃ v, AtVector v 1167 (lseAddressFacts L g) v.sub v.acc ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) v t)

set_option maxRecDepth 100000 in
private theorem lse_initial_facts {d : Wg0.D} {t : TState}
    (hState : SoftmaxWriteState (fun r => some (Wg0.valueOf P L g d r)) t)
    (hPc : t.pc = 1167) (hFault : t.fault = none) :
    AtVector t 1167 (lseAddressFacts L g) t.sub t.acc := by
  refine ⟨hPc, rfl, rfl, hFault, ?_⟩
  have hb : softmaxInBody t.pc = true := by rw [hPc]; decide
  have hRegs := hState.2
  have hk := And.intro (hRegs 2991 (by decide) hb)
    (And.intro (hRegs 460 (by decide) hb) (And.intro (hRegs 459 (by decide) hb)
      (And.intro (hRegs 463 (by decide) hb) True.intro)))
  simpa [lseAddressFacts, Wg0.valueOf, Wg0.table, lookupLit] using hk

private theorem continued_tau_fault_free {t u : TState}
    (hTau : Tau kernel Assumptions.all L g t u) : u.fault = none := by
  have ht := tau_fault_free hTau
  unfold Tau out at hTau
  split at hTau
  · cases hTau
  split at hTau
  · cases hTau
  split at hTau
  · cases hTau
  · cases hTau
    exact ht
  split at hTau
  · split at hTau
    · rename_i v hv
      cases hTau
      exact (local_frame hv).fault.trans ht
    · cases hTau
  · cases hTau

set_option maxRecDepth 100000 in
private theorem no_address_branch_targets :
    (List.range 11).all (fun k => !(kernel.branchTarget (1168 + k))) = true := by
  decide +kernel

private theorem address_no_branch {pc : Nat} (hLo : 1168 ≤ pc) (hHi : pc ≤ 1178) :
    kernel.branchTarget pc = false := by
  have hEq : 1168 + (pc - 1168) = pc := by omega
  have h := List.all_eq_true.mp no_address_branch_targets (pc - 1168)
    (List.mem_range.mpr (by omega))
  simpa [hEq] using h

set_option maxRecDepth 100000 in
private theorem address_tau {d : Wg0.D} {t u : TState}
    (hpre : Pre P L mem0) (hOld : LseAddressState P L g d t)
    (hTau : Tau kernel Assumptions.all L g t u) :
    LseAddressState P L g d u := by
  have hSoft := softmax_write_tau hOld.1 hTau
  have hFault := tau_fault_free hTau
  refine ⟨hSoft, register_region_tau
    (property := fun v => v = some (b32 64)) heads_audit hOld.2.1 ?_ hTau,
    register_region_tau (property := fun v =>
      v = some (.pred (decide (64 ≤ tidOf L g % 128)))) branch_audit hOld.2.2.1 ?_ hTau,
    register_region_tau (property := fun _ => tidOf L g % 128 < 64)
      lane_audit hOld.2.2.2.1 ?_ hTau, ?_⟩
  · intro ht _
    have hp := List.mem_singleton.mp ht
    have hReg := hOld.1.2 2991 (by decide) (by rw [hp]; decide)
    have hPtr : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
      simpa [Wg0.valueOf, Wg0.table, lookupLit] using hReg
    have hAt : AtVector t 1159 [] t.sub t.acc := ⟨hp, rfl, rfl, hFault, trivial⟩
    obtain ⟨v, hRun, hv⟩ := lse_param_vector hpre hAt (by simp) Flow.code_1159 hPtr
      (Wg0.supplied_int hpre.paramHq (by decide)) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) rfl
    have hHq : paramElem 32 32 (paramNat L (param "0") 8 4) = b32 64 := by
      change b32 (Thread.paramWord L 8 4) = b32 64
      rw [Thread.paramWord_four (fun i hi => hpre.paramHq i hi)]
      rfl
    exact (one_step_matches hTau hRun) ▸ (hHq ▸ hv.2.2.2.2.1)
  · intro ht _
    have hp := List.mem_singleton.mp ht
    have hHead := hOld.2.1 (hp ▸ by decide)
    have hReg := hOld.1.2 463 (by decide) (by rw [hp]; decide)
    have hLane : t.regs 463 = some (b32 (tidOf L g % 128)) := by
      simpa [Wg0.valueOf, Wg0.table, lookupLit] using hReg
    have hAt : AtVector t 1160 [(463, b32 (tidOf L g % 128)), (1729, b32 64)] t.sub t.acc :=
      ⟨hp, rfl, rfl, hFault, hLane, hHead, trivial⟩
    have hBound := Nat.mod_lt (tidOf L g) (by decide : 0 < 128)
    obtain ⟨v, hRun, hv⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 1161 [(118, .pred (decide (64 ≤ tidOf L g % 128)))] t.sub t.acc := by
      seg_fp hAt using norm_signed []
    exact (one_step_matches hTau hRun) ▸ hv.2.2.2.2.1
  · intro ht hu
    have hp := List.mem_singleton.mp ht
    by_contra! hWide
    have hReg := hOld.2.2.1 (hp ▸ by decide)
    have hPred : t.regs 118 = some (.pred true) := by simpa [hWide] using hReg
    let v := { t with pc := 1179 }
    have hNoLocal := Thread.asms_localRule_bra (L := L) (g := g) (t := t)
      (target := 1179) (uni := false) (by rw [hp]; decide) (by rw [hp]; decide)
    have hExec : execLocalA Assumptions.all L g t (.bra 1179 false) = .ok v := by
      rw [execLocalA_noSegment (asms_segment_free t), execLocalRule_of_none hNoLocal]
      rfl
    have hRun : run kernel Assumptions.all L g 1 t = some v := by
      simp [run, tauStep, out, hFault, hp, Flow.code_1161, guardHolds, readReg, hPred,
        pure, Except.pure, bind, Except.bind, hExec, Op.isLocal]
    have hEq := one_step_matches hTau hRun
    rw [hEq] at hu
    cases hu
  · intro hu
    by_cases hEntry : u.pc = 1167
    · exact ⟨u, lse_initial_facts hSoft hEntry (continued_tau_fault_free hTau), .refl⟩
    · obtain ⟨hLo, hHi⟩ := hu
      have hPrev := tau_step_before_non_target hTau (address_no_branch (by omega) hHi)
      obtain ⟨v, hv, hPath⟩ :=
        hOld.2.2.2.2 (show addressRegion t.pc from ⟨by omega, by omega⟩)
      exact ⟨v, hv, hPath.tail hTau⟩

set_option maxRecDepth 100000 in
private theorem address_local_instructions : kernel.code.zipIdx.all (fun (ins, pc) =>
    !decide (1166 ≤ pc ∧ pc < 1178) || ins.op.isLocal) = true := by decide +kernel

private theorem event_cannot_enter_address {t u : TState} {e : Event}
    (hStep : EStep kernel Assumptions.all L g t e (some u)) : ¬ addressRegion u.pc := by
  intro h
  obtain ⟨ins, hc, hLocal, hf⟩ := estep_event_source hStep
  have hRet := (estep_return_pc hStep (fun _ _ _ h => local_frame h)).2
  have ht : 1166 ≤ t.pc ∧ t.pc ≤ 1178 := by
    obtain ⟨hLo, hHi⟩ := h
    omega
  by_cases hEnd : t.pc = 1178
  · rw [hEnd, Flow.code_1178] at hc
    obtain rfl := Option.some.inj hc
    obtain ⟨hu, _⟩ := fires_stv_after (sp := .global) (ty := .int .b 32)
      (bw := 64) (base := 3574) (off := 0) (srcs := [.reg 1733]) rfl rfl hf
    have hEq : u.pc = t.pc + 1 := by
      rw [hu]
      simp [afterStore]
    have hHigh := h.2
    omega
  · have hAudit := List.all_eq_true.mp address_local_instructions (ins, t.pc)
      (List.mem_zipIdx_iff_getElem?.mpr hc)
    have hMid : t.pc < 1178 := by omega
    simp [ht.1, hMid, hLocal] at hAudit

set_option maxRecDepth 100000 in
private theorem address_event {d : Wg0.D} {t u : TState} {e : Event}
    (hOld : LseAddressState P L g d t)
    (hStep : EStep kernel Assumptions.all L g t e (some u)) : LseAddressState P L g d u := by
  refine ⟨softmax_write_event hOld.1 hStep, register_region_event
    (property := fun v => v = some (b32 64)) heads_audit
    (register_updates_local (by decide +kernel))
    hOld.2.1 hStep, register_region_event (property := fun v =>
      v = some (.pred (decide (64 ≤ tidOf L g % 128)))) branch_audit
      (register_updates_local (by decide +kernel)) hOld.2.2.1 hStep,
    register_region_event (property := fun _ => tidOf L g % 128 < 64) lane_audit
      (register_updates_local (by decide +kernel)) hOld.2.2.2.1 hStep,
    fun h => (event_cannot_enter_address hStep h).elim⟩

/-- A global LSE write reached from the first mask wait stays in the full LSE allocation,
even if the thread's numerical tracking was dismissed. -/
theorem actual_lse_write_extent {start i : Nat} {d : Wg0.D} {a : Acc} {bs : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hMask : d.site = .maskReady)
    (hState : Frame.stateAt (Machine.code P L) X g start = some (some (.wg0 d)))
    (hLe : start ≤ i) (hw : X.get (g, i) = some ⟨1178, .wr a bs⟩) :
    P.lseBase ≤ a.loc.addr ∧ a.loc.addr + a.size ≤ P.lseBase + lseBytes P := by
  have hGet : ((X.tr g).drop start)[i - start]? = some ⟨1178, .wr a bs⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hLe]
    exact hw
  have hm := List.mem_of_getElem? hGet
  have hg := Frame.lt_of_get hX hw
  obtain ⟨t, o, hSoft, hp, hRun⟩ :=
    softmax_write_suffix hX hs hg hMask hState (List.ne_nil_of_mem hm)
  have hInitial : LseAddressState P L g d t := by
    refine ⟨hSoft, ?_, ?_, ?_, ?_⟩
    all_goals rw [hp]
    · nofun
    · nofun
    · nofun
    · intro h
      have := h.1
      omega
  obtain ⟨u, q, hAt, hStep⟩ :=
    actual_event_invariant (address_tau hpre) address_event hInitial hRun hm
  have hPc : u.pc = 1178 := (estep_source_pc hStep).symm
  have hFirst := hAt.2.2.2.1 (hPc ▸ by decide)
  obtain ⟨v, hv, hV⟩ := hAt.2.2.2.2 (hPc ▸ by decide)
  have hb : eOf L g < P.b := Wg1Mma.eOf_lt_b hpre
  have hq : qOf L g < P.s_q := Wg1Mma.queryOf_lt hpre hg
  obtain ⟨last, hCode, hl⟩ := lse_address_vector hpre hb hq hFirst hv
  have hStops : Stops kernel Assumptions.all L g last :=
    ⟨_, out_event hl.2.2.2.1 (hl.1 ▸ Flow.code_1178) rfl rfl⟩
  have hSame := stop_unique hV (run_rtg hCode) (stops_of_estep hStep) hStops
  subst last
  have hExtent := lse_loc_extent hpre (g := g) hb hq
  have hRange := hpre.tensorRange.2.2
  have heff := effAddr_global (L := L) (g := g) hl.2.2.2.2.1 (by omega)
  cases q with
  | none =>
    obtain ⟨_, _, hf⟩ := hStep
    have hBad := fires_none_ends hf
    simp [Ends] at hBad
  | some w =>
    obtain ⟨ins, hc, _, hf⟩ := estep_event_source hStep
    rw [hPc, Flow.code_1178] at hc
    obtain rfl := Option.some.inj hc
    rw [eventTmpl, memTmpl_store (sp := .global) (base := 3574) (w := 64)
      rfl rfl rfl rfl (by simp), hPc] at hf
    obtain ⟨_, hStart, hFinal⟩ := direct_store_extent heff hf
    exact ⟨hExtent.1.trans hStart, hFinal.trans hExtent.2⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
