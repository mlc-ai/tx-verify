-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaRoleCut
public import Kernels.TmlFa4Fwd.Proof.SchedulerCuts
public import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof PTX.EventFrame Mma

noncomputable section

/-- The cut points separate parameter reads, scheduler loops and the shared exit path. -/
def epilogueRegion : Fin 6 → RoleRegion
  | 0 => ⟨2769, 2821, [2821, 2878]⟩
  | 1 => ⟨2824, 2878, [2878]⟩
  | 2 => ⟨2878, 2949, [2949, 3099]⟩
  | 3 => ⟨2950, 3029, [3029, 3086]⟩
  | 4 => ⟨3032, 3086, [3086]⟩
  | 5 => ⟨3086, 3099, [3099]⟩

def epilogueBoundsFrame (i : Fin 6) : List Nat :=
  [1062, 1072] ++ if i = 0 then [7228] else if i = 3 then [7147] else []

private def controlCode (i : Fin 6) (ins : Instr) : Bool :=
  let site := epilogueRegion i
  !allocationOp ins.op && (ins.op.isLocal || linearRoleOp ins.op) &&
    (epilogueBoundsFrame i).all
      (fun r => !((mmaWrites ins.op ++ epilogueExtraWrites ins.op).contains r)) &&
    (match ins.op with
      | .bra t _ => site.lo ≤ t && (t < site.hi || site.exits.contains t)
      | .brx .. => false
      | _ => true)

private theorem controlCodeAt (i : Fin 6) {pc : Nat} {ins : Instr}
    (hLo : (epilogueRegion i).lo ≤ pc) (hHi : pc < (epilogueRegion i).hi)
    (hc : kernel.code[pc]? = some ins) : controlCode i ins = true := by
  let lo := (epilogueRegion i).lo
  let hi := (epilogueRegion i).hi
  have hAll : ((kernel.code.drop lo).take (hi - lo)).all (controlCode i) = true := by
    fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  have hLower : lo ≤ pc := hLo
  have hUpper : pc < hi := hHi
  have hMem : ((kernel.code.drop lo).take (hi - lo))[pc - lo]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLower, hc]
  exact List.all_eq_true.mp hAll ins (List.mem_of_getElem? hMem)

private theorem epilogueRegionOut (i : Fin 6) {l : Launch} {g : Nat} {s : TState}
    (hLo : (epilogueRegion i).lo ≤ s.pc) (hHi : s.pc < (epilogueRegion i).hi) :
    out kernel Assumptions.all l g s = out kernel [] l g s := by
  apply epilogue_out_all_eq_nil
  fin_cases i <;> simp only [epilogueRegion] at hLo hHi <;>
    exact .inl ⟨by omega, by omega⟩

private theorem epilogueRegionNext (i : Fin 6) {pc : Nat}
    (hp : (epilogueRegion i).lo ≤ pc) (hq : pc < (epilogueRegion i).hi) :
    (epilogueRegion i).lo ≤ pc + 1 ∧
      (pc + 1 < (epilogueRegion i).hi ∨ pc + 1 ∈ (epilogueRegion i).exits) := by
  refine ⟨by omega, ?_⟩
  by_cases hi : pc + 1 < (epilogueRegion i).hi
  · exact .inl hi
  · have he : pc + 1 = (epilogueRegion i).hi := by omega
    right
    rw [he]
    fin_cases i <;> decide

private theorem notWrittenByLocal {op : Op} {r : Nat} (h : r ∉ mmaWrites op) :
    r ∉ writesRegs op := by
  cases op <;> first | exact h | simp [writesRegs]

/-- Any continuing step in the six scheduler intervals keeps the protected registers and
either stays in the same interval or takes one of its exact decoded exits. -/
theorem epilogueIntervalStep (i : Fin 6) {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (hLo : (epilogueRegion i).lo ≤ s.pc) (hHi : s.pc < (epilogueRegion i).hi)
    (hSub : s.sub = 0) (hAcc : s.acc = []) (he : WStep kernel Assumptions.all l g s ev u) :
    ((epilogueRegion i).lo ≤ u.pc ∧ u.pc < (epilogueRegion i).hi ∨
      u.pc ∈ (epilogueRegion i).exits ∧ u.fault = none) ∧
    u.sub = 0 ∧ u.acc = [] ∧ ∀ r ∈ epilogueBoundsFrame i, u.regs r = s.regs r := by
  let site := epilogueRegion i
  have hNext := epilogueRegionNext i hLo hHi
  have hAdv (hPc : u.pc = s.pc + 1) (hf : u.fault = none) :
      site.lo ≤ u.pc ∧ u.pc < site.hi ∨ u.pc ∈ site.exits ∧ u.fault = none := by
    rw [hPc]
    exact hNext.2.elim (fun h => .inl ⟨hNext.1, h⟩) (fun h => .inr ⟨h, hf⟩)
  have hRegs {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
      (r : Nat) (hr : r ∈ epilogueBoundsFrame i) :
      r ∉ mmaWrites ins.op ∧ r ∉ epilogueExtraWrites ins.op := by
    have hk := controlCodeAt i hLo hHi hc
    simp only [controlCode, Bool.and_eq_true] at hk
    have hb := List.all_eq_true.mp hk.1.2 r hr
    simpa using hb
  rcases he with ⟨-, ht⟩ | ⟨e, -, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← epilogueRegionOut i hLo hHi]
    obtain ⟨ins, hc⟩ := tau_core_has_code ht'
    have hf : s.fault = none := by
      cases h : s.fault
      · rfl
      · simp [Tau, out, h] at ht'
    have hCode := controlCodeAt i hLo hHi hc
    simp only [controlCode, Bool.and_eq_true] at hCode
    rcases tau_core_frame hc ht' with rfl | hF
    · exact ⟨hAdv rfl hf, rfl, rfl, fun _ _ => rfl⟩
    · refine ⟨?_, hF.sub.trans hSub, hF.acc.trans hAcc, fun r hr => ?_⟩
      · have hPc := hF.pc
        cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc
        case bra dst aligned =>
          have hDst : site.lo ≤ dst ∧ (dst < site.hi ∨ dst ∈ site.exits) := by
            simpa [hop] using hCode.2
          rw [hPc]
          exact hDst.2.elim (fun ht => .inl ⟨hDst.1, ht⟩)
            (fun ht => .inr ⟨ht, hF.fault.trans hf⟩)
        case brx => simp [hop] at hCode
        all_goals exact hAdv hPc (hF.fault.trans hf)
      · exact hF.regs r (notWrittenByLocal (hRegs hc r hr).1)
  · obtain ⟨ins, hc, hLocal, _⟩ := estep_event_source he
    have hf : s.fault = none := by
      cases h : s.fault
      · rfl
      · obtain ⟨m, hm, hFire⟩ := he
        simp only [out, h, Out.ev.injEq] at hm
        subst m
        cases hFire.2
    have hCode := controlCodeAt i hLo hHi hc
    simp only [controlCode, Bool.and_eq_true, hLocal, Bool.false_or] at hCode
    have hOp := hCode.1.1.2
    simp only [linearRoleOp, Bool.or_eq_true] at hOp
    rcases hOp with hM | hE
    · have hNo : allocationOp ins.op = false := by simpa using hCode.1.1.1
      obtain ⟨_, hA, hx | hx | hx⟩ :=
        linearEventProgressWithSub hc hM (by omega) hAcc he
      · have hZ := hx.2.2.elim id (fun hh => hh.1.trans hSub)
        exact ⟨hAdv hx.1 (hx.2.1.trans hf), hZ, hA,
          fun r hr => mmaEventRegs hc hM (hRegs hc r hr).1 he⟩
      · simp [hNo] at hx
      · exact ⟨.inl ⟨hx.1 ▸ hLo, hx.1 ▸ hHi⟩, hx.2.1.trans hSub, hA,
          fun r hr => mmaEventRegs hc hM (hRegs hc r hr).1 he⟩
    · obtain ⟨hP, hS, hA, hF⟩ := epilogueExtraProgress hc hE he
      exact ⟨hAdv hP (hF.trans hf), hS.trans hSub, hA.trans hAcc,
        fun r hr => epilogueExtraRegs hc hE (hRegs hc r hr).2 he⟩

def epilogueSetupSpan : Fin 4 → Nat × Nat
  | 0 => (2768, 2769)
  | 1 => (2821, 2824)
  | 2 => (2949, 2950)
  | 3 => (3029, 3032)

private theorem setupCodeAt (i : Fin 4) {pc : Nat} {ins : Instr}
    (hLo : (epilogueSetupSpan i).1 ≤ pc) (hHi : pc < (epilogueSetupSpan i).2)
    (hc : kernel.code[pc]? = some ins) :
    ins.op.isLocal = true ∧ schedulerFallsThrough ins.op = true := by
  let lo := (epilogueSetupSpan i).1
  let hi := (epilogueSetupSpan i).2
  have hAll : ((kernel.code.drop lo).take (hi - lo)).all
      (fun ins => ins.op.isLocal && schedulerFallsThrough ins.op) = true := by
    fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  have hLower : lo ≤ pc := hLo
  have hUpper : pc < hi := hHi
  have hs : ((kernel.code.drop lo).take (hi - lo))[pc - lo]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLower, hc]
  simpa only [Bool.and_eq_true] using List.all_eq_true.mp hAll ins (List.mem_of_getElem? hs)

theorem epilogueSetupStep (i : Fin 4) {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : (epilogueSetupSpan i).1 ≤ s.pc) (hHi : s.pc < (epilogueSetupSpan i).2)
    (hStep : WStep kernel Assumptions.all l g s e u) :
    e = none ∧ Tau kernel Assumptions.all l g s u ∧ u.pc = s.pc + 1 := by
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have hModel : out kernel Assumptions.all l g s = out kernel [] l g s := by
      apply epilogue_out_all_eq_nil
      fin_cases i <;> simp only [epilogueSetupSpan] at hLo hHi <;>
        exact .inl ⟨by omega, by omega⟩
    have hT : Tau kernel [] l g s u := by unfold Tau at ht ⊢; rwa [← hModel]
    obtain ⟨ins, hc⟩ := tau_core_has_code hT
    have hCode := setupCodeAt i hLo hHi hc
    refine ⟨rfl, ht, ?_⟩
    rcases tau_core_frame hc hT with rfl | hT
    · rfl
    · have hPc := hT.pc
      cases ho : ins.op <;> simp_all [schedulerFallsThrough, nextPc, BrxTarget]
  · obtain ⟨ins, hc, hLoc, _⟩ := estep_event_source he
    rw [(setupCodeAt i hLo hHi hc).1] at hLoc
    cases hLoc

private theorem setupFrameAt (i : Fin 4) {pc : Nat} {ins : Instr}
    (hLo : (epilogueSetupSpan i).1 ≤ pc) (hHi : pc < (epilogueSetupSpan i).2)
    (hc : kernel.code[pc]? = some ins) :
    1062 ∉ writesRegs ins.op ∧ 1072 ∉ writesRegs ins.op := by
  let lo := (epilogueSetupSpan i).1
  let hi := (epilogueSetupSpan i).2
  have hAll : ((kernel.code.drop lo).take (hi - lo)).all
      (fun ins => !((writesRegs ins.op).contains 1062) &&
        !((writesRegs ins.op).contains 1072)) = true := by
    fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  have hLower : lo ≤ pc := hLo
  have hUpper : pc < hi := hHi
  have hs : ((kernel.code.drop lo).take (hi - lo))[pc - lo]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLower, hc]
  simpa using List.all_eq_true.mp hAll ins (List.mem_of_getElem? hs)

theorem epilogueSetupRegisters (i : Fin 4) {l : Launch} {g n : Nat} {s u : TState}
    (hLo : (epilogueSetupSpan i).1 ≤ s.pc) (hHi : s.pc + n ≤ (epilogueSetupSpan i).2)
    (hr : run kernel Assumptions.all l g n s = some u) :
    u.pc = s.pc + n ∧ u.regs 1062 = s.regs 1062 ∧ u.regs 1072 = s.regs 1072 := by
  induction n generalizing s with
  | zero =>
    change some s = some u at hr
    obtain rfl := Option.some.inj hr
    exact ⟨by omega, rfl, rfl⟩
  | succ n ih =>
    simp only [run] at hr
    cases hs : tauStep kernel Assumptions.all l g s with
    | none => simp [hs] at hr
    | some v =>
      rw [hs, Option.bind_some] at hr
      have hT := tauStep_iff.mp hs
      have hh : s.pc < (epilogueSetupSpan i).2 := by omega
      have hp := (epilogueSetupStep i hLo hh (.inl ⟨rfl, hT⟩)).2.2
      have hv : (epilogueSetupSpan i).1 ≤ v.pc := by omega
      have hLater : v.pc + n ≤ (epilogueSetupSpan i).2 := by omega
      obtain ⟨hN, hW, hC⟩ := ih hv hLater hr
      have hEq : out kernel Assumptions.all l g s = out kernel [] l g s := by
        apply epilogue_out_all_eq_nil
        fin_cases i <;> simp only [epilogueSetupSpan] at hLo hh <;>
          exact .inl ⟨by omega, by omega⟩
      have ht : Tau kernel [] l g s v := by unfold Tau at hT ⊢; rwa [← hEq]
      obtain ⟨ins, hc⟩ := tau_core_has_code ht
      have hRegs := setupFrameAt i hLo hh hc
      have hpc : u.pc = s.pc + (n + 1) := by omega
      rcases tau_core_frame hc ht with rfl | hFrame
      · exact ⟨hpc, hW, hC⟩
      · exact ⟨hpc, hW.trans (hFrame.regs _ hRegs.1), hC.trans (hFrame.regs _ hRegs.2)⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
