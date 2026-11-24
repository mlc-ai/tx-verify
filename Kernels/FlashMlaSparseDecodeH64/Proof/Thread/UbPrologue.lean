-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.AllocReadbackOrder
public import Lemmas.Flow.UbStop
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Lemmas.Flow.TmplOkSync

public section

/-! # Undefined-behaviour templates in the launch, dispatch and idle path -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbPrologue

open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem prologue_reg {s : Site} {t : TState} {r : Nat}
    (ha : (Machine.code P L g).AtD (.prologue s) t) (hl : r ∈ liveAll s.pc) :
    t.regs r = some (valueOf L g r) :=
  holds_mem ha.2.2.2.2 (mem_factsFrom hl)

private theorem alloc_tmpl_ok {s : Site} {t : TState}
    (hpre : Pre P L mem0) (ha : (Machine.code P L g).AtD (.prologue s) t)
    (hs : s = .alloc ∨ s = .allocStore) (f : Fault) :
    eventTmpl Assumptions.all L g t (.tcAlloc .one 554 0 (.reg 555)) ≠ .ub f := by
  have hr : t.regs 554 = some (b32 (L.sharedBase + 222752)) := by
    rcases hs with rfl | rfl
    all_goals exact prologue_reg ha (by table_decide)
  have hc : t.regs 555 = some (b32 512) := by
    rcases hs with rfl | rfl
    all_goals exact prologue_reg ha (by table_decide)
  have hbase := sharedBase_lt hpre
  have hAlign := hpre.sharedAlignment
  rw [← hpre.sharedBase] at hAlign
  exact tcAlloc_ok (by rw [hpre.block]) hr (by omega) (by omega) hc f

/-- A represented launch-prologue site has a well-formed event template. -/
theorem prologue_tmpl_ok (hpre : Pre P L mem0) {s : Site} {t : TState} {ins : Instr}
    (ha : (Machine.code P L g).AtD (.prologue s) t)
    (hc : kernel.code[(Machine.code P L g).pc (.prologue s)]? = some ins)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  change kernel.code[s.pc]? = some ins at hc
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  cases s
  case shfl0 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
    have hr : t.regs 519 = some (b32 (wgOf L g)) :=
      prologue_reg ha (by table_decide)
    exact shfl_imm_ok (d := 462) (p := some 2) (.inr rfl) hb hr f
  case shfl1 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_1)
    have hr : t.regs 464 = some (b32 (warpOf L g)) :=
      prologue_reg ha (by table_decide)
    exact shfl_imm_ok (d := 465) (p := some 3) (.inr rfl) hb hr f
  case elect0 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0)
    exact elect_ok (prologue_reg ha (r := 522) (by table_decide)) f
  case elect1 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_1)
    exact elect_ok (prologue_reg ha (r := 525) (by table_decide)) f
  case init j =>
    intro hu
    have hd : (Machine.machine P L g).Fired (some (.prologue (.init j)))
        ⟨t.pc, .ub f⟩ none := by
      refine ⟨t, ⟨ha, trivial⟩, ?_⟩
      change Fires t.pc (match kernel.code[(Site.init j).pc]? with
        | some ins => eventTmpl Assumptions.all L g t ins.op
        | none => .ub .pcOutOfRange) ⟨t.pc, .ub f⟩ none
      rw [hc]
      change Fires t.pc (eventTmpl Assumptions.all L g t ins.op) ⟨t.pc, .ub f⟩ none
      rw [hu]
      exact ⟨rfl, rfl⟩
    cases RingEvents.barrier_init hpre hd
  case fence =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_0)
    exact plainOk_tmpl hb rfl f
  case alloc =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
    exact alloc_tmpl_ok hpre ha (.inl rfl) f
  case allocStore =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
    exact alloc_tmpl_ok hpre ha (.inr rfl) f
  case allocRead =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    change eventTmpl Assumptions.all L g t (.mem allocLoad) ≠ _
    rw [PrologueAllocation.alloc_read_template hpre ha.2.1]
    intro hh
    cases hh
  case relinquish =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
    exact plainOk_tmpl hb rfl f
  case barrier =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
    intro hh
    cases hh
  case handoff w =>
    fin_cases w
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_0)
      exact plainOk_tmpl hb rfl f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_1)
      exact plainOk_tmpl hb rfl f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_2)
      exact plainOk_tmpl hb rfl f

/-- A represented warp dispatch cannot fault while broadcasting the stored warp index. -/
theorem head_tmpl_ok (hpre : Pre P L mem0) {t : TState} {ins : Instr}
    (ha : (Machine.code P L g).AtD .head t)
    (hc : kernel.code[(Machine.code P L g).pc .head]? = some ins)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_2)
  change At t 1843 (Wg1Mma.facts P L g Wg1Mma.init) at ha
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  rw [Wg1Mma.event_head P L g ha hb]
  intro hh
  cases hh

/-- The two idle length reads, the closing CTA barrier, and the return have valid templates. -/
theorem idle_tmpl_ok (hpre : Pre P L mem0) {s : Thread.Site} {t : TState} {ins : Instr}
    (ha : (Machine.code P L g).AtD (.idle s) t)
    (hc : kernel.code[(Machine.code P L g).pc (.idle s)]? = some ins)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  change At t s.pc (Thread.facts L g s) at ha
  change kernel.code[s.pc]? = some ins at hc
  cases s
  case loadTopk =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_41)
    change eventTmpl Assumptions.all L g t (.mem Thread.ncLoadTopk) ≠ _
    rw [Thread.event_loadTopk hpre ha]
    intro hh
    cases hh
  case loadExtra =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_42)
    change eventTmpl Assumptions.all L g t (.mem Thread.ncLoadExtra) ≠ _
    rw [Thread.event_loadExtra hpre ha]
    intro hh
    cases hh
  case sync =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_14)
    rw [Thread.event_sync ha hpre.block]
    intro hh
    cases hh
  case exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    intro hh
    cases hh

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbPrologue
