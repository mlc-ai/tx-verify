-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderUb
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaUb
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreSites
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftUb
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrUb
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMachine
public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueRun

@[expose] public section

/-! # `Cross.SitesTmplOk`: no site of a thread's machine has an undefined-behaviour template

The role parts are `Cross.SitesTmplOk_loader`, `_mma`, `_store`, `_soft`, `_corr`. Here:

* the prologue (`Cross.SitesTmplOk_pro`): the shuffles read a 32-bit register of the table with
  the full member mask (`shfl_ok`), the elections have the full immediate mask (`electImm_ok`),
  an initialization fires the initialization of its table barrier (`init_event`,
  `init320_event`), and the fences and cluster-barrier operations are plain (`plainOk_tmpl`);
* the idle warp (`Cross.SitesTmplOk_idle`): a register request of a valid count and the return;
* the assembly over the thread's machine (`Cross.sitesTmplOk`), by the state's role. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- A full-mask shuffle of a 32-bit register, in a launch of whole warps, is not undefined
behaviour. -/
theorem shfl_ok {A : List Assumption} {g : Nat} {t : TState} {mode : ShflMode} {d r x : Nat}
    {ps : List (Option Nat)} {ty : Option DType} {b c : Int} (hb : L.block % 32 = 0)
    (hr : t.regs r = some (b32 x)) (f : Fault)
    (hrule : WarpInstr.rule ⟨.shfl mode, ty, some d :: ps, [.reg r, .imm b, .imm c],
      some (.imm (-1))⟩ = some .threadShfl := by rfl) :
    eventTmpl A L g t (.warp ⟨.shfl mode, ty, some d :: ps, [.reg r, .imm b, .imm c],
      some (.imm (-1))⟩) ≠ .ub f := by
  simp only [eventTmpl, warpTmpl, hrule, shflTmpl, readValue, readReg, hr, readBits, b32, pure,
    Except.pure]
  rw [show (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2 ^ 32 - 1 by decide]
  simp [hb, Value.bytes]

/-- A full-mask election with an immediate mask is not undefined behaviour. -/
theorem electImm_ok {A : List Assumption} {g : Nat} {t : TState} {dst : Option Nat} {p : Nat}
    {ty : Option DType} (f : Fault) :
    eventTmpl A L g t (.warp ⟨.elect, ty, [dst, some p], [], some (.imm (-1))⟩) ≠ .ub f := by
  have hm : electMember 4294967295 (laneOf L g) :=
    electMember_full (Nat.mod_lt (g % L.block) (show 0 < 32 by decide))
  simp only [eventTmpl, warpTmpl_elect, electTmpl, Prologue.readBits_full]
  rw [show (BitVec.ofNat 64 4294967295).toNat = 4294967295 by decide]
  simp [hm]

namespace Prologue

/-- A register live at a prologue site holds its table value. -/
theorem reg_at {g pc r : Nat} {t : TState}
    (h : Holds t.regs (factsAt L g (warpOf L g) (rankOf L g) pc)) (hl : r ∈ Flow.live pc) :
    t.regs r = some (valueOf L g (warpOf L g) (rankOf L g) r) :=
  holds_mem h (mem_factsFrom hl)

set_option maxHeartbeats 4000000 in
/-- **No prologue site has an undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre P L mem0) {g : Nat} {p : D} {t : TState} {ins : Instr}
    (h : At t p.site.pc (facts L g p)) (hc : kernel.code[p.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hR := h.2.2.2.2
  obtain ⟨s⟩ := p
  cases s with
  | shfl0 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
    exact shfl_ok hb (reg_at hR (r := 670) (by table_decide)) f
  | shfl1 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_1)
    exact shfl_ok hb (reg_at hR (r := 678) (by table_decide)) f
  | shfl2 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_2)
    exact shfl_ok hb (reg_at hR (r := 679) (by table_decide)) f
  | shfl3 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_3)
    exact shfl_ok hb (reg_at hR (r := 687) (by table_decide)) f
  | elect12 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0)
    exact electImm_ok f
  | elect e =>
    obtain ⟨dst, hc', -, -⟩ := code_elect e
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    exact electImm_ok f
  | init j =>
    refine not_ub_of_fires (pc := (Site.init j).pc) (fun f hf => ?_) f
    have := init_event hpre j h hc hf
    cases this
  | init320 =>
    refine not_ub_of_fires (pc := Site.init320.pc) (fun f hf => ?_) f
    have := init320_event hpre h hc hf
    cases this
  | fence0 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_0)
    exact plainOk_tmpl hb rfl f
  | fence1 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_1)
    exact plainOk_tmpl hb rfl f
  | clArrive =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_0)
    exact plainOk_tmpl hb rfl f
  | clWait =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_0)
    exact plainOk_tmpl hb rfl f

end Prologue

/-- **The prologue's part of `Cross.SitesTmplOk`.** -/
theorem Cross.SitesTmplOk_pro (hpre : Pre P L mem0) {g : Nat} (p : Prologue.D) (t : TState)
    (ins : Instr) (hat : (code L g).AtD (.inl p) t)
    (hc : kernel.code[(code L g).pc (.inl p)]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f :=
  Prologue.tmpl_ok hpre ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc f

/-- **The idle warp's part of `Cross.SitesTmplOk`**: a register request of a valid count and the
return. -/
theorem Cross.SitesTmplOk_idle (hpre : Pre P L mem0) {g : Nat} (s : Idle.D) (t : TState)
    (ins : Instr) (hc : kernel.code[(code L g).pc (.inr (.idle s))]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨site⟩ := s
  cases site with
  | setMaxReg =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_0)
    exact plainOk_tmpl hb (by decide) f
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    exact plainOk_tmpl hb rfl f

/-- **`Cross.SitesTmplOk`**: by the state's role. -/
theorem Cross.sitesTmplOk (hpre : Pre P L mem0) : Cross.SitesTmplOk L := by
  intro g hg d t ins hat hi hc f
  rcases d with p | r
  · exact Cross.SitesTmplOk_pro hpre p t ins hat hc f
  cases r with
  | idle s => exact Cross.SitesTmplOk_idle hpre s t ins hc f
  | loader d => exact Cross.SitesTmplOk_loader hpre hg d t ins hat hi hc f
  | mma d => exact Cross.SitesTmplOk_mma hpre hg d t ins hat hi hc f
  | store d => exact Cross.SitesTmplOk_store hpre d t ins hat hi hc f
  | softmax d => exact Cross.SitesTmplOk_soft hpre hg d t ins hat hi hc f
  | corr d => exact Cross.SitesTmplOk_corr hpre hg d t ins hat hi hc f

end
end PTX.Kernels.FlashAttn4Fwd.Proof
