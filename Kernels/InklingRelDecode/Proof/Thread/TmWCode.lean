-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmIdle
public import Kernels.InklingRelDecode.Proof.Thread.TmLoader
public import Kernels.InklingRelDecode.Proof.Thread.TmMma
public import Kernels.InklingRelDecode.Proof.Thread.WCompAll

@[expose] public section

/-! # The worker thread's sites are not undefined behaviour

The composed machine `WComp.code` of a worker thread (`TmplOk` of its sites): the sites the
launch and the invariant decide are proved (`WComp.tmpl_ok`), every state; `WComp.tmRest` is
empty. -/

namespace PTX.Kernels.InklingRelDecode.Proof.WComp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Tm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The worker states whose template is not proved here: none. -/
def tmRest : WSt → Bool := fun _ => false

/-- **A worker state not in `tmRest` has no undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre Q L mem0) (hg : g < L.threads) {s : WSt} (_hs : tmRest s = false)
    {t : TState} {ins : Instr} (hat : (code L g Q).AtD s t) (hi : (code L g Q).inv s)
    (hc : kernel.code[(code L g Q).pc s]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hH := hat.2.2.2.2
  cases s with
  | worker w => exact Worker.tmpl_ok hpre hH hc f
  | idle d => exact Worker.Idle.tmpl_ok hpre hc f
  | loader d P =>
    have hbt : Loader.natOf64 (d.pro 2020) % 4 = 0 := by
      rw [hi.2.1 2020 (by decide) (by decide)]
      have h := hi.2.2.1.pins.bt
      simp only [Loader.Pro.val, Loader.Pro.table, PTX.Flow.lookupLit, Option.getD_some,
        Loader.natOf64, b64, BitVec.toNat_ofNat]
      omega
    have hw70 : Loader.natOf (d.pro 531) % 8 = 0 := by
      rw [hi.2.1 531 (by decide) (by decide)]
      have h := hi.2.2.1.pins.w70
      simp only [Loader.Pro.val, Loader.Pro.table, PTX.Flow.lookupLit, Option.getD_some,
        Loader.natOf, b32, BitVec.toNat_ofNat]
      omega
    have hrd1 : d.pro 1949 = .ptr 64 true (.param (param "1")) 0 := by
      rw [hi.2.1 1949 (by decide) (by decide)]
      simp [Loader.Pro.val, Loader.Pro.table, List.lookup, hi.2.2.1.pins.rd1]
    exact Loader.tmpl_ok hpre hg hi.1 hbt hw70 hrd1 hH hc f
  | mma d P => exact Mma.tmpl_ok hpre hg hi.1 hi.2.2.2.2.1 hH hc f
  | exit x =>
    have hb : L.block % 32 = 0 := by rw [hpre.block]
    obtain ⟨s, P⟩ := x
    cases s
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_37)
      exact barSync_imm_ok (id := 0) (by decide) f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
      exact plainOk_tmpl hb rfl f

end
end PTX.Kernels.InklingRelDecode.Proof.WComp
