-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmDStart
public import Kernels.InklingRelDecode.Proof.Thread.TmProA
public import Kernels.InklingRelDecode.Proof.Thread.TmSm
public import Kernels.InklingRelDecode.Proof.Thread.TmEpi
public import Kernels.InklingRelDecode.Proof.Thread.DCompAll

@[expose] public section

/-! # The default-partition thread's sites are not undefined behaviour

The composed machine `DComp.code` of a default-partition thread: the states in `DComp.tmRest`
would be the ones the regions' statements leave; there are none (`ProA.Site.tmRest_eq_false`),
and `DComp.tmpl_ok` covers every state. -/

namespace PTX.Kernels.InklingRelDecode.Proof.DComp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Tm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The default-partition states whose template is not proved here: none. -/
def tmRest : St → Bool := fun _ => false

/-- **A default-partition state not in `tmRest` has no undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre Q L mem0) (hg : g < L.threads) {s : St} (_hs : tmRest s = false)
    {t : TState} {ins : Instr} (hat : (code L g Q).AtD s t) (hi : (code L g Q).inv s)
    (hc : kernel.code[(code L g Q).pc s]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hH := hat.2.2.2.2
  cases s with
  | dstart d => exact DStart.tmpl_ok hpre hH hc f
  | pro d =>
    obtain ⟨tm, -, hp⟩ := hi.2
    have hbt : d.dt.pro.btB % 4 = 0 := by rw [hp]; exact hpre.btAlign
    have hx0 : d.dt.pro.x0.toNat % 2 = 0 := by
      rw [hp]
      simp only [DStart.inh, BitVec.toNat_ofNat]
      have := hpre.qAlign
      omega
    have hrd1 : d.dt.pro.rest 1949 = .ptr 64 true (.param (param "1")) 0 := by
      rw [hp]
      simp [DStart.inh]
    have hw70 : d.dt.pro.w70 % 8 = 0 := by
      rw [hp]
      have := hpre.headColsAlign
      show Q.headCols % 2 ^ 32 % 8 = 0
      omega
    exact ProA.tmpl_ok hpre hg hi.1 hbt hx0 hrd1 hw70 hat.2.1 (ProA.Site.tmRest_eq_false _) hH hc f
  | sm d => exact Sm.tmpl_ok hpre hi hat.2.1 hH hc f
  | epi d => exact Epi.tmpl_ok hpre hi.1 hi.2 hat.2.1 hH hc f

end
end PTX.Kernels.InklingRelDecode.Proof.DComp
