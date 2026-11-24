-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbMmaControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace

public section

/-! # Defined templates for query loads, Tensor Memory copies, and MMA issues -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbMma

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- All live MMA role event templates are defined. -/
theorem tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads) :
    (Wg1Mma.code P L g).TmplOk := by
  rintro ⟨site, i⟩ t ins ha hi hc f
  cases site
  case qLoad k =>
    rw [MmaDataTrace.qLoad_template hpre hg i k ha hc]
    intro he
    cases he
  case qCopy k =>
    rw [MmaDataTrace.qCopy_template hpre hg i k ha hc]
    intro he
    cases he
  case qkMma k =>
    rw [MmaDataTrace.qkMma_template hpre hg i k ha hc]
    intro he
    cases he
  case pvMma k =>
    rw [MmaDataTrace.pvMma_template hpre hg i k ha hc]
    intro he
    cases he
  all_goals
    exact control_tmpl_ok hpre hg (d := ⟨_, i⟩) ha hi hc
      (by simp) (by simp) (by simp) (by simp) f

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbMma
