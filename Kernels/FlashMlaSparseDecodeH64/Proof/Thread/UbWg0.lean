-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbRoles
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbWg0Barriers
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbWg0Data
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbWg0Inputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbWg0LoopControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbWg0Output

public section

/-! # Defined softmax templates and live continuations -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbWg0

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem site_coverage (s : Wg0.Site) :
    (s = .sink ∨ s = .lenOrig ∨ s = .lenExtra) ∨ (LoopPlain s ∨ LoopMbar s) ∨
      LoopBarrier s ∨ DataSite s ∨ OutputSite s := by
  cases s <;> simp [LoopPlain, LoopMbar, LoopBarrier, DataSite, OutputSite]

/-- All live softmax event templates are defined. -/
theorem tmpl_ok (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) :
    (Wg0.code P L g).TmplOk := by
  intro d t ins ha hi hc f
  have hcover := site_coverage (Wg0.D.site d)
  rcases hcover with hInput | hCtrl | hBar | hData | hOut
  · exact input_tmpl_ok hpre ha hi hc hInput f
  · exact loop_control_tmpl_ok hpre ha hi hc hCtrl f
  · exact barrier_tmpl_ok hpre ha hi hc hBar f
  · exact data_tmpl_ok hpre hg ha hi hc hData f
  · exact output_tmpl_ok hpre hg ha hi hc hOut f

/-- All returned softmax events keep a represented successor. -/
theorem next_live (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) : UbRoles.SoftmaxContinues P L X := by
  intro g i d e he hd hReturns
  rcases site_coverage d.site with hInput | hCtrl | hBar | hData | hOut
  · exact input_next_live hpre hX hs he hd hInput
  · exact loop_control_next_live hpre hX hs he hd hCtrl
  · exact barrier_next_live hpre hX hs he hd hBar
  · exact data_next_live hpre hX hs he hd hData
  · exact output_next_live hpre hX hs he hd hOut hReturns

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbWg0
