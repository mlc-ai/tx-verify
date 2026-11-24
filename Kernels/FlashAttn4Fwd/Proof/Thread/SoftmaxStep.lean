-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSound
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithSpec
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax0
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithExp0
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax1
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithExp1
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Start
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Waits
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Stats1
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Stats2
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.LoadFirst
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.LoadFirst2
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.LoadLoop
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.LoadLoop2
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.LoadWaitFirst
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.LoadWaitLoop
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Item
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.PstFirst
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.PstLoop
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Publish
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Elect

@[expose] public section

/-! # The softmax warps' obligations as a code machine

Every event fired at a softmax state steps to the state `next` gives (`step_of`), given the
four arithmetic steps (`ArithSteps`, stated in `SoftmaxSteps/ArithSpec` and proved in
`SoftmaxSteps/ArithMax0`, `ArithExp0`, `ArithMax1`, `ArithExp1`): the exit's `ret` ends the
thread, so no step follows it. `stepAt` is the code machine's obligation for every state
(`code`, `site_ok`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A concrete state at a site of sub-step `0`. -/
theorem atS_at {d : D} {t : TState} (h : AtS L g d t) (hs : d.site.sub = 0) :
    At t d.site.pc (facts L g d) :=
  ⟨h.1, h.2.1.trans hs, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Every event fired at a softmax state steps to its successor. -/
theorem step_of (ar : ArithSteps) (hpre : Pre P L mem0) (hg : g < L.threads) {d : D}
    {t u : TState} {e : Event} {ins : Instr} (hi : Inv L g d) (h : AtS L g d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨s, i, tt, sc, m, l⟩ := d
  cases s with
  | setMaxReg => exact step_setMaxReg hpre rfl hi (atS_at h rfl) hc hf
  | bar0 => exact step_bar0 hpre hg rfl hi (atS_at h rfl) hc hf
  | statsW w =>
    rcases fin4_cases w with rfl | rfl | rfl | rfl
    · exact step_statsW0 hpre rfl hi (atS_at h rfl) hc hf
    · exact step_statsW1 hpre rfl hi (atS_at h rfl) hc hf
    · exact step_statsW2 hpre rfl hi (atS_at h rfl) hc hf
    · exact step_statsW3 hpre rfl hi (atS_at h rfl) hc hf
  | sW lp => exact step_sW hpre lp rfl hi (atS_at h rfl) hc hf
  | ld lp c =>
    by_cases hc2 : c.val < 2 <;> cases lp
    · exact step_ldFirst01 hpre c hc2 rfl hi (atS_at h rfl) hc hf
    · exact step_ldLoop01 hpre c hc2 rfl hi (atS_at h rfl) hc hf
    · exact step_ldFirst23 hpre c (by omega) rfl hi (atS_at h rfl) hc hf
    · exact step_ldLoop23 hpre c (by omega) rfl hi (atS_at h rfl) hc hf
  | ldW lp c =>
    by_cases hc3 : c.val < 3 <;> cases lp
    · exact step_ldW0 hpre c hc3 rfl hi h hc hf
    · exact step_ldW1 hpre c hc3 rfl hi h hc hf
    · obtain rfl : c = 3 := Fin.ext (by omega)
      exact ar.ldW3_gen0 hpre rfl hi h hc hf
    · obtain rfl : c = 3 := Fin.ext (by omega)
      exact ar.ldW3_alphaSt hpre rfl hi h hc hf
  | alphaSt => exact step_word hpre (.inl rfl) hi (atS_at h rfl) hc hf
  | gen j =>
    rcases fin3_cases j with rfl | rfl | rfl
    · exact ar.gen0_pst hpre rfl hi h hc hf
    · exact ar.gen1_pst hpre rfl hi h hc hf
    · exact step_gen2 hpre rfl hi (atS_at h rfl) hc hf
  | pst lp c =>
    cases lp
    · exact step_pst0 hpre c rfl hi (atS_at h rfl) hc hf
    · exact step_pst1 hpre c rfl hi (atS_at h rfl) hc hf
  | pwait lp hh => exact step_pwait hpre lp hh rfl hi (atS_at h rfl) hc hf
  | pArr lp => exact step_pArr hpre lp rfl hi (atS_at h rfl) hc hf
  | warpBar lp => exact step_warpBar hpre lp rfl hi (atS_at h rfl) hc hf
  | el lp => exact step_el hpre lp rfl hi (atS_at h rfl) hc hf
  | p2Arr lp => exact step_p2Arr hpre lp rfl hi (atS_at h rfl) hc hf
  | lSt => exact step_word hpre (.inr rfl) hi (atS_at h rfl) hc hf
  | barEnd => exact step_barEnd hpre rfl hi (atS_at h rfl) hc hf
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    simp [eventTmpl, Fires] at hf

/-- Every softmax state satisfies the code machine's obligation, given the arithmetic steps. -/
theorem stepAt_of (ar : ArithSteps) (hpre : Pre P L mem0) (hg : g < L.threads) (d : D) :
    (code asms L g).StepAt d where
  site _ := site_ok d
  step := by
    intro t e u ins h hi hc hf
    rcases step_of ar hpre hg hi h hc hf with ⟨hn, hd⟩ | ⟨d', t', hn, hr, ht, hi'⟩
    · exact .inr ⟨hn, hd⟩
    · exact .inl (.inr ⟨d', t', hn, hr, ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, hi'⟩)

/-- Every softmax state satisfies the code machine's obligation. -/
theorem stepAt (hpre : Pre P L mem0) (hg : g < L.threads) (d : D) : (code asms L g).StepAt d :=
  stepAt_of ⟨step_ldW3_gen0, step_gen0_pst, step_ldW3_alphaSt, step_gen1_pst⟩ hpre hg d

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
