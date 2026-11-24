-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LkBar
public import Kernels.InklingRelDecode.Proof.Safety.Aligned

@[expose] public section

/-!
# `barLanes` and the divergence half of `barAligned`, from the lockstep of the lanes

The lanes of a warp run the synchronizing events of the kernel in lockstep (`Interface/LkSkel`,
`LkMachine`): at their `n`-th synchronizing events they are at one site, given that they agree
on the few values that steer a branch between two synchronizing events (`LaneAgree`: the prologue's
three guards of the request's `num_pre`, the role byte, the loader's and the MMA warp's loop
counters, the lazy-rescale decision `min(alpha) >= 1`). From it:

* `barLanes`: two lanes of a warp at their `k`-th barrier event are at one barrier instruction,
  so agree on the barrier id and the thread count (the kernel has no `bar.arrive`, so this is all
  of `BarMismatch`);
* `AlignedClass.bar.Divergent`: they agree on the source position, and the class has no operands.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bar
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (LaneAgree lock_kernel bar_agree)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Safety.Protocol.barLanes`**: the lanes of a warp agree on the barrier and the thread count
at each barrier ordinal. -/
theorem barLanes_of_agree (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hA : LaneAgree Q L X) : ¬ Safety.BarLaneMismatch L X := by
  rintro ⟨g, h, i, j, id, id', count, count', pc, pc', hw, hi, hj, hcnt, hne⟩
  obtain ⟨-, h1, h2⟩ := bar_agree hpre hX hS ht (lock_kernel ht hA) hw hi hj hcnt
  rcases hne with hne | hne
  · exact hne h1
  · exact hne h2

/-- **The divergence half of `Safety.Protocol.barAligned`**: the lanes of a warp make their
`k`-th barrier event at one source position. -/
theorem barDivergent_not_of_agree (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hA : LaneAgree Q L X) : ¬ AlignedClass.bar.Divergent L kernel X := by
  rintro ⟨e, f, pe, pf, ke, kf, hw, he, hf, hme, hmf, hord, -, hne⟩
  simp only [AlignedClass.member, Execution.isBar] at hme hmf
  cases ke <;> simp at hme
  cases kf <;> simp at hmf
  rename_i id c m id' c' m'
  obtain ⟨hp, -, -⟩ := bar_agree hpre hX hS ht (lock_kernel ht hA) hw he hf hord
  rcases hne with hne | hne
  · exact hne hp
  · simp [AlignedClass.operands] at hne

end
end PTX.Kernels.InklingRelDecode.Proof.Bar
