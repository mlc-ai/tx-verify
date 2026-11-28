-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Protocol.NamedBarSources

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0}

/-- The four data warps are among the warps of the CTA. -/
theorem group_sub (hp : Pre Q L m) :
    Finset.range 4 ⊆ Finset.range (CtaBarrier.warps L.block) := by
  intro w hw
  simp only [Finset.mem_range, CtaBarrier.warps, hp.block] at hw ⊢
  omega

/-- The data group is not the whole CTA. -/
theorem group_ne (hp : Pre Q L m) : 4 ≠ CtaBarrier.warps L.block := by
  simp [CtaBarrier.warps, hp.block]

/-- The count 128 decodes to the four data warps. -/
theorem group_target : CtaBarrier.target L.block (some 128) = .ok 4 := by
  simp [CtaBarrier.target]

/-- **The loop group of barrier 0**: the four data warps, passing the count 128. -/
theorem loop_shape (hp : Pre Q L m) : NamedBar.Shape L (some 128) (Finset.range 4) 0 := by
  have hb : L.block = 256 := hp.block
  refine ⟨by simp, by simp [CtaBarrier.target], ?_, by decide⟩
  intro w hw
  simp only [Finset.mem_range, hb] at hw ⊢
  omega

/-- **The whole-CTA group of barrier 0**: all eight warps, without a count. -/
theorem all_shape (hp : Pre Q L m) :
    NamedBar.Shape L none (Finset.range (CtaBarrier.warps L.block)) 0 := by
  have hb : L.block = 256 := hp.block
  refine ⟨?_, by simp [CtaBarrier.target], ?_, by decide⟩
  · simp [CtaBarrier.warps, hb]
  · intro w hw
    simp only [Finset.mem_range, CtaBarrier.warps, hb] at hw ⊢
    omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
