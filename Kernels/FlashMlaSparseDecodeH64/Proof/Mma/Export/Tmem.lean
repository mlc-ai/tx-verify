-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The MMA warp's `tcgen05` events

`tmemRow_mma`: a `tcgen05` event of the MMA warp is the fence, a `128x256b` copy to its column, a
commit of group one or an MMA with its Tensor Memory operands (the shape table `Mma/Ev.lean`,
through `mma_at`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `TmemRow.Mma`**. -/
theorem tmemRow_mma (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : TmemRow.Mma P L X := by
  intro g k e c _ he hat hk
  obtain ⟨-, hlo, hhi⟩ := hat
  obtain ⟨d, -, ⟨hpc, hE⟩, hl, -⟩ :=
    mma_at hp hX hFw he (fun _ h => by rw [hk] at h; cases h) ⟨hlo, hhi⟩
  have hnu : ∀ f, e.kind ≠ .ub f := fun _ h => by rw [hk] at h; cases h
  obtain ⟨site, l0, l1, neg, cnt', pha, par⟩ := d
  unfold TmemRow.MmaTc
  cases site
  case qCopy i =>
    rcases hE with ⟨s, h1, h2, h3, h4, h5, -⟩ | ⟨f, hf⟩
    · exact .inr (.inl ⟨s, i.val, i.isLt, hpc, h1, h2, h3, h4, h5⟩)
    · exact absurd hf (hnu f)
  case qk i =>
    rcases hE with ⟨s, h1, h2, h3, h4, -⟩ | ⟨f, hf⟩
    · exact .inr (.inr (.inr (.inl ⟨s, i.val, i.isLt, hpc, h1, h2, h3, h4⟩)))
    · exact absurd hf (hnu f)
  case pv i =>
    rcases hE with ⟨s, h1, h2, h3, h4, -⟩ | ⟨f, hf⟩
    · refine .inr (.inr (.inr (.inr ⟨s, _, i.val, i.isLt, hpc, h1, fun h => ?_, h2, h3, h4⟩)))
      simp only [Mma.pvAcc, show ¬ i.val < 2 by omega, ↓reduceIte]
    · exact absurd hf (hnu f)
  case leave i => exact absurd rfl (hl i)
  all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, hk] at hE
  case qFence | qCopyFence | kvFence | soFence => subst hE; exact .inl hk
  case qCopyCommit | qkCommit | pvCommit =>
    obtain ⟨s, rfl, -, h2, -⟩ := hE; exact .inr (.inr (.inl ⟨s, hk, h2⟩))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
