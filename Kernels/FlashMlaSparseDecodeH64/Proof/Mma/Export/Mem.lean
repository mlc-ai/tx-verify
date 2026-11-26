-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The MMA warp's memory accesses

`memRow_mma` (`MemRow.Mma`): from the shape table (`Mma/Ev.lean`, through
`mma_at`), case by site. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A memory event is no undefined behaviour. -/
private theorem memEvent_ub {e : Event} (hm : MemRow.MemEvent e) : ∀ f, e.kind ≠ .ub f := by
  rcases hm with ⟨a, bs, h⟩ | ⟨a, bs, h⟩ | ⟨a, bs, h⟩ | ⟨a, o, n, h⟩ <;> intro f hf <;>
    rw [h] at hf <;> cases hf

/-- **Row `MemRow.Mma`**. -/
theorem memRow_mma (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MemRow.Mma P L X := by
  intro g k e _ he hat hm
  obtain ⟨-, hlo, hhi⟩ := hat
  obtain ⟨d, -, ⟨-, hE⟩, hl, -⟩ := mma_at hp hX hFw he (memEvent_ub hm) ⟨hlo, hhi⟩
  obtain ⟨site, l0, l1, neg, cnt', pha, par⟩ := d
  obtain ⟨pc, kd⟩ := e
  rcases hm with ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ <;>
    cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE ⊢
  all_goals exact absurd rfl (hl _)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
