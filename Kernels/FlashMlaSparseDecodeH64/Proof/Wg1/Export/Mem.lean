-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg1
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # Warpgroup 1's head and idle code: memory accesses

`memRow_wg1` (`MemRow.Wg1`): from the head's and the idle code's shape tables (`Wg1/Shape.lean`,
through `wg1_state`): the head's events are its `setmaxnreg` and its shuffle, the idle code's its
two length reads, its barrier and its return. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `MemRow.Wg1`**. -/
theorem memRow_wg1 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MemRow.Wg1 P L X := by
  intro g k e _ he hat hm
  have hub : ∀ f, e.kind ≠ .ub f := by
    rcases hm with ⟨a, bs, h⟩ | ⟨a, bs, h⟩ | ⟨a, bs, h⟩ | ⟨a, o, n, h⟩ <;> intro f hf <;>
      rw [h] at hf <;> cases hf
  obtain ⟨σ, -, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨-, -, hr⟩ := hat
  obtain ⟨pc, kd⟩ := e
  rcases wg1_state hJ hi hev hpc hr with ⟨s, hs, hev, -⟩ | ⟨s, hne, hev, -⟩
  · rcases hs with rfl | rfl <;>
      rcases hm with ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ <;>
      simp [Wg1.Ev] at hev
  · cases s with
    | ret => exact absurd rfl hne
    | _ =>
      rcases hm with ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ <;>
        simp [Wg1.IEv] at hev ⊢

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
