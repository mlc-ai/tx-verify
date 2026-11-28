-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg1
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # Warpgroup 1's head and idle code name no mbarrier

`mbarRow_wg1`: an event of a warpgroup-1 lane at a pc of the head or the idle code is the head's
`setmaxnreg` or shuffle, or the idle code's loads (or their fault) or barrier
(`wg1_state`, `Common/Where.lean`), none of which names an mbarrier. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `MbarRow.Wg1`**. -/
theorem mbarRow_wg1 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MbarRow.Wg1 P L X := by
  intro g k e l _ he hat hm
  have no : ∀ kd : Kind, e.kind = kd → (∀ pc, ¬ Frame.MbarOf ⟨pc, kd⟩ l) → False := by
    intro kd hk h
    obtain ⟨pc, kd'⟩ := e
    simp only at hk
    subst hk
    exact h pc hm
  have hub : ∀ f, e.kind ≠ .ub f := fun f hk => no _ hk (by simp [Frame.MbarOf])
  obtain ⟨σ, -, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨-, -, hr⟩ := hat
  rcases wg1_state hJ hi hev hpc hr with ⟨s, hs, hev, -⟩ | ⟨s, hne, hev, -⟩
  · rcases hs with rfl | rfl
    · obtain ⟨inst, hk⟩ := hev
      exact no _ hk (by simp [Frame.MbarOf])
    · obtain ⟨r, ok, hk⟩ := hev
      exact no _ hk (by simp [Frame.MbarOf])
  · cases s with
    | ldA | ldB =>
      rcases hev with ⟨a, bs, hk⟩ | ⟨f, hk⟩
      · exact no _ hk (by simp [Frame.MbarOf])
      · exact hub f hk
    | bar => exact no _ hev (by simp [Frame.MbarOf])
    | ret => exact hne rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
