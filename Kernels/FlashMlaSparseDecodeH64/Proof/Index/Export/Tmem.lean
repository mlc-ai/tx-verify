-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Quiet
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The index warp fires no `tcgen05` event

`tmemRow_index`: no event of the index warp's shape table (`Index/Ev.lean`, through `index_at`)
is a `tcgen05` event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `TmemRow.Index`**. -/
theorem tmemRow_index (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : TmemRow.Index P L X := by
  intro g k e c _ he hat hk
  obtain ⟨-, hr1, hr2⟩ := hat
  obtain ⟨d, -, ⟨-, hE⟩, -⟩ :=
    index_at hp hX hFw he (fun _ h => by rw [hk] at h; cases h) ⟨hr1, hr2⟩
  obtain ⟨site, el, ac, c'⟩ := d
  cases site <;> simp [Index.EvK, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv,
      Index.StoreEv, hk] at hE

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
