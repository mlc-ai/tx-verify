-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Quiet
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # Warpgroup 2 fires no `tcgen05` event

`tmemRow_dequant`: no event of warpgroup 2's shape table (`Dequant/Ev.lean`, through
`dequant_at`) is a `tcgen05` event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `TmemRow.Dequant`**. -/
theorem tmemRow_dequant (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : TmemRow.Dequant P L X := by
  intro g k e c _ he hat hk
  obtain ⟨-, -, hlo, hhi⟩ := hat
  obtain ⟨d, -, ⟨-, hE⟩, -⟩ :=
    dequant_at hp hX hFw he (fun _ h => by rw [hk] at h; cases h) ⟨hlo, hhi⟩
  obtain ⟨site, el, ac, l0, l1, cnt', sb, pb⟩ := d
  cases site <;>
    simp [Dequant.EvK, Dequant.PollEv, Dequant.LoadEv, Dequant.StoreEv, hk] at hE

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
