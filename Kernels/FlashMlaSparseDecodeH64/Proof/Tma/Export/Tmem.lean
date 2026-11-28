-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Quiet
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The TMA lane fires no `tcgen05` event

`tmemRow_tma`: no event of the TMA lane's shape table (`Tma/Ev.lean`, through `tma_at`) is a
`tcgen05` event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `TmemRow.Tma`**. -/
theorem tmemRow_tma (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : TmemRow.Tma P L X := by
  intro g k e c _ he hat hk
  obtain ⟨-, hr⟩ := hat
  obtain ⟨d, -, -, ⟨-, hE⟩, hl, -⟩ := tma_at hp hX hFw he (fun _ h => by rw [hk] at h; cases h) hr
  tma_state d
  cases s <;> simp [Tma.EvK, Tma.Poll, RdAt, hk] at hE
  case leave i => exact absurd rfl (hl i)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
