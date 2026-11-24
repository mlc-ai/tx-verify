-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Correction
public import Kernels.TmlFa4Fwd.Proof.CorrectionObservedRescaleEntry
public import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.AsyncCopy

/-- Issuing an ordinary shared proxy fence follows an earlier event in the same lane. -/
theorem scoreWaitBeforeProxyFence {X : Execution} {score wait fence : Nat}
    (hFence : X.IsProxyFence (score, fence) (.async (some (.shared .cta))) none)
    (hEarlier : wait < fence) : po X (score, wait) (score, fence) := by
  obtain ⟨_, hGet⟩ := hFence
  exact po_of_not_access rfl hEarlier (len_of_get hGet) (by rw [hGet]; rfl)

end PTX.Kernels.TmlFa4Fwd.Thread
