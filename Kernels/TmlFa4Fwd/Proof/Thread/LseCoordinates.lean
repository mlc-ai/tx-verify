-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseIssuer

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX

/-- The actual global scalar writer carries its scheduled request, head, tile and row. -/
theorem lseStoreAssigned {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {bytes : List Byte} (hw : X.Writes i a bytes)
    (hGlobal : a.loc.space = .global) :
    TmlFa4Fwd.Correction.AssignedLseFootprint p l (i.1 / l.block) i.1 a ∧
      8 ≤ Prologue.warpIndex l i.1 ∧ Prologue.warpIndex l i.1 < 12 := by
  have hw' : X.MemWrites (.thread i) a bytes := .inl hw
  rcases globalWriteSources hX hw' hGlobal with
    ⟨j, site, hRef, hSite, hGet⟩ | ⟨_, _, _, _, _, _, _, hRef, _⟩
  · obtain rfl := AsyncCopy.Ref.thread.inj hRef
    exact ⟨TmlFa4Fwd.Correction.lseStoreAssignment hp hX hSite hGet,
      TmlFa4Fwd.Correction.lseStoreWarp hp hX hGet hSite⟩
  · cases hRef

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
