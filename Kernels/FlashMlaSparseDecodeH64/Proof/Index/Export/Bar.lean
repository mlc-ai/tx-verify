-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Index
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The index warp's named barrier

`barRow_index`: the only named-barrier event of the index code is the CTA barrier
`barrier.sync 12` at pc 2585 over the whole CTA (384 threads, so the event records no count),
fired from the index state at its `bar` site (`index_at`, the shape table `Index/Ev.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `BarRow.Index`**: a barrier event of a warp-7 lane at a pc of the index code is
`everyone_sync` at 2585. -/
theorem barRow_index (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : BarRow.Index P L X := by
  intro g k e _ he hat hb
  obtain ⟨-, hr1, hr2⟩ := hat
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | bar b cnt mode =>
    obtain ⟨d, -, ⟨hpc, hk⟩, -⟩ := index_at hp hX hFw he (fun _ h => by cases h) ⟨hr1, hr2⟩
    obtain ⟨site, el, ac, c⟩ := d
    cases site <;>
      simp [Index.EvK, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv, Index.StoreEv] at hk
    case bar =>
      obtain ⟨rfl, rfl, rfl⟩ := hk
      exact ⟨hpc, rfl⟩
  | _ => simp [Execution.isBar] at hb

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
