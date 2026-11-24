-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateReadyAlign
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateWriter

@[expose] public section

/-! # A coordinate load has an ordered publication of its exact bytes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Proof PTX.Flow PTX.AsyncCopy PTX.MbarRing PTX.MBarrier
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Each coordinate load has an actual same-block writer and its exact published bytes,
ordered before the read by the observed ready release. -/
theorem coordinate_publication_with_writer {g i : Nat} {d : Wg1Tma.D}
    {e : Event} {k : Fin 16} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.code P L a).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hSite : d.site = .coord k j)
    :
    ∃ a bs w aw, e.kind = .rd a bs ∧ a.size = 4 ∧ a.loc = aw.loc ∧ aw.size = 4 ∧
      X.MemWrites (.thread w) aw (b32 (Wg1Tma.coordAt P L g d.block
        (Wg1Tma.coordPos k.val j.val))).toBytes ∧ baseCausality L X w (g, i) ∧
      ∃ (z : Wg1Index.D) (extra high : Bool),
        Frame.stateAt (Machine.code P L) X w.1 w.2 = some (some (.index z)) ∧
        z.site = .coord extra high ∧ z.block = d.block := by
  apply coordinate_writer_of_aligned_releases hpre hX hs he hd hSite
  intro q h t z extra _ hCount
  exact coordinate_ready_sources_aligned hpre hX hs he hd hSite hCount


end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
