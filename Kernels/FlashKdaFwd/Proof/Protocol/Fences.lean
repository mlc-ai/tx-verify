-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.Layout
public import Lemmas.Protocol.StagingCounts

@[expose] public section

/-! # Proxy fences and bulk-group waits: how a buffer changes hands

The copy engine ("TMA")
accesses shared memory through the *asynchronous proxy*; a thread accesses it through the
generic proxy. The model orders a thread access before a later asynchronous access of the same
byte only through a `fence.proxy.async` on a base-causality path from the access to the issue
of the asynchronous operation, and orders the source reads of an asynchronous store before a
later thread write only through a `cp.async.bulk.wait_group.read` that covers the store.

The four ways a buffer of this kernel changes hands are the four lemmas of the library file
`Lemmas/Protocol/StagingCounts.lean` (written with this kernel, generic over the kernel):

* `Staging.publish_of_unit`: **thread access → fence → release arrival → acquire poll →
  issue**, through the unit hand-off of an mbarrier. Used with `storeFull o` (output writes
  before the stores that read them: `StoreFacts.publish_output`) and with `loadEmpty s` (input
  reads before the next loads into the buffer: `LoadFacts.publish_input`); the fence is 2914
  in both.
* `Staging.release_of_unit`: **store issue → `.read` group wait → release arrival → acquire
  poll → thread write**. Used with `storeEmpty o` (`StoreFacts.release_output`; the wait is
  3093).
* `Staging.publish_of_handoff`, here `publish_of_bar`: **thread access → fence → `bar.sync 0` →
  issue.** Used for the added fence 1401 (reads of the FP32 state buffer before the first
  loads into the bytes they alias) and for the fence 3774 (final-state writes before the
  final-state stores).
* `Staging.release_of_handoff`, here `release_of_bar`: **store issue → `.read` group wait →
  `bar.sync 0` → thread write.** Used for the output stores of the last tiles before the
  final-state writes into the same bytes. -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **Publication through the CTA barrier.** A proxy fence of thread `g` after its access, with
fewer `bar.sync 0` up to it than thread `h` of the same CTA has before its issue. -/
theorem publish_of_bar
    (H : Handoff L X (fun g h => SameCta L g h) (bar0UpTo X) (bar0Before X))
    {g i f h k pcf : Nat} {p : Part} {l : Loc} (hif : i < f)
    (hfget : X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩)
    (hsame : SameCta L g h) (hk : k < (X.tr h).length)
    (hlt : bar0UpTo X (g, f) < bar0Before X (h, k))
    (hl : l.space = .shared) (hlc : l.cta = g / L.block) (hcov : AsyncCovers X (h, k) p l) :
    modelCausality L X l (.thread (g, i)) (.async (h, k) p) :=
  Staging.publish_of_handoff H hif hfget hsame hsame hk hlt hl hlc hcov

/-- **Release through the CTA barrier.** A `.read` bulk-group wait of thread `h` that covers its
store, with fewer `bar.sync 0` up to it than thread `g` of the same CTA has before its
access. -/
theorem release_of_bar (hX : Consistent L K A mem0 X)
    (H : Handoff L X (fun g h => SameCta L g h) (bar0UpTo X) (bar0Before X))
    {h k w g i : Nat} {x y z : Nat} {l : Loc} (hwait : BulkWaitsFor X .read (h, k) (h, w))
    (hw : w + 1 < (X.tr h).length) (hsame : SameCta L h g) (hlen : i < (X.tr g).length)
    (hlt : bar0UpTo X (h, w) < bar0Before X (g, i))
    (hcov : AsyncCovers X (h, k) (.read (.store x y z)) l) :
    modelCausality L X l (.async (h, k) (.read (.store x y z))) (.thread (g, i)) :=
  Staging.release_of_handoff hX H hwait hw hsame hlen hlt hcov

end PTX.Kernels.FlashKdaFwd.Protocol
