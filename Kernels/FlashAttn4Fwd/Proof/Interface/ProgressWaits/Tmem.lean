-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Time

@[expose] public section

/-! # What the thread layer exports for the progress of the paired Tensor Memory operations

Warp 12 of each CTA of a cluster makes the pair's three resource operations (`TmemFacts.event`):
the allocation (site `alloc`, time `allocT`), the relinquishment (`relinquish`, the tail's
`mmaTail n T 0`) and the deallocation (`dealloc`, `mmaTail n T 22`). Both CTAs of a cluster run
the same items, so the `n`-th operation of every lane of the pair's two warps is at one time.
Within the MMA role the times follow the program order, so a lane that has made at most `n`
operations is at a state no later than that time (`lag`). (After an operation, a warp-collective
`tcgen05` event, the thread is at a later state: `TcWaitFacts.after`.)

The fields are facts of single threads' events, from the prologue's and the MMA role's run
invariants and the site table `Progress.Time.mma`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof Tmem.Pair

noncomputable section

/-- The thread layer's facts for the progress of the paired Tensor Memory operations. -/
structure TmemWaitFacts (L : Launch) (X : Execution) : Prop where
  /-- A lane of warp 12 of a CTA of the pair of thread `g`'s CTA that has made at most `n`
  operations is no later (`endTime`) than the state of `g` before its `n`-th operation. -/
  lag : ∀ {g h j n : Nat} {d : ThreadD}, g < L.threads → h < L.threads →
    warpOf L h = 12 → ctaOf L h / 2 = ctaOf L g / 2 →
    (∃ pc grp dst act, X.get (g, j) = some ⟨pc, .tc (.resource grp dst act)⟩) →
    tmemOps ((X.tr g).take j) = n → St L X g j = some (some d) →
    tmemOps (X.tr h) ≤ n → endTime L X h ≤ stateTime L g d

end
end PTX.Kernels.FlashAttn4Fwd.Proof
