-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Bar9
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.SyncId
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Out
import Lemmas.Protocol.ClusterTrace

@[expose] public section

/-! # Barrier 9 orders warpgroup 0's accesses by their barrier counts

Two lanes `u`, `v` of warpgroup 0 in one CTA, `u` at an event that is no barrier-9 event after
`n` of its barrier-9 events and `v` at an event after more than `n` of its own: the event of `u`
is ordered before the one of `v` (`bar9_order`). Both lanes made their `n`-th barrier-9 event
(`v` before its event, `u` since it exits only past its `2 R + 6` events, `wg0_outExit`, and
otherwise by the released generation), and arrivals of one ordinal synchronize
(`Sources.same_ordinal_baseCausality`, as for the output publication `out_pub`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow ClusterTrace

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Barrier 9 orders the lanes of warpgroup 0**: `u`'s event, not a barrier-9 event, after `n`
of its barrier-9 events and below `2 R + 6`, is before `v`'s event after more than `n`. -/
theorem bar9_order (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : BarRows P L X) {u v i k : Nat} {e : Event}
    (hs : SameCta L u v) (hu : warp L u < 4) (hi : X.get (u, i) = some e)
    (hnb : Execution.isBarId 9 e = false) (hk : k < (X.tr v).length)
    (hlt : ((X.tr u).take i).countP (Execution.isBarId 9) <
      ((X.tr v).take k).countP (Execution.isBarId 9))
    (hb : ((X.tr u).take i).countP (Execution.isBarId 9) < 2 * blocksOf P L (u / L.block) + 6) :
    baseCausality L X (u, i) (v, k) := by
  have hmem : barIn 9 ((u % L.block) / 32) = true := by
    simp only [warp, tidOf_x_eq hp] at hu
    simp only [barIn, ite_true, decide_eq_true_eq]
    rw [hp.block]
    exact hu
  exact barId_order hp hX hR hs hmem hi hnb hk hlt fun j pcx hx => by
    have h6 := wg0_outExit hp hX hFw hu hx
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
