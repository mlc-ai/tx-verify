-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WpCore
public import Kernels.InklingRelDecode.Proof.Interface.Lk5VCount

@[expose] public section

/-!
# The softmax region's `s_ready` polls, met through the shuffles

A thread of the default partition at the softmax region's `waitS` of iteration `i` has made
`1 + num_pre + smBase i` shuffles (`Lk.cnt_inv`; `smBase` counts the iterations' shuffles, three in
the first and nine in each later one). That number grows with the iteration, and `num_pre` is the
CTA's. So of two lanes of a warp at `waitS`, the lane in the earlier iteration has made fewer
shuffles than the other, and `meet_shfl` orders its poll before the other's (`soft_met`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Interface.Lk

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem smBase_lt {i j : Nat} (h : i < j) : Sm.smBase i < Sm.smBase j := by
  unfold Sm.smBase
  split <;> split <;> omega

/-- The shuffles of a thread at `waitS` of iteration `i`. -/
theorem waitS_cnt (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {d : Sm.D} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .waitS) : cnt Execution.isShfl X g k = 1 + NP Q L g + Sm.smBase d.i := by
  rw [(cnt_inv hpre hX hf hg k hk hσ).1]
  simp [cntF, Sm.smW, Sm.smOff, hs]

/-- **Two lanes of a warp at the softmax region's `waitS`**: the poll of the lane in the earlier
iteration is ordered before the other's. -/
theorem soft_met (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hA : LaneAgree Q L X) {g h k k' : Nat} {e : Event}
    {d d' : Sm.D} (hw : SameWarp L g h) (he : X.get (g, k) = some e)
    (hne : Execution.isShfl e = false) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .waitS) (hσ' : St Q L X h k' = some (some (.d (.sm d'))))
    (hs' : d'.site = .waitS) (hk' : k' < (X.tr h).length) (hlt : d.i < d'.i) :
    PollBefore L kernel X (g, k) (h, k') := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have h1 := waitS_cnt hpre hX hf hw.1.1 (by omega) hσ hs
  have h2 := waitS_cnt hpre hX hf hw.1.2.1 (by omega) hσ' hs'
  have hc : g / L.block = h / L.block := hw.1.2.2
  have hnp : NP Q L g = NP Q L h := by simp only [NP, ProA.cta, hc]
  have h3 := smBase_lt hlt
  exact meet_shfl hX hf hA hw he hne (le_of_eq h1) (by omega) hk'

end
end PTX.Kernels.InklingRelDecode.Proof.Wp
