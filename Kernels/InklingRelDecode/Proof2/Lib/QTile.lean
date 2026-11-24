-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.FootQ

@[expose] public section

/-! # The address of a query store determines it

Moved from the first tree's `Interface/LpQTile.lean` (names and namespace unchanged): the offset
of a query store's byte in the Q tile, `2048 qGroup m + qSwz t + 4 w + b`, determines the thread
index `t`, the store `m` and the element `w` (`qOff_inj`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Kernels.InklingRelDecode.Proof

theorem qGroup_inj : ∀ m < 8, ∀ m' < 8, ProA.qGroup m = ProA.qGroup m' → m = m' := by
  decide

theorem qSwz_inj : ∀ t < 128, ∀ t' < 128, ProA.qSwz t = ProA.qSwz t' → t = t' := by
  decide +kernel

/-- **The offset of a query store's byte determines the thread, the store and the element.** -/
theorem qOff_inj {m m' t t' w w' b b' : Nat} (hm : m < 8) (hm' : m' < 8) (ht : t < 128)
    (ht' : t' < 128) (hw : w < 4) (hw' : w' < 4) (hb : b < 4) (hb' : b' < 4)
    (h : 2048 * ProA.qGroup m + ProA.qSwz t + 4 * w + b =
      2048 * ProA.qGroup m' + ProA.qSwz t' + 4 * w' + b') :
    t = t' ∧ m = m' ∧ w = w' := by
  obtain ⟨s1, s2⟩ := ProA.qSwz_spec t ht
  obtain ⟨s1', s2'⟩ := ProA.qSwz_spec t' ht'
  have hg : ProA.qGroup m = ProA.qGroup m' := by omega
  have hs : ProA.qSwz t = ProA.qSwz t' := by omega
  exact ⟨qSwz_inj t ht t' ht' hs, qGroup_inj m hm m' hm' hg, by omega⟩

end PTX.Kernels.InklingRelDecode.Proof.Lp
