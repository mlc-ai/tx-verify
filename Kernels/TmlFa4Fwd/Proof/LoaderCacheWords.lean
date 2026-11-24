-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PagedKvGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX

/-- Each complete pair of live bytes belongs to one launch BF16 element. -/
def CacheWords (m : Mem0) (source : Acc) : Prop :=
  ∀ word, 2 * word + 1 < source.size →
    ∃ value : ℝ, HasValue m (source.loc.at (2 * word)) (.float .bf16 value)

theorem cacheWordsOfLayout {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {source : Acc} {page head row lane : Nat} (hPage : page < p.pages)
    (hHead : head < p.kvHeads) (hRow : row < 16) (value upper : Bool)
    (hSize : source.size ≤ 16)
    (hLoc : source.loc = (if value then p.vLayout else p.kLayout).loc
      page head row (kvCopyColumn lane upper)) : CacheWords m source := by
  intro word hWord
  have hByte : 2 * word < 16 := by omega
  have hColumn := kvCopyColumn_byte_lt (lane := lane) upper hByte
  have hColumn' : kvCopyColumn lane upper + word < 128 := by
    simpa only [Nat.mul_div_cancel_left _ (by decide : 0 < 2)] using hColumn
  have hInit := hp.kvBytes page hPage head hHead row hRow _ hColumn'
  rw [hLoc, CacheLayout.loc_copy_byte]
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2), Nat.mul_mod_right, Loc.at, Nat.add_zero]
  cases value
  · exact ⟨_,hInit.1⟩
  · exact ⟨_,hInit.2⟩

end PTX.Kernels.TmlFa4Fwd.Loader
