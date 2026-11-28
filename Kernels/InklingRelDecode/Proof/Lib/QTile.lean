-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Lemmas.Flow.Regs

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

/-- The swizzled byte offset of a thread's row inside one 2048-byte group of the query tile. -/
def qSwz (t : Nat) : Nat := ((16 * t) &&& 2032) ^^^ ((2 * t) &&& 112)

/-- The group (a multiple of 2048 bytes from the tile base) of the `m`-th query store. -/
def qGroup (m : Nat) : Nat := m % 2 * 4 + m / 2

theorem qSwz_spec : ∀ t < 128, qSwz t < 2048 ∧ qSwz t % 16 = 0 := by decide +kernel

theorem qGroup_lt : ∀ m < 8, qGroup m < 8 := by decide +kernel

theorem qGroup_inj : ∀ m < 8, ∀ m' < 8, qGroup m = qGroup m' → m = m' := by
  decide

theorem qSwz_inj : ∀ t < 128, ∀ t' < 128, qSwz t = qSwz t' → t = t' := by
  decide +kernel

/-- **The offset of a query store's byte determines the thread, the store and the element.** -/
theorem qOff_inj {m m' t t' w w' b b' : Nat} (hm : m < 8) (hm' : m' < 8) (ht : t < 128)
    (ht' : t' < 128) (hw : w < 4) (hw' : w' < 4) (hb : b < 4) (hb' : b' < 4)
    (h : 2048 * qGroup m + qSwz t + 4 * w + b =
      2048 * qGroup m' + qSwz t' + 4 * w' + b') :
    t = t' ∧ m = m' ∧ w = w' := by
  obtain ⟨s1, s2⟩ := qSwz_spec t ht
  obtain ⟨s1', s2'⟩ := qSwz_spec t' ht'
  have hg : qGroup m = qGroup m' := by omega
  have hs : qSwz t = qSwz t' := by omega
  exact ⟨qSwz_inj t ht t' ht' hs, qGroup_inj m hm m' hm' hg, by omega⟩

theorem qSwz_onto : ∀ s < 128, ∃ t < 128, qSwz t = 16 * s := by decide +kernel

theorem qGroup_onto : ∀ g < 8, ∃ m < 8, qGroup m = g := by decide

/-- **Every byte of the query tile is a byte of one query store.** -/
theorem qOff_onto {off : Nat} (h : off < 16384) : ∃ t m w b, t < 128 ∧ m < 8 ∧ w < 4 ∧ b < 4 ∧
    off = 2048 * qGroup m + qSwz t + 4 * w + b := by
  obtain ⟨m, hm, hg⟩ := qGroup_onto (off / 2048) (by omega)
  obtain ⟨t, ht, hs⟩ := qSwz_onto (off % 2048 / 16) (by omega)
  exact ⟨t, m, off % 16 / 4, off % 4, ht, hm, by omega, by omega, by omega⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
