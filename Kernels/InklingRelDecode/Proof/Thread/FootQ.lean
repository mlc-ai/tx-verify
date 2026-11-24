-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.FootOps
public import Kernels.InklingRelDecode.Proof.Thread.EvDProStore

@[expose] public section

/-!
# The footprint of the prologue's query stores

The eight `st.shared.v4.b32` of the prologue write the thread's 16-byte vectors into the query
tile `[sharedBase + 196608, sharedBase + 212992)`. Store `m` writes at

`qStoreBase L g dt m = sharedBase + 196608 + 2048 (4 (m % 2) + m / 2) + qSwz (tid)`

where `qSwz t = ((16 t) &&& 2032) ^^^ ((2 t) &&& 112)` is the 128-byte swizzle of the thread's
row: a multiple of 16 below 2048 for `t < 128`. So the four elements of a store (`qStoreBase + 4 w`,
`w < 4`) lie in the query tile, and the store never touches the Tensor Memory base word, the pair
`(num_pre, num_iters)` or the role table (`qStoreBase_range`, `shape_stq_foot`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

/-- The swizzled byte offset of a thread's row inside one 2048-byte group of the query tile. -/
def qSwz (t : Nat) : Nat := ((16 * t) &&& 2032) ^^^ ((2 * t) &&& 112)

/-- The group (a multiple of 2048 bytes from the tile base) of the `m`-th query store. -/
def qGroup (m : Nat) : Nat := m % 2 * 4 + m / 2

theorem qSwz_spec : ∀ t < 128, qSwz t < 2048 ∧ qSwz t % 16 = 0 := by decide +kernel

theorem qGroup_lt : ∀ m < 8, qGroup m < 8 := by decide +kernel

theorem c4_nat : BitVec.ofInt 64 4 = BitVec.ofNat 64 4 := by rw [nf_ofInt]; rfl
theorem c1_nat : BitVec.ofInt 64 1 = BitVec.ofNat 64 1 := by rw [nf_ofInt]; rfl
theorem c2032_nat : BitVec.ofInt 64 2032 = BitVec.ofNat 64 2032 := by rw [nf_ofInt]; rfl
theorem c112_nat : BitVec.ofInt 64 112 = BitVec.ofNat 64 112 := by rw [nf_ofInt]; rfl

/-- The register the eight stores add their group offsets to: the shared base plus the swizzled
row offset of the thread. -/
theorem v_r330_eq (L : Launch) (g : Nat) (dt : Dat) (ht : tidOf L g < 128) (hs : SbRoom L) :
    v_r330 L g dt = BitVec.ofNat 64 (L.sharedBase + qSwz (tidOf L g)) := by
  have h2 := qSwz_spec _ ht
  have f1 : tidOf L g % 4294967296 * 16 % 4294967296 = 16 * tidOf L g := by omega
  have f2 : tidOf L g % 4294967296 * 2 % 4294967296 = 2 * tidOf L g := by omega
  have e4 : 16 * tidOf L g &&& 2032 < 4294967296 :=
    lt_of_le_of_lt Nat.and_le_right (by omega)
  have e5 : 2 * tidOf L g &&& 112 < 4294967296 := lt_of_le_of_lt Nat.and_le_right (by omega)
  have e6 : L.sharedBase % 4294967296 = L.sharedBase :=
    Nat.mod_eq_of_lt (by unfold SbRoom at hs; omega)
  simp only [v_r330, v_r329, v_r326, v_r328, v_r325, v_r327, v_r1, v_r205_eq, c4_nat, c1_nat,
    c2032_nat, c112_nat, wShl32_ofNat _ _ (by norm_num : 4 < 32),
    wShl32_ofNat _ _ (by norm_num : 1 < 32), wAnd32_ofNat, wXor32_ofNat, wAdd32_ofNat]
  congr 1
  simp only [Nat.reducePow, Nat.mod_mod, Nat.reduceMod]
  rw [f1, f2, Nat.mod_eq_of_lt e4, Nat.mod_eq_of_lt e5, e6]
  have := h2.1
  unfold qSwz at this ⊢
  exact Nat.mod_eq_of_lt (by unfold SbRoom at hs; omega)

/-- The address register of store `m` is the common register plus the store's constant. -/
theorem stq_base_reg (L : Launch) (g : Nat) (dt : Dat) {m : Nat} (hm : m < 8) :
    ∃ c : Nat, c = 196608 + 2048 * qGroup m ∧
      valueOf L g dt (gloadBase (stqSite (4 * m)).pc) =
        .bits 32 (wAdd32 (v_r330 L g dt) (BitVec.ofInt 64 (c : Int))) := by
  interval_cases m
  all_goals exact ⟨_, rfl, rfl⟩

/-- **The closed form of `qStoreBase`**: store `m` writes at the group `qGroup m` of the query
tile, at the swizzled offset of the thread's row. -/
theorem qStoreBase_form (L : Launch) (g : Nat) (dt : Dat) (ht : tidOf L g < 128) (hs : SbRoom L)
    {m : Nat} (hm : m < 8) :
    qStoreBase L g dt m = L.sharedBase + 196608 + 2048 * qGroup m + qSwz (tidOf L g) := by
  obtain ⟨c, hc, hv⟩ := stq_base_reg L g dt hm
  have hg := qGroup_lt m hm
  have h2 := qSwz_spec _ ht
  have hlt : L.sharedBase + 196608 + 2048 * qGroup m + qSwz (tidOf L g) < 2 ^ 32 := by
    unfold SbRoom at hs
    omega
  unfold qStoreBase
  rw [hv, v_r330_eq L g dt ht hs, ofInt_ofNat, wAdd32_ofNat]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : (L.sharedBase + qSwz (tidOf L g) + c) % 2 ^ 32 < 2 ^ 64)]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- **The query stores stay in the query tile**: element `w` of store `m` is at
`qStoreBase + 4 w`, and its four bytes are in `[sharedBase + 196608, sharedBase + 212992)`. -/
theorem qStoreBase_range (L : Launch) (g : Nat) (dt : Dat) (ht : tidOf L g < 128) (hs : SbRoom L)
    {m : Nat} (hm : m < 8) :
    L.sharedBase + 196608 ≤ qStoreBase L g dt m ∧ qStoreBase L g dt m + 16 ≤ L.sharedBase + 212992 ∧
      qStoreBase L g dt m % 16 = L.sharedBase % 16 := by
  rw [qStoreBase_form L g dt ht hs hm]
  have hg := qGroup_lt m hm
  have h2 := qSwz_spec _ ht
  refine ⟨by omega, by omega, by omega⟩

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- **A query store's footprint.** Element `w` of store `m` writes the four bytes at
`qStoreBase + 4 w` of the thread's CTA, and the whole 16-byte vector lies in the query tile
`[sharedBase + 196608, sharedBase + 212992)`. -/
theorem shape_stq_foot {m w : Nat} (hm : m < 8) (hw : w < 4) (ht : tidOf L g < 128)
    (hs : SbRoom L) (hF : Fired L g d e (some u)) (hsite : d.site = stqSite (4 * m + w)) :
    ∃ v' bs a, storeValue 32 (qWord d.dt (4 * m + w)) = .ok v' ∧
      e = ⟨evPc d.site, .wr a bs⟩ ∧
      a.loc = ⟨.shared, g / L.block, qStoreBase L g d.dt m + 4 * w⟩ ∧ a.size = 4 ∧
      L.sharedBase + 196608 ≤ a.loc.addr ∧ a.loc.addr + 4 ≤ L.sharedBase + 212992 := by
  obtain ⟨v', hv, he⟩ := shape_stq hm hw hF hsite
  refine ⟨v', _, _, hv, he, rfl, rfl, ?_, ?_⟩
  · have := (qStoreBase_range L g d.dt ht hs hm).1
    show L.sharedBase + 196608 ≤ qStoreBase L g d.dt m + 4 * w
    omega
  · have := (qStoreBase_range L g d.dt ht hs hm).2.1
    show qStoreBase L g d.dt m + 4 * w + 4 ≤ L.sharedBase + 212992
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
