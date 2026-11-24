-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.TmemGeometry
public import Lemmas.Flow.BitForms

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof

/-- The number of KV blocks reached by the two query stages of the selected tile. -/
def trips (p : Params) (batch tile : Nat) : Nat :=
  min ((p.kLength batch + 127) / 128)
    ((p.kLength batch - p.qLength batch + 256 * (tile + 1) + 127) / 128)

set_option maxRecDepth 3000 in
/-- A real tile has a first KV block. The signed arithmetic used by the trip count fits. -/
theorem trips_bounds {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {batch tile : Nat} (hb : batch < p.batch) (ht : 256 * tile < p.qLength batch) :
    0 < trips p batch tile ∧ trips p batch tile ≤ (p.kLength batch + 127) / 128 ∧
      p.kLength batch - p.qLength batch + 256 * (tile + 1) < 2 ^ 31 := by
  obtain ⟨_, hLen, hSigned⟩ := hp.lengths batch hb
  have hKey : 0 < (p.kLength batch + 127) / 128 := by omega
  have hCausal : 0 < (p.kLength batch - p.qLength batch + 256 * (tile + 1) + 127) / 128 := by
    omega
  have hInRange : p.kLength batch - p.qLength batch + 256 * (tile + 1) < 2 ^ 31 := by omega
  exact ⟨Nat.lt_min.mpr ⟨hKey, hCausal⟩, Nat.min_le_left _ _, hInRange⟩

/-- K and V alternate uses of a three-slot buffer. -/
def kvSlot (use : Nat) : Nat := use % 3

/-- The producer's full phase changes after each completed round of the three-slot buffer. -/
def kvParity (use : Nat) : Nat := use / 3 % 2

/-- The K-major Q or K descriptor slices the tile across the two 64-wide boxes. -/
def qkFragment (step : Fin 8) : Nat := 32 * (step.val % 4) + 16384 * (step.val / 4)

/-- Shared starts of the two physical Q tensors. -/
def qStart (l : Launch) (stage : Fin 2) : Nat := l.sharedBase + 3072 + 32768 * stage.val

/-- K and V occupy the same shared ring slot at different phases. -/
def kvStart (l : Launch) (use : Nat) : Nat := l.sharedBase + 68608 + 32768 * kvSlot use

/-- The fixed high word records a 1024-byte stride and 128-byte swizzling. -/
def sharedDescriptorWord (start leading : Nat) : Nat :=
  start / 16 + 2 ^ 16 * (leading / 16) + 2 ^ 32 * 0x40004040

/-- Physical operand descriptor, with the correct common stride and swizzle. -/
def sharedDescriptor (start leading : Nat) : TcShared.Descriptor :=
  ⟨start, leading, 1024, 0, false, false, .b128⟩

/-- The low-word mask preserves a 1024-aligned shared start in the precondition's address range. -/
theorem descriptorStart_mask {start : Nat} (hAlign : start % 1024 = 0) (hBound : start < 2 ^ 18) :
    start / 16 &&& 16320 = start / 16 := by
  have hEq : start / 16 = (start / 1024) <<< 6 := by
    rw [Nat.shiftLeft_eq]
    omega
  rw [hEq, show (16320 : Nat) = 255 <<< 6 by rfl, ← Nat.shiftLeft_and_distrib]
  have hi : start / 1024 < 2 ^ 8 := by omega
  change ((start / 1024) &&& (2 ^ 8 - 1)) <<< 6 = _
  rw [Nat.and_two_pow_sub_one_of_lt_two_pow hi]

private theorem decodeFields {w start leading : Nat}
    (hSw : w / 2 ^ 61 % 8 = 2) (hW : w < 2 ^ 64)
    (hR0 : w / 2 ^ 15 % 2 = 0) (hR1 : w / 2 ^ 31 % 2 = 0)
    (hVer : w / 2 ^ 46 % 8 = 1) (hR2 : w / 2 ^ 54 % 128 = 0)
    (hA : w % 2 ^ 15 * 16 = start) (hB : w / 2 ^ 16 % 2 ^ 15 * 16 = leading)
    (hStride : w / 2 ^ 32 % 2 ^ 14 * 16 = 1024) (hBase : w / 2 ^ 49 % 8 = 0)
    (hAbsolute : w / 2 ^ 52 % 2 = 0) (hLut : w / 2 ^ 53 % 2 = 0) :
    TcShared.decode w = some (sharedDescriptor start leading) := by
  simp only [TcShared.decode, hSw, TcShared.decodeSwizzle, hW, hR0, hR1, hVer, hR2,
    and_self, ↓reduceIte, hA, hB, hStride, hBase, hAbsolute, hLut, Nat.zero_ne_one,
    decide_false, sharedDescriptor]

private theorem overHigh {lo : Nat} (hLo : lo < 2 ^ 32) (d : Nat) :
    (lo + 2 ^ 32 * 0x40004040) / (2 ^ 32 * d) = 0x40004040 / d := by
  rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide),
    Nat.div_eq_of_lt hLo, Nat.zero_add]

private theorem belowHigh {lo d k : Nat} (hd : 0 < d) (hk : 2 ^ 32 = d * k) :
    (lo + 2 ^ 32 * 0x40004040) / d % k = lo / d % k := by
  calc
    _ = (lo + d * (k * 0x40004040)) / d % k := by rw [hk, Nat.mul_assoc]
    _ = (lo / d + k * 0x40004040) % k := by rw [Nat.add_mul_div_left _ _ hd]
    _ = _ := Nat.add_mul_mod_self_left _ _ _

private theorem clearReserved15 {lo start units : Nat} (hStart : start < 2 ^ 15)
    (hLo : lo = start + 2 ^ 16 * units) :
    (lo + 2 ^ 32 * 0x40004040) / 2 ^ 15 % 2 = 0 := by
  have hPacked : lo + 2 ^ 32 * 0x40004040 =
      start + 2 ^ 15 * (2 * (units + 2 ^ 16 * 0x40004040)) := by
    simp only [hLo, Nat.mul_add, ← Nat.mul_assoc]
    norm_num
    omega
  rw [hPacked, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hStart, Nat.zero_add]
  exact Nat.mul_mod_right _ _

private theorem descriptorLowFields {start leading : Nat}
    (hb : start < 2 ^ 18) (ha : start % 16 = 0) (hl : leading = 16 ∨ leading = 16384) :
    let lo := start / 16 + 2 ^ 16 * (leading / 16)
    let w := lo + 2 ^ 32 * 0x40004040
    lo < 2 ^ 32 ∧ w / 2 ^ 15 % 2 = 0 ∧ w / 2 ^ 31 % 2 = 0 ∧
      w % 2 ^ 15 * 16 = start ∧ w / 2 ^ 16 % 2 ^ 15 * 16 = leading := by
  intro lo w
  have hStart : start / 16 < 2 ^ 15 := by omega
  have hLeadUnits : leading / 16 ≤ 1024 := by rcases hl with rfl | rfl <;> decide
  have hLead16 : leading % 16 = 0 := by rcases hl with rfl | rfl <;> decide
  have hSmall : lo < 2 ^ 31 := by
    dsimp only [lo]
    exact ((Nat.add_lt_add_right hStart _).trans_le
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ hLeadUnits) _)).trans_le (by decide)
  have hLo : lo < 2 ^ 32 := hSmall.trans (by decide)
  have hR0 : w / 2 ^ 15 % 2 = 0 := clearReserved15 hStart rfl
  have hR1 : w / 2 ^ 31 % 2 = 0 := by
    change (lo + 2 ^ 32 * 0x40004040) / 2 ^ 31 % 2 = 0
    rw [belowHigh (by decide) (show 2 ^ 32 = 2 ^ 31 * 2 by rfl), Nat.div_eq_of_lt hSmall]
  have hA : w % 2 ^ 15 * 16 = start := by
    have h32 : w % 2 ^ 32 = lo := by
      change (lo + 2 ^ 32 * 0x40004040) % 2 ^ 32 = lo
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hLo]
    rw [← Nat.mod_mod_of_dvd w (show 2^15 ∣ 2^32 by decide), h32]
    dsimp only [lo]
    rw [show (2 : Nat)^16 = 2^15 * 2 from rfl, Nat.mul_assoc,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hStart]
    omega
  have hB : w / 2 ^ 16 % 2 ^ 15 * 16 = leading := by
    have hBits : w / 2 ^ 16 % 2 ^ 16 = lo / 2 ^ 16 % 2 ^ 16 :=
      belowHigh (by decide) rfl
    rw [← Nat.mod_mod_of_dvd (w / 2^16) (show 2^15 ∣ 2^16 by decide), hBits]
    dsimp only [lo]
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (by omega),
      Nat.zero_add, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  exact ⟨hLo, hR0, hR1, hA, hB⟩

/-- The assembled descriptor fits in the 64-bit operand lane. -/
theorem sharedDescriptorWord_lt {start leading : Nat}
    (hb : start < 2 ^ 18) (ha : start % 16 = 0) (hl : leading = 16 ∨ leading = 16384) :
    sharedDescriptorWord start leading < 2 ^ 64 := by
  have h := (descriptorLowFields hb ha hl).1
  exact (Nat.add_lt_add_right h _).trans_le (by norm_num)

/-- The physical descriptor fields used by both QK and PV are the fields decoded by Core. -/
theorem sharedDescriptor_decode {start leading : Nat}
    (hb : start < 2 ^ 18) (ha : start % 16 = 0) (hl : leading = 16 ∨ leading = 16384) :
    TcShared.decode (sharedDescriptorWord start leading) =
      some (sharedDescriptor start leading) := by
  let lo := start / 16 + 2 ^ 16 * (leading / 16)
  let w := sharedDescriptorWord start leading
  obtain ⟨hLo, hR0, hR1, hA, hB⟩ := descriptorLowFields hb ha hl
  have hLow : lo < 2 ^ 32 := hLo
  have hDiv (d : Nat) : w / (2 ^ 32 * d) = 0x40004040 / d := overHigh hLow d
  have hW : w < 2 ^ 64 := (Nat.add_lt_add_right hLow _).trans_le (by norm_num)
  have hSw : w / 2 ^ 61 % 8 = 2 := by
    rw [show (2 : Nat)^61 = 2^32 * 2^29 from rfl, hDiv]
    norm_num
  have hVer : w / 2 ^ 46 % 8 = 1 := by
    rw [show (2 : Nat)^46 = 2^32 * 2^14 from rfl, hDiv]
    norm_num
  have hR2 : w / 2 ^ 54 % 128 = 0 := by
    rw [show (2 : Nat)^54 = 2^32 * 2^22 from rfl, hDiv]
    norm_num
  have hStride : w / 2 ^ 32 % 2 ^ 14 * 16 = 1024 := by
    rw [show (2 : Nat)^32 = 2^32 * 1 from rfl, hDiv]
    norm_num
  have hBase : w / 2 ^ 49 % 8 = 0 := by
    rw [show (2 : Nat)^49 = 2^32 * 2^17 from rfl, hDiv]
    norm_num
  have hAbsolute : w / 2 ^ 52 % 2 = 0 := by
    rw [show (2 : Nat)^52 = 2^32 * 2^20 from rfl, hDiv]
    norm_num
  have hLut : w / 2 ^ 53 % 2 = 0 := by
    rw [show (2 : Nat)^53 = 2^32 * 2^21 from rfl, hDiv]
    norm_num
  exact decodeFields hSw hW hR0 hR1 hVer hR2 hA hB hStride hBase hAbsolute hLut

end PTX.Kernels.TmlFa4Fwd.Mma
