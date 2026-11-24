-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd

noncomputable section

/-- The loader shuffle mask keeps the upper two warp-lane bits and selects one of eight
lanes inside that group. -/
theorem kv_shuffle_source (lane : Fin 32) (source : Fin 8) :
    shflSource .idx lane.val source.val 6175 = (8 * (lane.val / 8) + source.val, true) := by
  revert lane source
  decide

/-- The first element of the eight-element BF16 vector copied by the loader lane. -/
def kvCopyColumn (lane : Nat) (upper : Bool) : Nat :=
  8 * (lane % 8) + if upper then 64 else 0

/-- The row copied at one of the sixteen source predicates of a loader group. -/
def kvCopyRow (tile lane group : Nat) : Nat := 128 * tile + lane / 8 % 8 + 8 * group

/-- The explicit source length of a loader copy with a valid, nonnegative tile. -/
def kvCopySize (len tile lane group : Nat) : Nat :=
  if kvCopyRow tile lane group < len then 16 else 0

theorem kvCopySize_le (len tile lane group : Nat) : kvCopySize len tile lane group ≤ 16 := by
  unfold kvCopySize
  split <;> omega

theorem kvCopyColumn_byte_lt {lane byte : Nat} (upper : Bool) (hb : byte < 16) :
    kvCopyColumn lane upper + byte / 2 < 128 := by
  have hl := Nat.mod_lt lane (show 0 < 8 by decide)
  cases upper <;> simp [kvCopyColumn] <;> omega

theorem CacheLayout.loc_aligned {c : CacheLayout} {page head row d : Nat}
    (hb : c.base % 16 = 0) (hp : c.pageStride % 8 = 0)
    (hh : c.headStride % 8 = 0) (hr : c.rowStride % 8 = 0) (hd : d % 8 = 0) :
    (c.loc page head row d).addr % 16 = 0 := by
  have hs : (page * c.pageStride + head * c.headStride + row * c.rowStride + d) % 8 = 0 := by
    simp [Nat.add_mod, Nat.mul_mod, hp, hh, hr, hd]
  have hb' : c.base = 16 * (c.base / 16) := by omega
  have hs' : ∀ n, n % 8 = 0 → n = 8 * (n / 8) := by omega
  dsimp [CacheLayout.loc, globalLoc]
  have h := hs' _ hs
  omega

/-- A valid vector's entire 16-byte source stays inside the host cache region. -/
theorem CacheLayout.loc_copy_in_region {c : CacheLayout} {page pages head heads row d byte : Nat}
    (hp : page < pages) (hh : head < heads) (hr : row < 16) (hd : d + byte / 2 < 128) :
    (c.region pages heads).Contains ((c.loc page head row d).at byte) := by
  have hp' := Nat.mul_le_mul_right c.pageStride (show page ≤ pages - 1 by omega)
  have hh' := Nat.mul_le_mul_right c.headStride (show head ≤ heads - 1 by omega)
  have hr' := Nat.mul_le_mul_right c.rowStride (show row ≤ 15 by omega)
  refine ⟨rfl, rfl, ?_, ?_⟩
  all_goals simp only [CacheLayout.loc, globalLoc, CacheLayout.region, Loc.at] at *
  all_goals omega

/-- An offset within the eight-element copy names the corresponding byte of its BF16 element. -/
theorem CacheLayout.loc_copy_byte (c : CacheLayout) (page head row d byte : Nat) :
    (c.loc page head row d).at byte =
      (c.loc page head row (d + byte / 2)).at (byte % 2) := by
  simp only [CacheLayout.loc, globalLoc, Loc.at, Loc.mk.injEq, true_and]
  omega

/-- Valid rows of a paged K/V copy are initialized by the supplied physical page, cache head,
within-page row and BF16 column. -/
theorem Pre.kv_copy_byte {p : Params} {l : Launch} {m : Mem0} (h : Pre p l m)
    {b head row lane byte : Nat} (hb : b < p.batch) (hh : head < p.kvHeads)
    (hr : row < p.kLength b) (hbyte : byte < 16) (upper : Bool) :
    let page := p.page b (row / 16)
    let r := row % 16
    let d := kvCopyColumn lane upper
    m ((p.kLayout.loc page head r d).at byte) =
      some (some ((Value.float .bf16 (p.k page head r (d + byte / 2))).byteAt (byte % 2))) ∧
    m ((p.vLayout.loc page head r d).at byte) =
      some (some ((Value.float .bf16 (p.v page head r (d + byte / 2))).byteAt (byte % 2))) := by
  have hpage : row / 16 < (p.kLength b + 15) / 16 := by omega
  have hp := ((h.pageTable b hb).2 _ hpage).1
  obtain ⟨hk, hv⟩ := h.kvBytes _ hp head hh (row % 16) (Nat.mod_lt _ (by decide)) _
    (kvCopyColumn_byte_lt (lane := lane) upper hbyte)
  dsimp only
  rw [CacheLayout.loc_copy_byte p.kLayout, CacheLayout.loc_copy_byte p.vLayout]
  exact ⟨hk _ (by simp [Value.bytes, FloatFmt.bytes]; omega),
    hv _ (by simp [Value.bytes, FloatFmt.bytes]; omega)⟩

/-- The two addresses in each of the four local scratch arrays. The lower two arrays
store 64-bit K/V row bases; the upper two store 32-bit within-page rows and page indices. -/
def kvLocalOffset (array : Fin 4) (entry : Fin 2) : Nat :=
  32 * array.val + (if array.val < 2 then 8 else 4) * entry.val

theorem kvLocalOffset_aligned (array : Fin 4) (entry : Fin 2) {base : Nat}
    (hb : base % 32 = 0) :
    (base + kvLocalOffset array entry) % (if array.val < 2 then 8 else 4) = 0 := by
  unfold kvLocalOffset
  split <;> omega

theorem kvLocalOffset_bound (array : Fin 4) (entry : Fin 2) {byte : Nat}
    (hb : byte < (if array.val < 2 then 8 else 4)) :
    kvLocalOffset array entry + byte < 128 := by
  have ha := array.isLt
  have he := entry.isLt
  unfold kvLocalOffset
  by_cases h : array.val < 2 <;> simp [h] at hb ⊢ <;> omega

theorem Pre.kv_local_allocated {p : Params} {l : Launch} {m : Mem0} (h : Pre p l m)
    {g byte : Nat} (hg : g < l.threads) (array : Fin 4) (entry : Fin 2)
    (hb : byte < (if array.val < 2 then 8 else 4)) :
    m ((⟨.local, g, l.localBase + kvLocalOffset array entry⟩ : Loc).at byte) ≠ none := by
  simpa [Loc.at, Nat.add_assoc] using h.localMemory.2.2 _ hg _ (kvLocalOffset_bound array entry hb)

/-- Shared-address swizzle performed by `shr.u32`, `and.b32` and `xor.b32`. -/
def kvSwizzle (addr : Nat) : Nat := addr ^^^ ((addr >>> 3) &&& 112)

private theorem kvSwizzle_div_128 (addr : Nat) : kvSwizzle addr / 128 = addr / 128 := by
  have h := Nat.and_lt_two_pow (addr >>> 3) (show 112 < 2 ^ 7 by decide)
  have hz : ((addr >>> 3) &&& 112) / 128 = 0 := by omega
  unfold kvSwizzle
  rw [show 128 = 2 ^ 7 by decide, Nat.xor_div_two_pow]
  simpa using congrArg (fun n => (addr / 128) ^^^ n) hz

theorem kvSwizzle_div_1024 (addr : Nat) : kvSwizzle addr / 1024 = addr / 1024 := by
  have h := kvSwizzle_div_128 addr
  omega

theorem kvSwizzle_injective : Function.Injective kvSwizzle := by
  intro a b he
  have hd : a / 128 = b / 128 := by
    rw [← kvSwizzle_div_128 a, ← kvSwizzle_div_128 b, he]
  let mask := fun x : Nat => (x >>> 3) &&& 112
  have hmask : ∀ x, mask x = 16 * ((x / 128) % 8) := by
    intro x
    have hd' : mask x / 16 = (x / 128) % 8 := by
      dsimp only [mask]
      rw [show 16 = 2 ^ 4 by decide, Nat.and_div_two_pow, Nat.shiftRight_eq_div_pow]
      have hq : x / 2 ^ 3 / 2 ^ 4 = x / 128 := by omega
      rw [hq, show (112 : Nat) / 2 ^ 4 = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    have hm : mask x % 16 = 0 := by
      dsimp only [mask]
      rw [show 16 = 2 ^ 4 by decide, Nat.and_mod_two_pow]
      simp
    omega
  have hm : mask a = mask b := by rw [hmask, hmask, hd]
  change a ^^^ mask a = b ^^^ mask b at he
  rw [hm] at he
  have hh := congrArg (fun x => x ^^^ mask b) he
  simpa [Nat.xor_assoc, Nat.xor_self] using hh

theorem kvSwizzle_aligned {addr : Nat} (ha : addr % 16 = 0) :
    kvSwizzle addr % 16 = 0 := by
  unfold kvSwizzle
  rw [show 16 = 2 ^ 4 by decide, Nat.xor_mod_two_pow, Nat.and_mod_two_pow]
  simp [ha]

/-- Destination of one 16-byte copy. The source-predicate index selects a 1024-byte row
group, and the upper half selects the second 16384-byte plane. -/
def kvCopyAddress (base stage lane group : Nat) (upper : Bool) : Nat :=
  kvSwizzle (base + 68608 + 1024 * (group % 2) + 16 * (lane % 64)) +
    32768 * stage + 2048 * (group / 2) + if upper then 16384 else 0

theorem kvCopyAddress_div_1024 {base : Nat} (hb : base % 1024 = 0)
    (stage lane group : Nat) (upper : Bool) :
    kvCopyAddress base stage lane group upper / 1024 =
      base / 1024 + 67 + 32 * stage + group + if upper then 16 else 0 := by
  have hl := Nat.mod_lt lane (show 0 < 64 by decide)
  have hs := kvSwizzle_div_1024 (base + 68608 + 1024 * (group % 2) + 16 * (lane % 64))
  unfold kvCopyAddress
  cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem kvCopyAddress_aligned {base : Nat} (hb : base % 1024 = 0)
    (stage lane group : Nat) (upper : Bool) :
    kvCopyAddress base stage lane group upper % 16 = 0 := by
  have hs := kvSwizzle_aligned
    (addr := base + 68608 + 1024 * (group % 2) + 16 * (lane % 64)) (by omega)
  unfold kvCopyAddress
  cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem kvCopyAddress_range {base stage lane group byte : Nat} {upper : Bool}
    (hb : base % 1024 = 0) (hs : stage < 3) (hg : group < 16) (hbyte : byte < 16) :
    base + 68608 ≤ kvCopyAddress base stage lane group upper + byte ∧
      kvCopyAddress base stage lane group upper + byte < base + 166912 := by
  have hd := kvCopyAddress_div_1024 hb stage lane group upper
  have ha := kvCopyAddress_aligned hb stage lane group upper
  cases upper <;> simp at hd <;> omega

theorem Pre.kv_destination_allocated {p : Params} {l : Launch} {m : Mem0} (h : Pre p l m)
    {cta stage lane group byte : Nat} {upper : Bool} (hc : cta < l.grid)
    (hs : stage < 3) (hg : group < 16) (hb : byte < 16) :
    m ⟨.shared, cta, kvCopyAddress l.sharedBase stage lane group upper + byte⟩ ≠ none := by
  have hr := kvCopyAddress_range (lane := lane) (upper := upper) h.shared.1 hs hg hb
  let off := kvCopyAddress l.sharedBase stage lane group upper + byte - l.sharedBase
  have he : l.sharedBase + off = kvCopyAddress l.sharedBase stage lane group upper + byte := by
    dsimp [off]
    omega
  rw [← he]
  exact h.shared.2.2 cta hc off (by dsimp [off]; omega)

/-- Distinct copies from the same issuing lane and committed group occupy disjoint shared bytes. -/
theorem kvCopyAddress_apart {base stage lane i j : Nat} {u v : Bool}
    (hb : base % 1024 = 0) (hi : i < 16) (hj : j < 16) (h : i ≠ j ∨ u ≠ v) :
    kvCopyAddress base stage lane i u + 16 ≤ kvCopyAddress base stage lane j v ∨
      kvCopyAddress base stage lane j v + 16 ≤ kvCopyAddress base stage lane i u := by
  have hdi := kvCopyAddress_div_1024 hb stage lane i u
  have hdj := kvCopyAddress_div_1024 hb stage lane j v
  have hai := kvCopyAddress_aligned hb stage lane i u
  have haj := kvCopyAddress_aligned hb stage lane j v
  cases u <;> cases v <;> simp at h hdi hdj <;> omega

/-- The 64 loader lanes write disjoint vectors for a fixed row-group index and plane. -/
theorem kvCopyAddress_lane_ne {base stage a b group : Nat} {upper : Bool}
    (hne : a % 64 ≠ b % 64) :
    kvCopyAddress base stage a group upper ≠ kvCopyAddress base stage b group upper := by
  intro h
  unfold kvCopyAddress at h
  have he : kvSwizzle (base + 68608 + 1024 * (group % 2) + 16 * (a % 64)) =
      kvSwizzle (base + 68608 + 1024 * (group % 2) + 16 * (b % 64)) := by
    omega
  have hraw := kvSwizzle_injective he
  exact hne (by omega)

end

end PTX.Kernels.TmlFa4Fwd
