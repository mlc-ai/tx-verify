-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot
import Lemmas.Flow.Arith32Word
import Lemmas.Flow.OrBits
import Lemmas.Flow.BitForms
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The MMA warp's shared descriptor words, decoded

The words of the shape table (`qkBW`, `pvBW`, `pvAW`, `cpW`, `Ev.lean`) decode to the descriptors
of `Lib/MmaFoot.lean` at the tiles of the workspace (`Pre.sharedBase`, `Pre.sharedAlignment`,
`Pre.sharedRange`): QK MMA `k`'s B is `keyDesc` of the phase's dequantized tile, PV MMA `k`'s B
`valueDesc` of it, PV MMA `k`'s A `probDesc` of the P tile (byte 204800), copy `k`'s source
`keyDesc` of the query tile (byte 0). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MmaFoot

noncomputable section

private theorem shl_W {a : Nat} (h : a * 8 < 2 ^ 32) : shl (W a) 3 = W (a * 8) := by
  apply BitVec.eq_of_toNat_eq
  have h3 : (i32 3).toNat = 3 := by decide
  simp only [shl, h3]
  simp [r32, truncBits, W, Nat.shiftLeft_eq]
  omega

private theorem mad_W {a b c : Nat} (h : a * b + c < 2 ^ 32) (ha : a < 2 ^ 32)
    (hb : b < 2 ^ 31) (hc : c < 2 ^ 32) :
    mad32 (W a) (i32 (b : Int)) (W c) = W (a * b + c) := by
  rw [i32_W hb]
  apply BitVec.eq_of_toNat_eq
  have ha' : a % 4294967296 = a := Nat.mod_eq_of_lt ha
  have hb' : b % 4294967296 = b := Nat.mod_eq_of_lt (by omega)
  have hc' : c % 4294967296 = c := Nat.mod_eq_of_lt hc
  simp [mad32, r32, truncBits, W, ha', hb', hc']
  omega

private theorem shru_W {a : Nat} (h : a < 2 ^ 32) : shru (W a) 4 = W (a / 16) := by
  apply BitVec.eq_of_toNat_eq
  have h4 : (i32 4).toNat = 4 := by decide
  simp only [shru, h4]
  simp [r32, truncBits, W, Nat.shiftRight_eq_div_pow]
  omega

private theorem andi_W {a : Nat} (h : a < 2 ^ 32) : andi (W a) 16383 = W (a % 16384) := by
  apply BitVec.eq_of_toNat_eq
  have hi : i32 16383 = W 16383 := by decide
  simp only [andi, hi]
  simp [r32, truncBits, W]
  rw [Nat.mod_eq_of_lt (a := a) (by omega), land16383]
  omega

private theorem zext_W {a : Nat} (h : a < 2 ^ 32) : zext (W a) = W a := by
  apply BitVec.eq_of_toNat_eq
  simp only [zext, r32, truncBits, W, BitVec.toNat_ofNat]
  omega

private theorem ori_W {a C : Nat} (h : a < 2 ^ 16) (hC : C % 2 ^ 16 = 0) (hC' : C < 2 ^ 63) :
    ori64 (W a) (C : Int) = W (a + C) := by
  apply BitVec.eq_of_toNat_eq
  simp only [ori64, r64, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_ofInt, BitVec.toNat_or]
  rw [Int.toNat_emod (by omega) (by omega)]
  simp only [Int.toNat_natCast]
  have ha : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  have hc : C % 2 ^ 64 = C := Nat.mod_eq_of_lt (by omega)
  have h1 := lor_eq_add hC h
  have h2 := Nat.or_comm C a
  simp only [ha, hc]
  omega

private theorem lo32_W {a : Nat} (h : a < 2 ^ 64) : lo32 (W a) = W (a % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo32, truncBits, W, BitVec.toNat_ofNat]
  omega

private theorem hi32_W {a : Nat} (h : a < 2 ^ 64) : hi32 (W a) = W (a / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [hi32, truncBits, W, BitVec.toNat_ofNat]
  omega

private theorem join_W {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    join (W a) (W b) = W (a + b * 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [join, W, BitVec.toNat_ofNat, BitVec.toNat_or, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega),
    Nat.mod_eq_of_lt (a := b * 2 ^ 32) (by omega), Nat.or_comm,
    lor_eq_add (k := 32) (by simp) ha]
  omega

variable {P : Params} {L : Launch} {m : Mem0}

theorem base_facts (hp : Pre P L m) :
    L.sharedBase % 1024 = 0 ∧ L.sharedBase + 223232 ≤ 2 ^ 18 := by
  have h1 := hp.sharedAlignment
  have h2 := hp.sharedBase
  have h3 := hp.sharedRange
  unfold sharedBytes at h3
  rw [h2]
  omega

private theorem sbw_W (hB : L.sharedBase < 2 ^ 32) : sbw L = W L.sharedBase := by
  apply BitVec.eq_of_toNat_eq
  simp [sbw, truncBits, W]
  omega

private theorem rd116_W (hB : L.sharedBase + 223232 ≤ 2 ^ 18) {h : Nat} (hh : h < 2) :
    rd116 L (W h) = W ((L.sharedBase + 65536 * h) / 16) := by
  have hm := mad_W (a := h) (b := 65528) (c := L.sharedBase + h * 8) (by omega) (by omega)
    (by omega) (by omega)
  simp only [Nat.cast_ofNat] at hm
  simp only [rd116, bb]
  rw [sbw_W (by omega), shl_W (by omega), add32_W (by omega), hm, shru_W (by omega),
    andi_W (by omega), zext_W (by omega)]
  congr 1
  omega

private theorem addi64_W {a n : Nat} (hn : n < 2 ^ 63) :
    addi64 (W a) (n : Int) = W (a + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi64, r64, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  rw [Int.toNat_emod (by omega) (by omega)]
  simp only [Int.toNat_natCast]
  omega

private theorem qkOff_eq (k : Nat) : qkOff k = ((qkDelta k : Nat) : Int) := by
  simp [qkOff, qkDelta]

private theorem pvOff_eq {k : Nat} (hk : k < 8) : pvOff k = ((pvDelta k : Nat) : Int) := by
  unfold pvOff pvDelta
  interval_cases k <;> rfl

private theorem pvAOff_eq {k : Nat} (hk : k < 8) : pvAOff k = ((128 * (k / 2) : Nat) : Int) := by
  unfold pvAOff
  interval_cases k <;> rfl

/-- The word `x` with the high constant `C`: `x | C`. -/
private theorem ori_hi {a C : Nat} (ha : a < 2 ^ 16) (hC : C % 2 ^ 16 = 0) (hC' : C < 2 ^ 63)
    {c : Int} (hc : c = (C : Int)) : ori64 (W a) c = W (a + C) := by
  rw [hc]; exact ori_W ha hC hC'

/-- A word `n + C` advanced in its low half by `d`. -/
private theorem advance {n C d : Nat} (hn : n + C % 2 ^ 32 + d < 2 ^ 32) (hd : d < 2 ^ 31)
    (hC : C < 2 ^ 64) :
    join (addi (lo32 (W (n + C))) (d : Int)) (hi32 (W (n + C))) = W (n + d + C) := by
  have hc : (n + C) % 2 ^ 32 = n + C % 2 ^ 32 := by omega
  rw [lo32_W (by omega), hi32_W (by omega), hc, addi_W hd hn, join_W hn (by omega)]
  congr 1
  omega

private theorem kd_W (hB : L.sharedBase + 223232 ≤ 2 ^ 18) {h : Nat} (hh : h < 2) :
    kd L (W h) = W ((L.sharedBase + 65536 * h) / 16 + keyHi) := by
  simp only [kd]
  rw [rd116_W hB hh]
  exact ori_hi (by omega) (by decide) (by decide) (by simp [keyHi])

private theorem vd_W (hB : L.sharedBase + 223232 ≤ 2 ^ 18) {h : Nat} (hh : h < 2) :
    vd L (W h) = W ((L.sharedBase + 65536 * h) / 16 + valueHi) := by
  simp only [vd]
  rw [rd116_W hB hh]
  exact ori_hi (by omega) (by decide) (by decide) (by simp [valueHi])

/-- **QK MMA `k`'s B word**: the key descriptor of the phase's tile. -/
theorem qkBW_eq (hp : Pre P L m) {h k : Nat} (hh : h < 2) (hk : k < 16) :
    qkBW L (W h) k = W ((L.sharedBase + 65536 * h) / 16 + qkDelta k + keyHi) := by
  obtain ⟨-, hB⟩ := base_facts hp
  unfold qkBW
  split
  · subst k; rw [kd_W hB hh]; simp [qkDelta]
  · rw [kd_W hB hh, qkOff_eq]
    exact advance (by unfold qkDelta keyHi; omega) (by unfold qkDelta; omega) (by decide)

/-- **PV MMA `k`'s B word**: the value descriptor of the phase's tile. -/
theorem pvBW_eq (hp : Pre P L m) {h k : Nat} (hh : h < 2) (hk : k < 8) :
    pvBW L (W h) k = W ((L.sharedBase + 65536 * h) / 16 + pvDelta k + valueHi) := by
  obtain ⟨-, hB⟩ := base_facts hp
  unfold pvBW
  split
  · subst k; rw [vd_W hB hh]; simp [pvDelta]
  · rw [vd_W hB hh, pvOff_eq hk]
    exact advance (by unfold pvDelta valueHi; omega) (by unfold pvDelta; omega) (by decide)

/-- **PV MMA `k`'s A word**: the P tile's descriptor. -/
theorem pvAW_eq (hp : Pre P L m) {k : Nat} (hk : k < 8) :
    pvAW L k = W ((L.sharedBase + 204800) / 16 + 128 * (k / 2) + probHi) := by
  obtain ⟨-, hB⟩ := base_facts hp
  have h104 : rd104 L = W ((L.sharedBase + 204800) / 16 + probHi) := by
    have ha := addi_W (a := L.sharedBase) (n := 204800) (by omega) (by omega)
    simp only [Nat.cast_ofNat] at ha
    simp only [rd104]
    rw [sbw_W (by omega), ha, shru_W (by omega), andi_W (by omega), zext_W (by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact ori_hi (by omega) (by decide) (by decide) (by simp [probHi])
  unfold pvAW
  split
  · rename_i h0; rw [h104, h0]; simp
  · rw [h104, pvAOff_eq hk]
    exact advance (by unfold probHi; omega) (by omega) (by decide)

/-- **Copy `k`'s source word**: the key-layout descriptor of the query tile. -/
theorem cpW_eq (hp : Pre P L m) {k : Nat} (hk : k < 16) :
    cpW L k = W (L.sharedBase / 16 + qkDelta k + keyHi) := by
  obtain ⟨-, hB⟩ := base_facts hp
  have h87 : rd87 L = W (L.sharedBase / 16) := by
    simp only [rd87]
    rw [sbw_W (by omega), shru_W (by omega), andi_W (by omega), zext_W (by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hoff : cpOff k = ((qkDelta k + keyHi : Nat) : Int) := by
    simp only [cpOff, qkOff_eq, keyHi]; push_cast; ring
  unfold cpW
  split
  · subst k; rw [h87]
    exact ori_hi (by omega) (by decide) (by decide) (by rw [hoff]; simp [qkDelta])
  · rw [h87, hoff, addi64_W (by unfold qkDelta keyHi; omega),
      ← Nat.add_assoc]

/-! ### The decoded descriptors -/

private theorem desc_eq {n s lead st : Nat} {sw : TcShared.Swizzle} (h : 16 * n = s) :
    some (⟨16 * n, lead, st, 0, false, false, sw⟩ : TcShared.Descriptor) =
      some ⟨s, lead, st, 0, false, false, sw⟩ := by
  rw [h]

/-- **QK MMA `k`'s B descriptor** is the key layout of the phase's dequantized tile. -/
theorem qkBW_decode (hp : Pre P L m) {h k : Nat} (hh : h < 2) (hk : k < 16) :
    TcShared.decode (qkBW L (W h) k).toNat = some (keyDesc (L.sharedBase + 65536 * h) k) := by
  obtain ⟨hA, hB⟩ := base_facts hp
  rw [qkBW_eq hp hh hk, toNat_W (by unfold qkDelta keyHi; omega),
    decode_key (by unfold qkDelta; omega)]
  exact desc_eq (by omega)

/-- **PV MMA `k`'s B descriptor** is the value layout of the phase's dequantized tile. -/
theorem pvBW_decode (hp : Pre P L m) {h k : Nat} (hh : h < 2) (hk : k < 8) :
    TcShared.decode (pvBW L (W h) k).toNat = some (valueDesc (L.sharedBase + 65536 * h) k) := by
  obtain ⟨hA, hB⟩ := base_facts hp
  rw [pvBW_eq hp hh hk, toNat_W (by unfold pvDelta valueHi; omega),
    decode_value (by unfold pvDelta; omega)]
  exact desc_eq (by omega)

/-- **PV MMA `k`'s A descriptor** is the P tile's. -/
theorem pvAW_decode (hp : Pre P L m) {k : Nat} (hk : k < 8) :
    TcShared.decode (pvAW L k).toNat = some (probDesc (L.sharedBase + 204800) k) := by
  obtain ⟨hA, hB⟩ := base_facts hp
  rw [pvAW_eq hp hk, toNat_W (by unfold probHi; omega), decode_prob (by omega)]
  exact desc_eq (by omega)

/-- **Copy `k`'s source descriptor** is the key layout of the query tile (byte 0). -/
theorem cpW_decode (hp : Pre P L m) {k : Nat} (hk : k < 16) :
    TcShared.decode (cpW L k).toNat = some (keyDesc L.sharedBase k) := by
  obtain ⟨hA, hB⟩ := base_facts hp
  rw [cpW_eq hp hk, toNat_W (by unfold qkDelta keyHi; omega),
    decode_key (by unfold qkDelta; omega)]
  exact desc_eq (by omega)

/-- The tiles' first bytes are multiples of 128. -/
theorem base_128 (hp : Pre P L m) (c : Nat) (hc : c % 128 = 0) : (L.sharedBase + c) % 128 = 0 := by
  obtain ⟨hA, -⟩ := base_facts hp
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
