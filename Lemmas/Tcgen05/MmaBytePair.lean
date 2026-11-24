-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaSafety
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # The two bytes of a 2-byte MMA operand element are adjacent

The swizzles permute 16-byte chunks (32-byte chunks for the 32-byte-atomic mode) and keep the
bytes inside a chunk in order, so a byte that is not the last of its chunk is followed by the
next one (`TensorSwizzle.offset_succ`, `TcShared.Swizzle.offset_succ`). With an even start,
leading and stride (true of every encoded descriptor, `TcMma.SharedEncoded`), the canonical
offset of a 2-byte element is even, so its second byte is the shared byte after its first
(`TcShared.byteAddress_two_succ`) and its first byte is at an even address
(`TcShared.byteAddress_two_even`). So an MMA operand of a 2-byte kind reads byte `2 m + 1` at the
location after byte `2 m` (`TcMma.OperandSpec.byteLoc_pair`), which is even
(`TcMma.OperandSpec.byteLoc_even`). -/

namespace PTX

namespace TensorSwizzle

/-- **A swizzle keeps the order inside a chunk.** -/
theorem offset_succ (mode : Mode) (base byte : Nat) (h : byte % 16 < 15) :
    offset mode base (byte + 1) = offset mode base byte + 1 := by
  have h1 : (byte + 1) / 128 = byte / 128 := by omega
  have h2 : (byte + 1) / 16 = byte / 16 := by omega
  have h3 : (byte + 1) % 16 = byte % 16 + 1 := by omega
  simp only [offset, h1, h2, h3]
  omega

/-- The 32-byte-atomic swizzle keeps the order inside a 32-byte chunk. -/
theorem offset128x32_succ (base byte : Nat) (h : byte % 32 < 31) :
    offset128x32 base (byte + 1) = offset128x32 base byte + 1 := by
  have h1 : (byte + 1) / 128 = byte / 128 := by omega
  have h2 : (byte + 1) / 32 = byte / 32 := by omega
  have h3 : (byte + 1) % 32 = byte % 32 + 1 := by omega
  simp only [offset128x32, h1, h2, h3]
  omega

end TensorSwizzle

namespace TcShared

/-- Every MMA swizzle keeps the order inside a 16-byte chunk. -/
theorem Swizzle.offset_succ (s : Swizzle) (a : Nat) (h : a % 16 < 15) :
    s.offset (a + 1) = s.offset a + 1 := by
  cases s <;> simp only [Swizzle.offset] <;>
    first
    | exact TensorSwizzle.offset_succ _ _ _ h
    | exact TensorSwizzle.offset128x32_succ _ _ (by omega)

/-- The canonical offset of a 2-byte element is even when the strides are. -/
theorem linear_two_even (major : Major) (s : Swizzle) (d : Descriptor) (row k : Nat)
    (hl : d.leading % 2 = 0) (hs : d.stride % 2 = 0) : linear 2 major s d row k % 2 = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, d.leading = 2 * a := ⟨d.leading / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, d.stride = 2 * b := ⟨d.stride / 2, by omega⟩
  cases major <;> simp only [linear, ha, hb] <;> split_ifs <;> simp only [Nat.mul_assoc] <;> omega

/-- **The second byte of a 2-byte element** is the shared byte after its first, for a descriptor
with even start, leading and stride. -/
theorem byteAddress_two_succ (major : Major) (d : Descriptor) (row k : Nat)
    (hst : d.start % 2 = 0) (hl : d.leading % 2 = 0) (hs : d.stride % 2 = 0) :
    byteAddress 2 major d row k 1 = (byteAddress 2 major d row k 0).map (· + 1) := by
  have he := linear_two_even major d.swizzle d row k hl hs
  unfold byteAddress
  split_ifs with h1 h0 h0
  · simp only [Option.map_some, Nat.add_zero]
    exact congrArg some
      (Swizzle.offset_succ _ (d.start + linear 2 major d.swizzle d row k) (by omega))
  · exact absurd ⟨h1.1, h1.2.1, h1.2.2.1, by decide, h1.2.2.2.2⟩ h0
  · exact absurd ⟨h0.1, h0.2.1, h0.2.2.1, by decide, h0.2.2.2.2⟩ h1
  · rfl

/-- Every MMA swizzle keeps the parity of a byte address. -/
theorem Swizzle.offset_mod_two (s : Swizzle) (a : Nat) : s.offset a % 2 = a % 2 := by
  cases s <;> simp only [Swizzle.offset]
  · have := TensorSwizzle.offset_byte .none 0 a
    omega
  · simp only [TensorSwizzle.offset128x32]
    omega
  · have := TensorSwizzle.offset_byte .b128 0 a
    omega
  · have := TensorSwizzle.offset_byte .b64 0 a
    omega
  · have := TensorSwizzle.offset_byte .b32 0 a
    omega

/-- **The first byte of a 2-byte element** is at an even address, for a descriptor with even
start, leading and stride. -/
theorem byteAddress_two_even (major : Major) (d : Descriptor) (row k : Nat)
    (hst : d.start % 2 = 0) (hl : d.leading % 2 = 0) (hs : d.stride % 2 = 0) {a : Nat}
    (h : byteAddress 2 major d row k 0 = some a) : a % 2 = 0 := by
  have he := linear_two_even major d.swizzle d row k hl hs
  unfold byteAddress at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  rw [Swizzle.offset_mod_two]
  omega

end TcShared

namespace TcMma

/-- The shared byte after `l`. -/
def nextLoc (l : Loc) : Loc := ⟨l.space, l.cta, l.addr + 1⟩

theorem kind_k_pos (kd : Kind) : 0 < kd.k := by
  cases kd <;> simp [Kind.k]

/-- **The two bytes of a 2-byte operand element are adjacent**: an MMA of a 2-byte kind with
encoded shared descriptors reads byte `2 m + 1` of an operand at the byte after byte `2 m`. -/
theorem OperandSpec.byteLoc_pair (s : OperandSpec) (op : Operand) (m : Nat)
    (hw : s.descriptor.kind.width = 2) (ha : SharedEncoded s.a) (hb : SharedEncoded s.b) :
    s.byteLoc op (2 * m + 1) = (s.byteLoc op (2 * m)).map nextLoc := by
  have hk := kind_k_pos s.descriptor.kind
  have hrow : (2 * m + 1) / (s.descriptor.kind.k * 2) = 2 * m / (s.descriptor.kind.k * 2) := by
    rw [Nat.mul_comm s.descriptor.kind.k 2, ← Nat.div_div_eq_div_mul,
      ← Nat.div_div_eq_div_mul]
    congr 1
    omega
  have hkk : (2 * m + 1) / 2 % s.descriptor.kind.k = 2 * m / 2 % s.descriptor.kind.k := by
    congr 1
    omega
  have hz1 : (2 * m + 1) % 2 = 1 := by omega
  have hz0 : 2 * m % 2 = 0 := by omega
  have hsh : ∀ (d : TcShared.Descriptor), SharedEncoded d → ∀ major row k,
      TcShared.byteAddress 2 major d row k 1 =
        (TcShared.byteAddress 2 major d row k 0).map (· + 1) := by
    intro d hd major row k
    obtain ⟨-, -, -, h1, h2, h3⟩ := hd
    exact TcShared.byteAddress_two_succ major d row k (by omega) (by omega) (by omega)
  unfold OperandSpec.byteLoc
  cases op <;> simp only [hw, hrow, hkk, hz1, hz0] <;> split_ifs <;>
    first
    | rfl
    | (rw [hsh _ ha]; cases TcShared.byteAddress 2 _ s.a _ _ 0 <;> rfl)
    | (rw [hsh _ hb]; cases TcShared.byteAddress 2 _ s.b _ _ 0 <;> rfl)

/-- **The first byte of a 2-byte operand element is at an even address.** -/
theorem OperandSpec.byteLoc_even (s : OperandSpec) (op : Operand) (m : Nat)
    (hw : s.descriptor.kind.width = 2) (ha : SharedEncoded s.a) (hb : SharedEncoded s.b) {l : Loc}
    (h : s.byteLoc op (2 * m) = some l) : l.addr % 2 = 0 := by
  have hev : ∀ (d : TcShared.Descriptor), SharedEncoded d → ∀ major row k a,
      TcShared.byteAddress 2 major d row k 0 = some a → a % 2 = 0 := by
    intro d hd major row k a h
    obtain ⟨-, -, -, h1, h2, h3⟩ := hd
    exact TcShared.byteAddress_two_even major d row k (by omega) (by omega) (by omega) h
  have hz0 : 2 * m % 2 = 0 := by omega
  unfold OperandSpec.byteLoc at h
  cases op <;> simp only [hw, hz0] at h <;> split_ifs at h <;>
    obtain ⟨addr, hadd, hl⟩ := Option.bind_eq_some_iff.mp h <;>
    obtain rfl := Option.some.inj hl <;>
    first
    | exact hev _ ha _ _ _ _ hadd
    | exact hev _ hb _ _ _ _ hadd

/-- An MMA operand byte is a shared byte. -/
theorem OperandSpec.byteLoc_shared {s : OperandSpec} {op : Operand} {idx : Nat} {l : Loc}
    (h : s.byteLoc op idx = some l) : l.space = .shared := by
  unfold OperandSpec.byteLoc at h
  simp only [bind, Option.bind] at h
  split_ifs at h
  all_goals split at h
  all_goals first
    | (cases h; rfl)
    | cases h

end TcMma

end PTX
