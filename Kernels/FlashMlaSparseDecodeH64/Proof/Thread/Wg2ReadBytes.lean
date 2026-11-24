-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Tracked

@[expose] public section

/-! # Finite raw bytes as dequantizer read operands -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2

open PTX PTX.Proof

/-- A cache input byte is a plain, initialized eight-bit integer payload. -/
def inputByte (n : Nat) : Option Byte := some (Value.bits 8 (BitVec.ofNat 64 n), 0)

private def packed : List Nat → Nat
  | [] => 0
  | n :: ns => n + 256 * packed ns

private theorem packed_lt {ns : List Nat} (h : ∀ n ∈ ns, n < 256) :
    packed ns < 256 ^ ns.length := by
  induction ns with
  | nil => decide
  | cons n ns ih =>
    have hn := h n (by simp)
    have hp := ih (fun x hx => h x (List.mem_cons_of_mem n hx))
    simp only [packed, List.length_cons, pow_succ']
    omega

private theorem unpack {ns : List Nat} (h : ∀ n ∈ ns, n < 256) {i : Nat}
    (hi : i < ns.length) : Numeric.byteAt (packed ns) i = ns[i] := by
  induction ns generalizing i with
  | nil => simp at hi
  | cons n ns ih =>
    have hn := h n (by simp)
    cases i with
    | zero =>
      simp [Numeric.byteAt, packed, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn]
    | succ i =>
      have hid : (n + 256 * packed ns) / 256 = packed ns := by omega
      have hi' : i < ns.length := by simpa using hi
      simp only [Numeric.byteAt, packed, pow_succ', ← Nat.div_div_eq_div_mul, hid,
        List.getElem_cons_succ]
      exact ih (fun x hx => h x (List.mem_cons_of_mem n hx)) hi'

private theorem littleEndianBits_input {ns : List Nat} (h : ∀ n ∈ ns, n < 256) :
    littleEndianBits (ns.map inputByte) = some (packed ns) := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    have hn := h n (by simp)
    have hp := ih (fun x hx => h x (List.mem_cons_of_mem n hx))
    simp [littleEndianBits, inputByte, byteBits, Value.bitPattern, Value.bytes, hp, packed,
      Nat.mod_eq_of_lt hn ]

private theorem rebuild_input {ns : List Nat} (h : ∀ n ∈ ns, n < 256)
    (hn : ns.length = 4 ∨ ns.length = 8) :
    rebuild 3 (ns.map inputByte) = .ok (.bits (8 * ns.length) (BitVec.ofNat 64 (packed ns))) := by
  have bits := littleEndianBits_input h
  have hz : none ∉ ns.map inputByte := by
    simp [inputByte]
  have hb : (ns.map inputByte).all intByte = true := by
    simp [List.all_eq_true, inputByte, intByte]
  rcases ns with _ | ⟨n, ns⟩
  · simp at hn
  · have hm : 1 ≠ (ns.length + 1) := by
      simp only [List.length_cons] at hn
      omega
    simp only [List.map_cons, inputByte] at hz hb bits ⊢
    have hns : ns.length = 3 ∨ ns.length = 7 := by
      simp only [List.length_cons] at hn
      omega
    rcases hns with hns | hns <;>
      simp [rebuild, rebuild.halves, hz, hb, rebuildBits, bits, Value.bytes, hns, pure,
        Except.pure]

/-- Eight finite e4m3 payload bytes rebuild into the raw register the site accepts. -/
theorem raw_read_accepts {ns : List Nat} (hlen : ns.length = 8)
    (hByte : ∀ b ∈ ns, b < 256 ∧ b ≠ 127 ∧ b ≠ 255) :
    let bs := ns.map inputByte
    rebuild 3 bs = .ok (b64 (rawBits bs)) ∧ RawWordOk (rawBits bs) := by
  intro bs
  have h : ∀ n ∈ ns, n < 256 := fun n hn => (hByte n hn).1
  have hPacked := packed_lt h
  rw [hlen] at hPacked
  have hPacked64 : packed ns < 2 ^ 64 := hPacked
  have hRaw : rawBits bs = packed ns := by
    unfold rawBits bytesNat
    rw [show littleEndianBits bs = some (packed ns) from littleEndianBits_input h]
    exact Nat.mod_eq_of_lt hPacked64
  rw [hRaw]
  refine ⟨?_, hPacked64, ?_⟩
  · simpa [bs, hlen, b64] using rebuild_input h (.inr hlen)
  · intro i
    have hi : i.val < ns.length := by rw [hlen]; exact i.isLt
    rw [unpack h hi]
    exact (hByte _ (List.getElem_mem _)).2

/-- Four finite ue8m0 payload bytes rebuild into the scale accumulator word. -/
theorem scale_read_accepts {ns : List Nat} (hlen : ns.length = 4)
    (hByte : ∀ b ∈ ns, b < 255) :
    let bs := ns.map inputByte
    rebuild 3 bs = .ok (b32 (scaleBits bs)) ∧
      ∀ i : Fin 4, Numeric.byteAt (scaleBits bs) i.val < 255 := by
  intro bs
  have h : ∀ n ∈ ns, n < 256 := fun n hn => (hByte n hn).trans (by decide)
  have hPacked := packed_lt h
  rw [hlen] at hPacked
  have hRaw : scaleBits bs = packed ns := by
    unfold scaleBits bytesNat
    rw [show littleEndianBits bs = some (packed ns) from littleEndianBits_input h]
    exact Nat.mod_eq_of_lt hPacked
  rw [hRaw]
  constructor
  · simpa [bs, hlen, b32] using rebuild_input h (.inl hlen)
  · intro i
    have hi : i.val < ns.length := by rw [hlen]; exact i.isLt
    rw [unpack h hi]
    exact hByte _ (List.getElem_mem _)

/-- Four bytes of the tensor map's typed zero fill. -/
def zeroWord : List (Option Byte) := (b32 0).toBytes.map some

/-- An invalid row's two zero-fill words rebuild into one finite raw word. -/
theorem raw_zero_accepts :
    rebuild 3 (zeroWord ++ zeroWord) = .ok (b64 (rawBits (zeroWord ++ zeroWord))) ∧
      RawWordOk (rawBits (zeroWord ++ zeroWord)) := by
  constructor
  · let z := b32 0
    have hw : zeroWord = [some (z, 0), some (z, 1), some (z, 2), some (z, 3)] := rfl
    rw [hw]
    simp [rebuild, rebuild.halves, rebuildBits, z, b32, b64, Value.bytes, intByte,
      rawBits, bytesNat, littleEndianBits, byteBits, Value.bitPattern, pure, Except.pure]
  · change RawWordOk 0
    decide

/-- An invalid row's single zero-fill word rebuilds into its finite scales. -/
theorem scale_zero_accepts :
    rebuild 3 zeroWord = .ok (b32 (scaleBits zeroWord)) ∧
      ∀ i : Fin 4, Numeric.byteAt (scaleBits zeroWord) i.val < 255 := by
  constructor
  · change rebuild 3 ((b32 0).toBytes.map some) = .ok (b32 0)
    exact PTX.Proof.rebuild_scalar (by decide) rfl
  · change ∀ i : Fin 4, Numeric.byteAt 0 i.val < 255
    decide

private theorem byteAt_mod {v i : Nat} :
    Numeric.byteAt (v % 256 ^ (i + 1)) i = Numeric.byteAt v i := by
  simp only [Numeric.byteAt, pow_succ, Nat.mod_mul_right_div_self, Nat.mod_mod]

/-- A scale element extends the finite-byte prefix tracked in its little-endian accumulator. -/
theorem scale_update_prefix {old fresh count : Nat}
    (hOld : ∀ i < count, Numeric.byteAt old i < 255)
    (hFresh : ∀ i : Fin 4, Numeric.byteAt fresh i.val < 255) :
    ∀ i < count + 4,
      Numeric.byteAt (old % 256 ^ count + 256 ^ count * fresh) i < 255 := by
  intro i hi
  by_cases h : i < count
  · have hd := Nat.pow_dvd_pow 256 (show i + 1 ≤ count by omega)
    have hshift : 256 ^ (i + 1) ∣ 256 ^ count * fresh := dvd_mul_of_dvd_left hd _
    have hm : (old % 256 ^ count + 256 ^ count * fresh) % 256 ^ (i + 1) =
        old % 256 ^ (i + 1) := by
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hshift, Nat.add_zero, Nat.mod_mod,
        Nat.mod_mod_of_dvd _ hd]
    have hbyte := congrArg (fun n => Numeric.byteAt n i) hm
    simp only [byteAt_mod] at hbyte
    exact hbyte.symm ▸ hOld i h
  · have hpow := Nat.pow_pos (n := count) (show 0 < (256 : Nat) by decide)
    have hcount : count + (i - count) = i := by omega
    have hw : (old % 256 ^ count + 256 ^ count * fresh) / 256 ^ count = fresh := by
      rw [Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt (Nat.mod_lt _ hpow), Nat.zero_add]
    have hbyte : Numeric.byteAt (old % 256 ^ count + 256 ^ count * fresh) i =
        Numeric.byteAt fresh (i - count) := by
      unfold Numeric.byteAt
      conv_lhs =>
        rw [← hcount, pow_add, ← Nat.div_div_eq_div_mul, hw]
    rw [hbyte]
    exact hFresh ⟨i - count, by omega⟩

/-- The last scale element turns the finite-byte prefix into a finite full scale word. -/
theorem scale_update_final {old fresh : Nat}
    (hOld : ∀ i < 12, Numeric.byteAt old i < 255)
    (hFresh : ∀ i : Fin 4, Numeric.byteAt fresh i.val < 255) :
    ScaleWordOk (old % 256 ^ 12 + 256 ^ 12 * fresh) :=
  fun i => scale_update_prefix hOld hFresh i.val i.isLt

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2
