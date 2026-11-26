-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Access

@[expose] public section

/-! # Four bytes of 32-bit words rebuild a 32-bit word

Read bytes `i < 4`, each the byte `i` of some 32-bit value (the values may differ), rebuild a
32-bit word (`rebuild`): the bytes are integer bytes, so the value is assembled from their bit
patterns. -/

namespace PTX

/-- **Four read bytes that are bytes of 32-bit values rebuild a 32-bit value.** -/
theorem rebuild_bits32 {bs : List (Option Byte)} (hl : bs.length = 4)
    (h : ∀ i < 4, ∃ z, bs[i]? = some (some (Value.bits 32 z, i))) :
    ∃ z, rebuild 3 bs = .ok (.bits 32 z) := by
  match bs, hl with
  | [b0, b1, b2, b3], _ =>
    obtain ⟨z0, h0⟩ := h 0 (by omega)
    obtain ⟨z1, h1⟩ := h 1 (by omega)
    obtain ⟨z2, h2⟩ := h 2 (by omega)
    obtain ⟨z3, h3⟩ := h 3 (by omega)
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1 h2 h3
    subst h0 h1 h2 h3
    by_cases hz : z0 = z1 ∧ z1 = z2 ∧ z2 = z3
    · obtain ⟨rfl, rfl, rfl⟩ := hz
      refine ⟨z0, ?_⟩
      simp [rebuild, Value.bytes, Value.toBytes, Value.byteAt, List.range_succ]; rfl
    · obtain ⟨x, hx⟩ : ∃ x, littleEndianBits [some (Value.bits 32 z0, 0),
          some (Value.bits 32 z1, 1), some (Value.bits 32 z2, 2),
          some (Value.bits 32 z3, 3)] = some x := by
        simp [littleEndianBits, byteBits, Value.bitPattern, Value.bytes]
      refine ⟨BitVec.ofNat 64 x, ?_⟩
      simp [rebuild, rebuild.halves, intByte, rebuildBits, hx]
      split_ifs with hc
      · exfalso
        apply hz
        simp [Value.toBytes, Value.bytes, Value.byteAt, List.range_succ] at hc
        obtain ⟨h1, h2, h3⟩ := hc
        subst h1 h2 h3
        exact ⟨rfl, rfl, rfl⟩
      · rfl

end PTX
