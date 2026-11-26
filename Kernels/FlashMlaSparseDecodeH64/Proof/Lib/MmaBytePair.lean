-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot
import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # The two bytes of a 16-bit operand element are adjacent

Byte `2 m + 1` of a 16-bit element of an MMA's shared operand lies one byte after byte `2 m`, and
byte `2 m` is at an even address (`byteLoc_pair`), when the descriptor's start, leading and stride
offsets are even: the address is the swizzle of `start + linear + byte`, and the swizzle permutes
16-byte chunks and keeps the byte within the chunk. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot
open PTX

/-- A swizzle keeps an even byte's successor adjacent. -/
theorem swz_succ (mode : TensorSwizzle.Mode) {x : Nat} (hx : x % 2 = 0) :
    TensorSwizzle.offset mode 0 (x + 1) = TensorSwizzle.offset mode 0 x + 1 := by
  have h1 : (x + 1) / 128 = x / 128 := by omega
  have h2 : (x + 1) / 16 = x / 16 := by omega
  unfold TensorSwizzle.offset
  rw [h1, h2]
  omega

theorem swz_even (mode : TensorSwizzle.Mode) {x : Nat} (hx : x % 2 = 0) :
    TensorSwizzle.offset mode 0 x % 2 = 0 := by
  unfold TensorSwizzle.offset
  omega

/-- **Bytes `2 m` and `2 m + 1` of a 16-bit operand element are at adjacent addresses.** -/
theorem byteAddress_pair {major : TcShared.Major} {d : TcShared.Descriptor} {row k : Nat}
    {a : Nat} (h0 : d.start % 2 = 0) (h1 : d.leading % 2 = 0)
    (h2 : d.stride % 2 = 0) (h : TcShared.byteAddress 2 major d row k 0 = some a) :
    TcShared.byteAddress 2 major d row k 1 = some (a + 1) ∧ a % 2 = 0 := by
  unfold TcShared.byteAddress at h ⊢
  split_ifs at h with hc
  obtain ⟨c1, c2, c3, -, c5, c6⟩ := hc
  have hsw : d.swizzle ≠ .b128x32 := by
    cases major
    · exact c5 rfl
    · intro hh
      have := (c6 rfl).mp hh
      omega
  have hev : (d.start + TcShared.linear 2 major d.swizzle d row k) % 2 = 0 := by
    cases major <;> cases hs : d.swizzle <;>
      simp [TcShared.linear, TcShared.Swizzle.sectors, h0, h1, h2, Nat.add_mod, Nat.mul_mod]
  split_ifs with hc2
  · simp only [Option.some.injEq] at h ⊢
    subst h
    cases hs : d.swizzle <;> simp only [hs, TcShared.Swizzle.offset, Nat.add_zero] at hev hsw ⊢
    all_goals first | exact ⟨swz_succ _ hev, swz_even _ hev⟩ | exact absurd rfl hsw
  · exact absurd ⟨c1, c2, c3, by omega, c5, c6⟩ hc2

/-- **Bytes `2 m` and `2 m + 1` of a shared operand element of a valid 16-bit MMA.** -/
theorem byteLoc_pair {s : TcMma.OperandSpec} {op : TcMma.Operand} {m : Nat} {l : Loc}
    (hk : s.descriptor.kind = .f16 .bf16 .f32)
    (hd : (match op with | .a => s.a | .b => s.b).start % 2 = 0 ∧
      (match op with | .a => s.a | .b => s.b).leading % 2 = 0 ∧
      (match op with | .a => s.a | .b => s.b).stride % 2 = 0)
    (h : s.byteLoc op (2 * m) = some l) :
    s.byteLoc op (2 * m + 1) = some ⟨l.space, l.cta, l.addr + 1⟩ ∧ l.addr % 2 = 0 := by
  have hw : s.descriptor.kind.width = 2 := by simp [hk, TcMma.Kind.width]
  have hk16 : s.descriptor.kind.k = 16 := by simp [hk, TcMma.Kind.k]
  have e1 : (2 * m + 1) / 32 = 2 * m / 32 := by omega
  have e2 : (2 * m + 1) / 2 = 2 * m / 2 := by omega
  have hm : (2 * m + 1) % 2 = 1 := by omega
  have hm0 : 2 * m % 2 = 0 := by omega
  unfold TcMma.OperandSpec.byteLoc at h ⊢
  simp only [hw, hk16, show 16 * 2 = 32 from rfl, e1, e2, hm, hm0] at h ⊢
  have c1 : TcMma.Valid s.descriptor ∧ 2 * m / 32 <
      (if op = TcMma.Operand.a ∧ s.descriptor.ws = true ∧ s.descriptor.m < 128 then 128
        else op.extent s.descriptor) := by
    by_contra hn
    rw [ite_eq_left hn] at h
    cases h
  have c2 : ¬(op = TcMma.Operand.a ∧ s.aTmem.isSome = true) := by
    intro hn
    rw [ite_eq_right (not_not.mpr c1), ite_eq_left hn] at h
    cases h
  rw [ite_eq_right (not_not.mpr c1), ite_eq_right c2] at h ⊢
  obtain ⟨addr, hba, hl⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hb1, ha2⟩ := byteAddress_pair hd.1 hd.2.1 hd.2.2 hba
  obtain rfl := (Option.some.inj hl)
  refine ⟨?_, ha2⟩
  simp only [bind, pure] at hl ⊢
  exact (congrArg (fun o => Option.bind o _) hb1).trans rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot
