-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # The staging layout

Each staging store element lies in the 8 KB buffer of its warp group and slice parity
(`stagingOff_bounds`); within a group, distinct threads, chunks and elements write distinct
bytes (`stagingOff_inj`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

noncomputable section

namespace OutputRing

theorem xor_lt4 {a b : Nat} (ha : a < 4) (hb : b < 4) : a ^^^ b < 4 :=
  Nat.xor_lt_two_pow (n := 2) ha hb

/-- A staging element lies in its group's buffer of its slice parity. -/
theorem stagingOff_bounds {t b i el : Nat} (hi : i < 4) (he : el < 4) :
    Consumer.stagingBase t b ≤ Consumer.stagingOff t b i el ∧
      Consumer.stagingOff t b i el + 4 ≤ Consumer.stagingBase t b + 8192 := by
  have hx := xor_lt4 (a := t / 2 % 4) (b := i) (Nat.mod_lt _ (by decide)) hi
  simp only [Consumer.stagingBase, Consumer.stagingOff, Consumer.stage]
  omega

/-- Within a group, distinct threads, chunks and elements write distinct staging bytes. -/
theorem stagingOff_inj {t t' b b' i i' el el' : Nat} (hq : t / 32 / 4 = t' / 32 / 4)
    (hi : i < 4) (hi' : i' < 4) (he : el < 4) (he' : el' < 4)
    (h : Consumer.stagingOff t b i el = Consumer.stagingOff t' b' i' el') :
    t = t' ∧ b = b' ∧ i = i' ∧ el = el' := by
  have hx := xor_lt4 (a := t / 2 % 4) (b := i) (Nat.mod_lt _ (by decide)) hi
  have hx' := xor_lt4 (a := t' / 2 % 4) (b := i') (Nat.mod_lt _ (by decide)) hi'
  simp only [Consumer.stagingOff, Consumer.stage] at h
  have hel : el = el' := by omega
  have hxe : (t / 2 % 4) ^^^ i = (t' / 2 % 4) ^^^ i' := by omega
  have ht2 : t / 2 % 16 = t' / 2 % 16 := by omega
  have ht1 : t % 2 = t' % 2 := by omega
  have hw : t / 32 % 4 = t' / 32 % 4 := by omega
  have hbb : b = b' := by omega
  have htt : t = t' := by omega
  subst htt
  refine ⟨rfl, hbb, ?_, hel⟩
  have := congrArg (· ^^^ (t / 2 % 4)) hxe
  simp only [Nat.xor_comm (t / 2 % 4) i, Nat.xor_comm (t / 2 % 4) i', Nat.xor_assoc,
    Nat.xor_self, Nat.xor_zero] at this
  exact this

end OutputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
