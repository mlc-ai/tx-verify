-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.PreIndex
import Kernels.InklingRelDecode.Gen.StepSoftmax
import Kernels.InklingRelDecode.Gen.StepSoftmax01
import Lemmas.Flow.FloatRun
import Lemmas.Flow.SegJump
import Lemmas.Flow.SignedBits
import Lemmas.Flow.BranchU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {v : Carry}
local notation "F" => facts e L g (D.mk (Softmax.Site.bar0) 0 v)
theorem mul_wide_word (a b : Nat) :
    truncBits 64 (BitVec.ofInt 64 (toSigned 32 (truncBits 32 (BitVec.ofNat 64 a)) *
      toSigned 32 (truncBits 32 (BitVec.ofNat 64 b)))) =
      BitVec.ofNat 64 ((sx a * sx b) % 2^64) := by
  have h := madwide_s32 a b 0
  rw [show intOf .s 64 (truncBits 64 (BitVec.ofNat 64 0)) = 0 by decide,
    Int.add_zero,Nat.add_zero] at h
  exact h

theorem add_unsigned_wide (a c : Nat) (small : a < 2^32) :
    Value.bits 64 (intBits 64 (intOf .u 32 (truncBits 32 (BitVec.ofNat 64 a)) *
      intOf .u 32 (truncBits 32 (BitVec.ofInt 64 2)) +
      intOf .u 64 (truncBits 64 (BitVec.ofNat 64 (c % 2^64))))) = u64 (c+a*2) := by
  change Value.bits 64 _ = Value.bits 64 _
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [intBits,intOf,truncBits,BitVec.toNat_ofInt,BitVec.toNat_ofNat]
  norm_num
  omega

theorem add_signed_wide (a c : Nat) :
    Value.bits 64 (intBits 64 (intOf .s 32 (truncBits 32 (BitVec.ofNat 64 (a % 2^32))) *
      intOf .s 32 (truncBits 32 (BitVec.ofInt 64 2)) +
      intOf .s 64 (truncBits 64 (BitVec.ofNat 64 (c % 2^64))))) = u64 (c+sx a*2) := by
  change Value.bits 64 _ = Value.bits 64 _
  rw [ofInt_two,madwide_s32,sx_two]
  congr 2
  simp only [sx,Nat.mod_mod]
  omega

local macro "address_eq" : tactic => `(tactic| (
  simp only [valueOf,scalarValue,u32,u64,Nat.reduceEqDiff,↓reduceIte]
  all_goals norm_bits [biasBase]))

private theorem addr_602 (ok : e.Ok) :
    SegU kernel Assumptions.all L g 602 (F 602) 603 (F 603) := by
  have off := ok.offsetWord
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using
    change Value.bits 64 (truncBits 64 (BitVec.ofInt 64 _)) = Value.bits 64 _
    rw [mul_wide_word]
    simp [sx]

private theorem addr_603 (ok : e.Ok) :
    SegU kernel Assumptions.all L g 603 (F 603) 604 (F 604) := by
  have off := ok.offsetWord
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using address_eq

private theorem addr_604 (ok : e.Ok) :
    SegU kernel Assumptions.all L g 604 (F 604) 605 (F 605) := by
  have off := ok.offsetWord
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using address_eq

private theorem addr_605 (ok : e.Ok) :
    SegU kernel Assumptions.all L g 605 (F 605) 606 (F 606) := by
  have off := ok.offsetWord
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using address_eq

private theorem addr_606 (ok : e.Ok) :
    SegU kernel Assumptions.all L g 606 (F 606) 607 (F 607) := by
  have off := ok.offsetWord
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using
    exact add_unsigned_wide _ _ (Nat.mod_lt _ (by decide))

private theorem addr_607 (ok : e.Ok) :
    SegU kernel Assumptions.all L g 607 (F 607) 608 (F 608) := by
  have off := ok.offsetWord
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using address_eq

private theorem addr_608 (ok : e.Ok) :
    SegU kernel Assumptions.all L g 608 (F 608) 609 (F 609) := by
  have off := ok.offsetWord
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using
    exact add_signed_wide _ _

private theorem addr_609 (ok : e.Ok) :
    SegU kernel Assumptions.all L g 609 (F 609) 610 (F 610) := by
  have off := ok.offsetWord
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using address_eq

private theorem addr_610 (ok : e.Ok) :
    SegU kernel Assumptions.all L g 610 (F 610) 611 (F 611) := by
  have off := ok.offsetWord
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using
    have hb : (g % L.block / 16 % 2)*64 < 2^32 := by omega
    convert add_unsigned_wide _ _ hb using 1
    unfold valueOf scalarValue biasBase u64
    simp only [Nat.reduceEqDiff,↓reduceIte]
    congr 3
    omega

theorem pre_address (ok : e.Ok) : SegU kernel Assumptions.all L g 599 (F 599) 611 (F 611) := by
  have scale : SegU kernel Assumptions.all L g 599 (F 599) 602 (F 602) := by ink_ctl
  apply scale.comp
  apply (addr_602 ok).comp
  apply (addr_603 ok).comp
  apply (addr_604 ok).comp
  apply (addr_605 ok).comp
  apply (addr_606 ok).comp
  apply (addr_607 ok).comp
  apply (addr_608 ok).comp
  apply (addr_609 ok).comp
  exact addr_610 ok

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
