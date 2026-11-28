-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.LoopRoute
import Kernels.InklingRelDecode.Gen.StepSoftmax04
import Kernels.InklingRelDecode.Gen.StepSoftmax08
import Kernels.InklingRelDecode.Flow.Code.Part014
import Lemmas.Flow.SegJump
import Lemmas.Flow.SignedBits
import Lemmas.Flow.BranchU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {v : Carry}
local notation "F" => facts e L g (D.mk (Softmax.Site.pre 63) 0 v)
theorem cvt_s64_s32 (a : Nat) :
    MemExt.same.extendBits 64 (cvtIntBits false IType.s 64 IType.s 32
      (truncBits 32 (BitVec.ofNat 64 a))) = b64 (sx a) := by
  simp only [MemExt.extendBits_same, cvtIntBits, intSat, intOf, intBits, ite_true,
    Bool.not_false, b64]
  rw [toSigned32_ofNat]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  unfold sx
  have h := Nat.mod_lt a (show 0 < 2 ^ 32 by decide)
  split_ifs with h1 <;> push_cast <;> omega

private theorem mask12 (t : Nat) (h : t < 256) : t*4 &&& 12 = t%4*4 := by
  revert t h; decide +kernel

theorem after_pre (ok : e.Ok) (thread : g % L.block < 256) :
    SegU kernel Assumptions.all L g 807 (F 806) 1049 (F 1049) := by
  have limit := limit_bound ok
  have range := ok.keyRange
  have split : e.split < 2^32 := by omega
  have splits : e.splits < 2^32 := by
    rw [Nat.add_mul,Nat.one_mul] at range
    omega
  have start : SegU kernel Assumptions.all L g 807 (F 806) 808 (F 808) := by
    ink_ctl
  have tsmall : (g % L.block * 4) % 4294967296 = g % L.block * 4 :=
    Nat.mod_eq_of_lt (by omega)
  have tsmall64 : (g % L.block * 4) % 18446744073709551616 = g % L.block * 4 :=
    Nat.mod_eq_of_lt (by omega)
  have index : SegU kernel Assumptions.all L g 808 (F 808) 812 (F 812) := by
    apply SegU.of_seg (n := 4)
    intro t ht
    seg_fp ht using
      simp only [valueOf,scalarValue,u32]
      all_goals norm_bits [tsmall,tsmall64,mask12 _ thread]
  have sign : SegU kernel Assumptions.all L g 812 (F 812) 813 (F 813) := by
    apply SegU.of_seg (n := 1)
    intro t ht
    seg_fp ht using
      change _ = b64 (sx e.blocks % 2^64)
      rw [Nat.mod_eq_of_lt (show sx e.blocks < 2^64 by
        unfold sx; have := Nat.mod_lt e.blocks (by decide : 0 < 2^32); omega)]
      exact cvt_s64_s32 _
  have len : SegU kernel Assumptions.all L g 813 (F 813) 814 (F 814) := by
    apply SegU.of_seg (n := 1)
    intro t ht
    seg_fp ht using seg_close [valueOf,scalarValue]
  have pack : SegU kernel Assumptions.all L g 814 (F 814) 943 (F 943) := by
    ink_ctl
  have shift : SegU kernel Assumptions.all L g 943 (F 943) 944 (F 944) := by
    apply SegU.of_seg (n := 1)
    intro t ht
    seg_fp ht using seg_close [valueOf,scalarValue,u32]
  have fill : SegU kernel Assumptions.all L g 944 (F 944) 946 (F 946) := by ink_ctl
  have beginLoop : SegU kernel Assumptions.all L g 946 (F 946) 948 (F 1049) := by
    apply SegU.of_seg (n := 2)
    intro t ht
    seg_fp ht using first | rfl | seg_close [valueOf,scalarValue,u32]
  apply start.comp (index.comp (sign.comp (len.comp (pack.comp ?_))))
  apply shift.comp (fill.comp (beginLoop.comp ?_))
  exact SegU.of_seg (seg_jmp Flow.code_948 (fun t _ => Lib.bra_rule t) (segFree (by decide)))

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
