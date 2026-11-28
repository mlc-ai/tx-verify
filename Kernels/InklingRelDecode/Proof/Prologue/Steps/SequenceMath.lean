-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Divide
import Kernels.InklingRelDecode.Gen.StepPrologue
import Lemmas.Flow.SegChain
import Lemmas.Flow.Scalars

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

set_option maxRecDepth 100000
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {d : D}
local notation "F" => facts Q L g w d

private theorem as_bits (v : BitVec 64)
    (h : subValue d.seq (subValue d.last d.first) = .bits 32 v) :
    valueOf Q L g w d = Function.update (valueOf Q L g w d) 482 (.bits 32 v) := by
  funext r
  by_cases hr : r=482
  · subst r; rw [Function.update_self]; exact h
  · simp [hr]

theorem seg_bias (x) (hx : subValue d.seq (subValue d.last d.first) = .bits 32 x) :
    Seg kernel Assumptions.all L g 1 43 (F 43) 44 (F 44) := by
  intro t ht
  unfold facts at *
  rw [as_bits x hx] at ht ⊢
  seg_fp ht using
    (change Value.bits 32 _ = Value.bits 32 (addi (Lib.word (subValue d.seq _)) (-1023))
     rw [hx]
     simp only [Lib.word,Value.regBits,Option.getD_some,addi,r32,truncBits_idem])

theorem seg_clip_bias : Seg kernel Assumptions.all L g 2 44 (F 44) 46 (F 46) := by
  intro t ht
  seg_fp ht using rfl

theorem seg_blocks (x) (hx : subValue d.seq (subValue d.last d.first) = .bits 32 x) :
    Seg kernel Assumptions.all L g 4 46 (F 46) 50 (F 50) := by
  intro t ht
  change At t 46 (factsFrom _ _) at ht
  unfold facts at *
  rw [as_bits x hx] at ht ⊢
  have pastEq : Lib.word (subValue d.seq (subValue d.last d.first)) = r32 x := by rw [hx]; rfl
  seg_fp ht using
    (change Value.bits 32 _ = Value.bits 32 (div128 (Lib.word (subValue d.seq _)))
     rw [pastEq]
     simp only [div128,add32,shru,shrs,r32,truncBits_idem])

theorem seg_ceiling :
    Seg kernel Assumptions.all L g 5 51 (F 51) 56 (F 56) := by
  intro t ht
  seg_fp ht using rfl

private theorem low_mod (a : Nat) : r32 (W (a%2^32)) = r32 (W a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [r32,W,truncBits,BitVec.toNat_ofNat]
  omega

theorem seg_sum (hs : Q.splits < 2^32) :
    Seg kernel Assumptions.all L g 3 56 (F 56) 59 (F 59) := by
  intro t ht
  have h₁ : Q.splits % 4294967296 = Q.splits := Nat.mod_eq_of_lt hs
  have h₂ := low_mod ((L.ctaidOf (g/L.block)).get .x)
  change truncBits 32 (BitVec.ofNat 64 (_ % 4294967296)) = truncBits 32 (BitVec.ofNat 64 _) at h₂
  seg_fp ht using simp [valueOf,copyReg,registerValue,h₁,W,add32,not32,div128,r32,h₂]

private theorem quotient (hs : Q.splits < 2^32) :
    SegU kernel Assumptions.all L g 59 (F 59) 60 (F 60) := by
  apply div_span (valueOf Q L g w d) Flow.code_59 (by decide)
    (by decide +kernel) (by decide +kernel) rfl rfl _ _
  · dsimp only [iters]
    rw [Nat.mod_eq_of_lt hs]
    rfl
  · intro r hr
    have keys : (ctlLive 60).all (fun r => decide (r=486 ∨ r ∈ ctlLive 59)) := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp keys r hr)

theorem seg_clip : Seg kernel Assumptions.all L g 1 60 (F 60) 61 (F 61) := by
  intro t ht
  seg_fp ht using rfl

private theorem add_word (s : Value) (hn : ∀ pw gen sp off, s ≠ .ptr pw gen sp off) :
    .bits 32 (addi (Lib.word s) 127) = Lib.addBase s 127 := by
  cases s <;> first | exact False.elim (hn _ _ _ _ rfl) |
    (apply congrArg (Value.bits 32); apply BitVec.eq_of_toNat_eq
     simp only [addi,r32,i32,truncBits,BitVec.toNat_ofNat,BitVec.toNat_ofInt,
       BitVec.toNat_add]
     norm_num; omega)

private theorem ceiling_input (hn : ∀ pw gen sp off, d.seq ≠ .ptr pw gen sp off) :
    SegU kernel Assumptions.all L g 50 (F 50) 51 (F 51) := by
  apply Lib.sum_span (V := valueOf Q L g w d) (r := 612) (dst := 630) (δ := 127)
    (op := .imm 127) false (by decide) Flow.code_50 (by decide) (by decide +kernel)
    (add_word d.seq hn) (fun _ _ => ⟨rfl,rfl⟩)
  intro r hr
  have keys : (ctlLive 51).all (fun r => decide (r=630 ∨ r ∈ ctlLive 50)) := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp keys r hr)

theorem sequence_math {m} (hp : Pre Q L m) (x) (hx : subValue d.seq (subValue d.last d.first) =
    .bits 32 x) : SegU kernel Assumptions.all L g 43 (F 43) 61 (F 61) := by
  have hs : Q.splits<2^32 := by have := hp.splitsRange; omega
  have hn : ∀ pw gen sp off, d.seq ≠ .ptr pw gen sp off := by
    rintro pw gen sp off eq
    rw [eq] at hx
    cases hx
  exact (SegU.of_seg (((seg_bias x hx).comp seg_clip_bias).comp (seg_blocks x hx))).comp
    ((ceiling_input hn).comp ((SegU.of_seg (seg_ceiling.comp (seg_sum hs))).comp
      ((quotient hs).comp (SegU.of_seg seg_clip))))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
