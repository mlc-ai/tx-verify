-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
import Kernels.InklingRelDecode.Gen.StepPrologue
import Kernels.InklingRelDecode.Gen.StepPrologue01
import Kernels.InklingRelDecode.Gen.StepPrologue02
import Kernels.InklingRelDecode.Gen.StepPrologue03
import Kernels.InklingRelDecode.Gen.StepPrologue04
import Lemmas.Flow.SegChain
import Lemmas.Flow.SignedBits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

set_option maxRecDepth 100000
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {d : D}
local notation "F" => facts Q L g w d

private theorem mul_u32 (a b : Nat) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (a % 2 ^ 32)) *
      truncBits 32 (BitVec.ofNat 64 (b % 2 ^ 32)))) = u32 (a * b) := by
  unfold u32 b32
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have h1 (x : Nat) : x % 2 ^ 32 % 2 ^ 64 = x % 2 ^ 32 :=
    Nat.mod_eq_of_lt (by have := Nat.mod_lt x (by norm_num : 0 < 2 ^ 32); omega)
  have h2 (m : Nat) : m % 2 ^ 64 % 2 ^ 32 = m % 2 ^ 32 :=
    Nat.mod_mod_of_dvd m (by norm_num)
  simp only [h1, Nat.mod_mod, h2, Nat.mul_mod a b]

private theorem mod_right (a b : Nat) : u32 (a * (b % 2 ^ 32)) = u32 (a * b) := by
  unfold u32
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem seg_s190 : Seg kernel Assumptions.all L g 1 190 (F 189) 191 (F 191) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff]
    rw [mod_right]
    exact mul_u32 _ _)

private theorem madw (a c : Nat) :
    Value.bits (2 * 32) (intBits (2 * 32) (intOf IType.s 32 (truncBits 32 (BitVec.ofNat 64 a)) *
      intOf IType.s 32 (truncBits 32 (BitVec.ofInt 64 4)) +
      intOf IType.s (2 * 32) (truncBits (2 * 32) (BitVec.ofNat 64 c)))) =
      u64 (Lib.sx a * 4 + c) := by
  have h := Lib.madwide_s32 a 4 c
  have e : (BitVec.ofInt 64 4) = BitVec.ofNat 64 4 := rfl
  have s4 : Lib.sx 4 = 4 := by decide
  rw [e]
  unfold u64 b64
  show Value.bits 64 _ = _
  refine congrArg (Value.bits 64) ?_
  simpa [s4] using h

private theorem sx_mod (n : Nat) : Lib.sx (n % 2 ^ 32) = Lib.sx n := by
  unfold Lib.sx
  simp

theorem seg_s191 : Seg kernel Assumptions.all L g 1 191 (F 191) 192 (F 192) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, btRow]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff]
    rw [madw, sx_mod])

theorem seg_s194 : Seg kernel Assumptions.all L g 1 194 (F 193) 195 (F 195) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, blkOff]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff])

private theorem madwB (x : BitVec 64) (c : Nat) :
    Value.bits (2 * 32) (intBits (2 * 32) (intOf IType.s 32 (truncBits 32 x) *
      intOf IType.s 32 (truncBits 32 (BitVec.ofInt 64 4)) +
      intOf IType.s (2 * 32) (truncBits (2 * 32) (BitVec.ofNat 64 c)))) =
      u64 (Lib.sx x.toNat * 4 + c) := by
  have e : BitVec.ofNat 64 x.toNat = x := by
    apply BitVec.eq_of_toNat_eq
    simp
  have := madw x.toNat c
  rwa [e] at this

private theorem u64_mod (a c : Nat) : u64 (a + c % 2 ^ 64) = u64 (a + c) := by
  unfold u64
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem seg_s195 : Seg kernel Assumptions.all L g 1 195 (F 195) 196 (F 196) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, blockPtr, btRow, blkIx]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceSub, Nat.reduceMul, add_zero]
    rw [madwB, u64_mod])

theorem seg_s218 : Seg kernel Assumptions.all L g 1 218 (F 217) 219 (F 219) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, blockPtr]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceSub, Nat.reduceMul]
    show Value.bits _ _ = _
    norm_bits [u64])

theorem seg_s234 : Seg kernel Assumptions.all L g 1 234 (F 231) 235 (F 235) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff]
    show Value.bits _ _ = _
    norm_bits [u32])

theorem seg_s235 : Seg kernel Assumptions.all L g 1 235 (F 235) 236 (F 236) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff]
    show Value.bits _ _ = _
    norm_bits [u32])

theorem seg_s238 : Seg kernel Assumptions.all L g 1 238 (F 237) 239 (F 239) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, blkOff]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff])

theorem seg_s239 : Seg kernel Assumptions.all L g 1 239 (F 239) 240 (F 240) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, blockPtr, btRow, blkIx]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceSub, Nat.reduceMul, add_zero]
    rw [madwB, u64_mod])

theorem seg_s260 : Seg kernel Assumptions.all L g 1 260 (F 259) 261 (F 261) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, blockPtr]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceSub, Nat.reduceMul]
    show Value.bits _ _ = _
    norm_bits [u64])

theorem seg_s276 : Seg kernel Assumptions.all L g 1 276 (F 273) 277 (F 277) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff]
    show Value.bits _ _ = _
    norm_bits [u32])

theorem seg_s277 : Seg kernel Assumptions.all L g 1 277 (F 277) 278 (F 278) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff]
    show Value.bits _ _ = _
    norm_bits [u32])

theorem seg_s280 : Seg kernel Assumptions.all L g 1 280 (F 279) 281 (F 281) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, blkOff]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff])

theorem seg_s281 : Seg kernel Assumptions.all L g 1 281 (F 281) 282 (F 282) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, blockPtr, btRow, blkIx]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceSub, Nat.reduceMul, add_zero]
    rw [madwB, u64_mod])

theorem seg_s302 : Seg kernel Assumptions.all L g 1 302 (F 301) 303 (F 303) := by
  intro t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_query]
    simp only [queryValue, blockPtr]
    simp (disch := decide +kernel) only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceSub, Nat.reduceMul]
    show Value.bits _ _ = _
    norm_bits [u64])

/-- The block-table row of the request, at pcs 190 and 191. -/
theorem block_row : SegU kernel Assumptions.all L g 190 (F 189) 192 (F 192) :=
  SegU.of_seg (seg_s190.comp seg_s191)

theorem block_arrive_0 : SegU kernel Assumptions.all L g 194 (F 193) 197 (F 197) :=
  (SegU.of_seg (seg_s194.comp seg_s195)).comp (cross (by decide +kernel : crossCheck 196 196 197))

theorem block_arrive_1 : SegU kernel Assumptions.all L g 238 (F 237) 241 (F 241) :=
  (SegU.of_seg (seg_s238.comp seg_s239)).comp (cross (by decide +kernel : crossCheck 240 240 241))

theorem block_arrive_2 : SegU kernel Assumptions.all L g 280 (F 279) 283 (F 283) :=
  (SegU.of_seg (seg_s280.comp seg_s281)).comp (cross (by decide +kernel : crossCheck 282 282 283))

theorem block_half_0 : SegU kernel Assumptions.all L g 218 (F 217) 220 (F 220) :=
  (SegU.of_seg seg_s218).comp (cross (by decide +kernel : crossCheck 219 219 220))

theorem block_half_1 : SegU kernel Assumptions.all L g 260 (F 259) 262 (F 262) :=
  (SegU.of_seg seg_s260).comp (cross (by decide +kernel : crossCheck 261 261 262))

theorem block_half_2 : SegU kernel Assumptions.all L g 302 (F 301) 304 (F 304) :=
  (SegU.of_seg seg_s302).comp (cross (by decide +kernel : crossCheck 303 303 304))

theorem block_mid_1 : SegU kernel Assumptions.all L g 234 (F 231) 236 (F 236) :=
  SegU.of_seg (seg_s234.comp seg_s235)

theorem block_mid_2 : SegU kernel Assumptions.all L g 276 (F 273) 278 (F 278) :=
  SegU.of_seg (seg_s276.comp seg_s277)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
