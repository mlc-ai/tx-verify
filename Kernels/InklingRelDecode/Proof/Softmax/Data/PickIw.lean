-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.MaskConst

@[expose] public section

/-! # The two predicates that choose the path of the first window

Register 96 tests `n < nbias` (the block `n = split + i * splits` is before the first block with
relative logits), register 97 tests `128 n + 127 <= P0` (the block lies entirely before the words
past the first token). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

theorem w1V_483 {d : D} (hs : d.c.site = .waitLd) : w1V e L g d 483 = b32 e.nbias := by
  rw [w1V_eq hs (by decide +kernel)]
  unfold lookupD baseF
  simp only [lookup_append_eq, Control.facts, hs, lookup_factsFrom]
  have h : 483 ∈ ctlLive Site.waitLd.pc := by decide +kernel
  simp [h]
  simp [valueOf, scalarValue]

theorem w1V_1913 {d : D} (hs : d.c.site = .waitLd) :
    w1V e L g d 1913 = u32 (e.split + d.c.i * e.splits) := by
  rw [w1V_eq hs (by decide +kernel)]
  unfold lookupD baseF
  simp only [lookup_append_eq, Control.facts, hs, lookup_factsFrom]
  have h : 1913 ∈ ctlLive Site.waitLd.pc := by decide +kernel
  simp [h]
  simp [valueOf, scalarValue]

theorem w1V_482 {d : D} (hs : d.c.site = .waitLd) : w1V e L g d 482 = e.prior := by
  rw [w1V_eq hs (by decide +kernel)]
  unfold lookupD baseF
  simp only [lookup_append_eq, Control.facts, hs, lookup_factsFrom]
  have h : 482 ∉ ctlLive Site.waitLd.pc := by decide +kernel
  simp [dF, dFS, startF, hs, inRound, h, List.lookup]

theorem vP_96 (V : Nat → Value) : vP V 96 = Gen.w1p_v1299 V := by
  refine V'_out runP runP_ok (P := fun r v => r = 96 → v = Gen.w1p_v1299 V)
    (fun p hp => ?_) (show 96 ∈ runP.outs by decide +kernel) rfl
  change p ∈ Gen.w1p_facts1 V at hp
  simp only [Gen.w1p_facts1, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' (rcases hp with rfl | hp)
  all_goals first | (intro h; dsimp only at h; omega) | (intro _; rfl)

theorem vA_97 (V : Nat → Value) : vA V 97 = Gen.w1a_v1464 (vP V) := by
  refine V'_out runA runA_ok (P := fun r v => r = 97 → v = Gen.w1a_v1464 (vP V))
    (fun p hp => ?_) (show 97 ∈ runA.outs by decide +kernel) rfl
  change p ∈ Gen.w1a_facts6 (vP V) at hp
  simp only [Gen.w1a_facts6, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' (rcases hp with rfl | hp)
  all_goals first | (intro h; dsimp only at h; omega) | (intro _; rfl)

theorem setp_rr_w {cmp : Cmp} {d a b : Nat} (hab : b ≠ a) (x y : ℤ) (v : Value) :
    okVal v (coreF (.int ⟨.setp cmp none, .int .s 32, false, [some d], [.reg a, .reg b]⟩) [a, b]
      [w32 x, w32 y]) = .pred (compare cmp .s 32 (truncBits 32 (BitVec.ofInt 64 x))
        (truncBits 32 (BitVec.ofInt 64 y))) := by
  have h1 : lk [a, b] [w32 x, w32 y] a = w32 x := by simp [lk]
  have h2 : lk [a, b] [w32 x, w32 y] b = w32 y := by
    simp only [lk, List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hab,
      beq_self_eq_true, Option.getD_some]
  have hk : (DType.int IType.s 32).kind?.getD IType.b = IType.s := rfl
  have e : coreF (.int ⟨.setp cmp none, .int .s 32, false, [some d], [.reg a, .reg b]⟩) [a, b]
      [w32 x, w32 y] = .ok (.pred (compare cmp .s 32 (truncBits 32 (BitVec.ofInt 64 x))
        (truncBits 32 (BitVec.ofInt 64 y)))) := by
    simp only [coreF, coreW, oBits, h1, h2, pure, Except.pure, bind, Except.bind, DType.width]
    simp only [w32, trunc_idem, hk]
  rw [okVal_ok e]

/-- **Register 96**: the block is before the first block with relative logits. -/
theorem pick96_iff {d : D} (hs : d.c.site = .waitLd)
    (hn : (e.split + d.c.i * e.splits : ℤ) < 2 ^ 31) (hb : (e.nbias : ℤ) < 2 ^ 31) :
    pick96 (w1V e L g d) = decide (((e.split + d.c.i * e.splits : Nat) : ℤ) < e.nbias) := by
  have n1 : e.split + d.c.i * e.splits < 2 ^ 32 := by omega
  unfold pick96
  rw [vP_96]
  unfold Gen.w1p_v1299
  rw [w1V_1913 hs, w1V_483 hs]
  unfold u32
  rw [Nat.mod_eq_of_lt n1, b32_iw n1, b32_iw (by omega : e.nbias < 2 ^ 32)]
  unfold Gen.w1p_op1299
  rw [setp_rr_w (by decide)]
  simp only [predBool, compare]
  rw [toSigned_w (by omega) (by omega), toSigned_w (by omega) (by omega)]

/-- **Register 97**: the block lies entirely before the words past the first token. -/
theorem pick97_iff {d : D} (hs : d.c.site = .waitLd) {P0 : ℤ} (hp : e.prior = w32 P0)
    (hb : (e.split + d.c.i * e.splits) * 128 + 127 < 2 ^ 31) (h0 : 0 ≤ P0) (h1 : P0 < 2 ^ 31) :
    pick97 (w1V e L g d) =
      decide ((((e.split + d.c.i * e.splits) * 128 : Nat) : ℤ) + 127 ≤ P0) := by
  have n1 : (e.split + d.c.i * e.splits) * 128 < 2 ^ 32 := by omega
  unfold pick97
  rw [vA_97]
  unfold Gen.w1a_v1464 Gen.w1a_v1463
  have p1912 : vP (w1V e L g d) 1912 = w1V e L g d 1912 :=
    V'_notin runP runP_ok _ (by decide +kernel)
  have p482 : vP (w1V e L g d) 482 = w1V e L g d 482 :=
    V'_notin runP runP_ok _ (by decide +kernel)
  rw [p1912, p482, w1V_1912 hs, w1V_482 hs, hp]
  unfold u32
  rw [Nat.mod_eq_of_lt n1, b32_iw n1]
  unfold Gen.w1a_op1463 Gen.w1a_op1464
  rw [add_imm_w, setp_rr_w (by decide)]
  simp only [predBool, compare]
  rw [toSigned_w (by omega) (by omega), toSigned_w (by omega) (by omega)]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
