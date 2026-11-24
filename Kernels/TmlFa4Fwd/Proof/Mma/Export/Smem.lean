-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Words
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Desc
import Kernels.TmlFa4Fwd.Proof.Mma.Ref
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The shared descriptors of the MMA warp's operands, as records -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **A descriptor with the fixed high word**: start `16 w`, leading `16 t`, stride 1024, the
128-byte swizzle. -/
theorem decode_desc {lo : BitVec 64} {w t : Nat} (hlo : lo.toNat = 65536 * t + w) (hw : w < 32768)
    (ht : t < 2048) : TcShared.decode (lo ||| dhi <<< 32).toNat =
      some ⟨16 * w, 16 * t, 1024, 0, false, false, .b128⟩ := by
  rw [toNat_join (by omega), dhi_val, hlo]
  obtain ⟨x, hx⟩ : ∃ x, 65536 * t + w + 1073758272 * 2 ^ 32 = x := ⟨_, rfl⟩
  rw [hx]
  obtain ⟨e1, e2, e0, hlt, h15, h31⟩ : x % 2 ^ 15 * 16 = 16 * w ∧
      x / 2 ^ 16 % 2 ^ 15 * 16 = 16 * t ∧ x / 2 ^ 32 = 1073758272 ∧ x < 2 ^ 64 ∧
      x / 2 ^ 15 % 2 = 0 ∧ x / 2 ^ 31 % 2 = 0 := by
    norm_num at hx ⊢
    omega
  have hd : ∀ k, x / 2 ^ (32 + k) = 1073758272 / 2 ^ k := fun k => by
    rw [pow_add, ← Nat.div_div_eq_div_mul, e0]
  have e3 : x / 2 ^ 32 % 2 ^ 14 * 16 = 1024 := by rw [e0]; decide
  have e61 : x / 2 ^ 61 = 2 := hd 29
  have e46 : x / 2 ^ 46 = 65537 := (hd 14).trans (by decide)
  have e54 : x / 2 ^ 54 = 256 := (hd 22).trans (by decide)
  have e49 : x / 2 ^ 49 = 8192 := (hd 17).trans (by decide)
  have e52 : x / 2 ^ 52 = 1024 := (hd 20).trans (by decide)
  have e53 : x / 2 ^ 53 = 512 := (hd 21).trans (by decide)
  clear hd hx e0
  unfold TcShared.decode
  rw [e61, e46, e54, e49, e52, e53, e1, e2, e3, h15, h31]
  norm_num at hlt
  simp [TcShared.decodeSwizzle, hlt]

theorem and_val {y : BitVec 64} {A : Nat} (hy : y.toNat = A / 16) (hA : A % 1024 = 0)
    (hlt : A < 2 ^ 18) : (andi y 16320).toNat = A / 16 := by
  show (r32 y &&& i32 16320).toNat = _
  rw [BitVec.toNat_and, toNat_r32, show (i32 16320).toNat = 16320 from rfl, hy,
    Nat.mod_eq_of_lt (by omega)]
  exact and_16320 _ (by omega) (by omega)

theorem ori16_val {x : BitVec 64} (hx : x.toNat < 2 ^ 16) :
    (ori x 65536).toNat = 65536 + x.toNat := by
  have hi : (i32 65536).toNat = 2 ^ 16 := rfl
  have hr : (r32 x).toNat = x.toNat := by rw [toNat_r32]; omega
  simp only [ori, BitVec.toNat_or, hr, hi]
  rw [Nat.or_two_pow_eq_add_of_lt hx]
  omega

theorem ori26_val {x : BitVec 64} (hx : x.toNat < 2 ^ 16) :
    (ori x 67108864).toNat = 67108864 + x.toNat := by
  have hi : (i32 67108864).toNat = 2 ^ 26 := rfl
  have hr : (r32 x).toNat = x.toNat := by rw [toNat_r32]; omega
  simp only [ori, BitVec.toNat_or, hr, hi]
  rw [Nat.or_two_pow_eq_add_of_lt (by omega)]
  omega

/-- The address word of a K/V slot. -/
theorem slot_shru (hp : Pre p L m) {n : Nat} (hn : n < 3) :
    (shru (addi (Epilogue.add32 (sbW L) (Epilogue.shl (iw n) 15)) 68608) 4).toNat =
      (L.sharedBase + 68608 + 32768 * n) / 16 := by
  have hs := hp.shared
  have h15 : (Epilogue.shl (iw n) 15).toNat = 32768 * n := by
    interval_cases n <;> rfl
  have hb : (sbW L).toNat = L.sharedBase := by
    simp only [sbW, BitVec.toNat_ofNat]; omega
  have h0 : (Epilogue.add32 (sbW L) (Epilogue.shl (iw n) 15)).toNat = L.sharedBase + 32768 * n := by
    have h := iv_add32 (show Iv (sbW L).toNat (sbW L).toNat (sbW L) from ⟨le_rfl, le_rfl⟩)
      (show Iv (Epilogue.shl (iw n) 15).toNat (Epilogue.shl (iw n) 15).toNat _ from
        ⟨le_rfl, le_rfl⟩) (by omega)
    unfold Iv at h
    omega
  generalize Epilogue.add32 (sbW L) (Epilogue.shl (iw n) 15) = x at h0 ⊢
  have h1 : Iv ((x.toNat + 68608) / 2 ^ 4) ((x.toNat + 68608) / 2 ^ 4) (shru (addi x 68608) 4) :=
    iv_shru (iv_addi (show Iv x.toNat x.toNat x from ⟨le_rfl, le_rfl⟩) 68608 (by omega)) 4
      (by decide) (by omega)
  unfold Iv at h1
  omega

/-- **The B descriptor words of a K/V slot.** -/
theorem slotDesc_val (hp : Pre p L m) {n : Nat} (hn : n < 3) :
    (slotDesc L (iw n) 65536).toNat = 65536 + (L.sharedBase + 68608 + 32768 * n) / 16 ∧
      (slotDesc L (iw n) 67108864).toNat =
        67108864 + (L.sharedBase + 68608 + 32768 * n) / 16 := by
  have hs := hp.shared
  have h := and_val (slot_shru hp hn) (by omega) (by omega)
  have hlt : (andi (shru (addi (Epilogue.add32 (sbW L) (Epilogue.shl (iw n) 15)) 68608) 4)
      16320).toNat < 2 ^ 16 := by rw [h]; omega
  exact ⟨(ori16_val hlt).trans (by rw [h]), (ori26_val hlt).trans (by rw [h])⟩

/-- The K block's first descriptor word is slot 0's. -/
theorem kv0_val (hp : Pre p L m) : (shSrc L {} 0).toNat =
    65536 + (L.sharedBase + 68608) / 16 := by
  have hs := hp.shared
  have hy : (shru (BitVec.ofNat 64 (L.sharedBase + 68608)) 4).toNat =
      (L.sharedBase + 68608) / 16 := by
    have h1 : Iv ((L.sharedBase + 68608) / 2 ^ 4) ((L.sharedBase + 68608) / 2 ^ 4)
        (shru (BitVec.ofNat 64 (L.sharedBase + 68608)) 4) :=
      iv_shru (iv_lit _ (by omega)) 4 (by decide) (by omega)
    unfold Iv at h1
    omega
  have h := and_val hy (by omega) (by omega)
  have hlt : (andi (shru (BitVec.ofNat 64 (L.sharedBase + 68608)) 4) 16320).toNat < 2 ^ 16 := by
    rw [h]; omega
  exact (ori16_val hlt).trans (by rw [h])

/-- The Q descriptors' base word. -/
theorem qx_val' (hp : Pre p L m) : (qx L).toNat = 65536 + (L.sharedBase + 35840) / 16 := by
  have hs := hp.shared
  have hy : (shru (addi (sbW L) 35840) 4).toNat = (L.sharedBase + 35840) / 16 := by
    have h0 : Iv L.sharedBase L.sharedBase (sbW L) := iv_lit _ (by omega)
    have h1 : Iv ((L.sharedBase + 35840) / 2 ^ 4) ((L.sharedBase + 35840) / 2 ^ 4)
        (shru (addi (sbW L) 35840) 4) :=
      iv_shru (iv_addi h0 35840 (by omega)) 4 (by decide) (by omega)
    unfold Iv at h1
    omega
  have h := and_val hy (by omega) (by omega)
  have hlt : (andi (shru (addi (sbW L) 35840) 4) 16320).toNat < 2 ^ 16 := by rw [h]; omega
  exact (ori16_val hlt).trans (by rw [h])

/-- The offset of step `j` in 16-byte units: 2 per step in a box, 1024 to the second box. -/
def qn (j : Fin 8) : Nat := 1024 * (j.val / 4) + 2 * (j.val % 4)

theorem qoff_qn : ∀ j : Fin 8, qoff j = (qn j : Int) := by decide
theorem qn_le : ∀ j : Fin 8, qn j ≤ 1030 := by decide
theorem qn_zero : ∀ j : Fin 8, j = 0 → qn j = 0 := by decide

theorem addi_val {x : BitVec 64} {n : Nat} (h : x.toNat + n < 2 ^ 32) :
    (addi x n).toNat = x.toNat + n := by
  have := iv_addi (show Iv x.toNat x.toNat x from ⟨le_rfl, le_rfl⟩) n h
  unfold Iv at this
  omega

theorem qlo_val {x : BitVec 64} (h : x.toNat < 2 ^ 31) (j : Fin 8) :
    (qlo x j).toNat = x.toNat + qn j := by
  unfold qlo
  split
  · rename_i hj; rw [qn_zero j hj, Nat.add_zero]
  · rw [qoff_qn]
    have := qn_le j
    exact addi_val (by omega)

theorem pvlo_val {x : BitVec 64} (h : x.toNat < 2 ^ 31) (j : Fin 8) :
    (pvlo x j.val).toNat = x.toNat + 128 * j.val := by
  have h1 : (addi x 640).toNat = x.toNat + 640 := addi_val (n := 640) (by omega)
  have h2 : (addi (addi x 640) 128).toNat = x.toNat + 768 := by
    have := addi_val (x := addi x 640) (n := 128) (by omega)
    rw [h1] at this
    exact this
  fin_cases j
  · rfl
  · exact addi_val (n := 128) (by omega)
  · exact addi_val (n := 256) (by omega)
  · exact addi_val (n := 384) (by omega)
  · exact addi_val (n := 512) (by omega)
  · exact h1
  · exact h2
  · have := addi_val (x := addi (addi x 640) 128) (n := 128) (by omega)
    rw [h2] at this
    exact this

/-- **The A descriptors of the QK MMAs**: the Q stage's. -/
theorem qkA_decode (hp : Pre p L m) (b : Fin 4) (j : Fin 8) {da : TcShared.Descriptor}
    (h : TcShared.decode (qv L (neg (.qk b j)) j).toNat = some da) :
    da = Tm.qkA L (b.val % 2) j := by
  have hs := hp.shared
  have hx := qx_val' hp
  have hq := qn_le j
  have hl := qlo_val (x := qx L) (by omega) j
  have key : ∀ {lo : BitVec 64} {st : Nat}, st < 2 →
      lo.toNat = 65536 + ((L.sharedBase + 3072 + 32768 * st) / 16 + qn j) →
      TcShared.decode (lo ||| dhi <<< 32).toNat = some (Tm.qkA L st j) := by
    intro lo st hst hlo
    rw [decode_desc (t := 1) (w := (L.sharedBase + 3072 + 32768 * st) / 16 + qn j) (by omega)
      (by omega) (by decide)]
    simp only [Tm.qkA, Tm.kDesc, qn, Option.some.injEq, TcShared.Descriptor.mk.injEq, and_true,
      mul_one]
    unfold qn at hq
    omega
  have hb : neg (.qk b j) = decide (b.val % 2 = 0) := rfl
  rw [hb] at h
  by_cases h0 : b.val % 2 = 0
  · simp only [h0, decide_true, qv, ↓reduceIte, qinit] at h ⊢
    rw [qstep_join (by omega)] at h
    have h2 : (addi (qlo (qx L) j) (-2048)).toNat = (qlo (qx L) j).toNat - 2048 := by
      have := iv_addi_neg (show Iv (qlo (qx L) j).toNat (qlo (qx L) j).toNat _ from
        ⟨le_rfl, le_rfl⟩) 2048 (by omega) (by omega)
      unfold Iv at this
      have e : (-((2048 : Nat) : Int)) = -2048 := rfl
      rw [e] at this
      omega
    rw [key (st := 0) (by decide) (by omega)] at h
    exact (Option.some.inj h).symm
  · have h1 : b.val % 2 = 1 := by omega
    simp only [h0, decide_false, qv, Bool.false_eq_true, ↓reduceIte, qinit] at h
    rw [key (st := 1) (by decide) (by omega)] at h
    rw [h1]
    exact (Option.some.inj h).symm

/-- A K descriptor of a slot. -/
theorem kB_decode (hp : Pre p L m) {x : BitVec 64} {n : Nat} (hn : n < 3)
    (hx : x.toNat = 65536 + (L.sharedBase + 68608 + 32768 * n) / 16) (j : Fin 8)
    {db : TcShared.Descriptor} (h : TcShared.decode (qlo x j ||| dhi <<< 32).toNat = some db) :
    db = Tm.qkB L n j := by
  have hs := hp.shared
  have hq := qn_le j
  have hl := qlo_val (x := x) (by omega) j
  rw [decode_desc (t := 1) (w := (L.sharedBase + 68608 + 32768 * n) / 16 + qn j) (by omega)
    (by omega) (by decide)] at h
  rw [← Option.some.inj h]
  simp only [Tm.qkB, Tm.kDesc, qn, TcShared.Descriptor.mk.injEq, and_true, mul_one]
  unfold qn at hq
  omega

/-- A V descriptor of a slot. -/
theorem vB_decode (hp : Pre p L m) {x : BitVec 64} {n : Nat} (hn : n < 3)
    (hx : x.toNat = 67108864 + (L.sharedBase + 68608 + 32768 * n) / 16) (j : Fin 8)
    {db : TcShared.Descriptor} (h : TcShared.decode (pvlo x j.val ||| dhi <<< 32).toNat = some db) :
    db = Tm.pvB L n j := by
  have hs := hp.shared
  have hj := j.isLt
  have hl := pvlo_val (x := x) (by omega) j
  rw [decode_desc (t := 1024) (w := (L.sharedBase + 68608 + 32768 * n) / 16 + 128 * j.val)
    (by omega) (by omega) (by decide)] at h
  rw [← Option.some.inj h]
  simp only [Tm.pvB, Tm.mnDesc, TcShared.Descriptor.mk.injEq, and_true]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
