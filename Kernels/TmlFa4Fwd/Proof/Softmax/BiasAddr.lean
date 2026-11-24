-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
public import Lemmas.Flow.UbFree
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.Align
import Kernels.TmlFa4Fwd.Proof.Softmax.Safe
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Where the softmax warps read the bias

A lane's bias loads read four words of the bias window of its stage, `[sb + 166912 + 32768 st,
sb + 199680 + 32768 st)`: each address is a swizzled offset, which stays in its 128-byte row
(`bld_acc`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 add32 addi shl andi)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem add32_nat {x y : BitVec 64} {a b : Nat} (hx : x.toNat = a) (hy : y.toNat = b)
    (hab : a + b < 2 ^ 32) : (add32 x y).toNat = a + b := by
  simp only [add32, r32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, hx, hy]
  omega

/-- The swizzle keeps the 128-byte row. -/
theorem swz_row {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (swz x).toNat / 128 = x.toNat / 128 := by
  have e : (swz x).toNat = (andi (Epilogue.shru x 3) 112).toNat ^^^ x.toNat := by
    simp only [swz, Epilogue.xor32, r32, truncBits, BitVec.toNat_xor, BitVec.toNat_ofNat]
    have h1 : (andi (Epilogue.shru x 3) 112).toNat < 2 ^ 32 := by
      simp only [andi, r32, i32, truncBits, BitVec.toNat_and, BitVec.toNat_ofNat]
      refine lt_of_le_of_lt Nat.and_le_left ?_
      omega
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have h2 : (andi (Epilogue.shru x 3) 112).toNat < 128 := by
    simp only [andi, r32, i32, truncBits, BitVec.toNat_and, BitVec.toNat_ofNat]
    refine lt_of_le_of_lt Nat.and_le_right ?_
    decide
  rw [e]
  have : (128 : Nat) = 2 ^ 7 := by decide
  rw [this, Nat.xor_div_two_pow, Nat.div_eq_of_lt (by omega), Nat.zero_xor]

theorem tid_row (n : Nat) (hn : n < 512) :
    (andi (shl (BitVec.ofNat 64 n) 7) 16256).toNat = 128 * (n % 128) := by
  have key : ∀ n < 512, (andi (shl (BitVec.ofNat 64 n) 7) 16256).toNat = 128 * (n % 128) := by
    decide +kernel
  exact key n hn

theorem bOff_nat (hw : g % L.block / 32 < 8) :
    (bOff L g).toNat = 32768 * (g % L.block / 32 / 4) := by
  have key : ∀ w < 8, (Epilogue.sel (Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3) (i32 32768)
      (i32 0)).toNat = 32768 * (w / 4) := by decide +kernel
  exact key _ hw

theorem i32_nat {n : Nat} (hn : n < 2 ^ 31) : (i32 (n : Int)).toNat = n := by
  simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

theorem addi_nat {x : BitVec 64} {a n : Nat} (hx : x.toNat = a) (hn : n < 2 ^ 31)
    (han : a + n < 2 ^ 32) : (addi x (n : Int)).toNat = a + n := by
  have h := i32_nat hn
  show (truncBits 32 (r32 x + i32 (n : Int))).toNat = _
  generalize i32 (n : Int) = y at h ⊢
  simp only [r32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, hx, h]
  omega

theorem rowSb_nat (hp : Pre p L m) :
    (rowSb L g).toNat = L.sharedBase + 128 * (g % L.block % 128) := by
  have hb : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hs := hp.shared.2.1
  refine add32_nat ?_ (by rw [tidW_eq hp]; exact tid_row _ hb) (by omega)
  simp only [Mma.sbW, BitVec.toNat_ofNat]
  omega

/-- The bias addresses lie in the lane's rows of its stage's window. -/
theorem bAddr_row (hp : Pre p L m) (hw : g % L.block / 32 < 8) {n : Nat} (hn : n ≤ 199000) :
    (bAddr L g n).toNat / 128 =
      (L.sharedBase + 128 * (g % L.block % 128) + 32768 * (g % L.block / 32 / 4) + n) / 128 := by
  have hs := hp.shared.2.1
  have h1 := add32_nat (rowSb_nat (g := g) hp) (bOff_nat hw) (by omega)
  have h2 := addi_nat h1 (n := n) (by omega) (by omega)
  show (swz _).toNat / 128 = _
  rw [swz_row (by rw [h2]; omega), h2]

theorem bAddr0_row (hp : Pre p L m) (hw : g % L.block / 32 < 8) :
    (bAddr0 L g).toNat / 128 =
      (L.sharedBase + 128 * (g % L.block % 128) + 32768 * (g % L.block / 32 / 4) + 166912) /
        128 ∧ (bAddr0 L g).toNat < 2 ^ 18 + 2 ^ 17 := by
  have hs := hp.shared.2.1
  have h0 := addi_nat (rowSb_nat (g := g) hp) (n := 166912) (by omega) (by omega)
  have h1 := swz_row (x := addi (rowSb L g) ((166912 : Nat) : Int)) (by rw [h0]; omega)
  rw [h0] at h1
  have h2 := add32_nat (x := swz (addi (rowSb L g) ((166912 : Nat) : Int))) (a := _) rfl
    (bOff_nat (g := g) hw) (by omega)
  have e : bAddr0 L g = add32 (swz (addi (rowSb L g) ((166912 : Nat) : Int))) (bOff L g) := rfl
  rw [e, h2]
  omega

/-- The address register and offset of a bias load, and the word the register holds. -/
def bldBase (b : Bool) (c : Fin 16) : Nat :=
  (if b then
    [4170, 4034, 4030, 4026, 4022, 4018, 4014, 4010, 4170, 4006, 4002, 3998, 3994, 3990, 3986, 3982]
  else
    [2784, 2846, 2842, 2838, 2834, 2830, 2826, 2822, 2784, 2818, 2814, 2810, 2806, 2802, 2798,
      2794]).getD c.val 0
def bldOff (c : Fin 16) : Int := if c.val = 8 then 16384 else 0
def bldX (L : Launch) (g : Nat) (c : Fin 16) : BitVec 64 :=
  if c.val = 0 ∨ c.val = 8 then bAddr0 L g
  else bAddr L g (bOffs.getD (if c.val < 8 then 14 - c.val else 15 - c.val) 0)

theorem bld_tmpl (b : Bool) (c : Fin 16) : ∃ ins ds, kernel.code[(Site.bld b c).pc]? = some ins ∧
    ds.length = 4 ∧ ∀ L g t, eventTmpl Assumptions.all L g t ins.op =
      loadTmpl Assumptions.all L g t .shared false 32 ds (bldBase b c) (bldOff c) := by
  cases b <;> fin_cases c <;> exact ⟨_, _, by code_lookup, rfl, fun _ _ _ => rfl⟩

set_option maxHeartbeats 4000000 in
/-- The address register of a bias load. -/
theorem bld_reg (b : Bool) (c : Fin 16) (k : Fin 4) (v : V) (acc : List Value) {t : TState}
    (hat : (code p L g).AtD ⟨.bld b c, v, k, acc⟩ t) :
    t.regs (bldBase b c) = some (.bits 32 (bldX L g c)) := by
  have hF := hat.2.2.2.2
  cases b <;> fin_cases c
  · exact (PTX.Flow.regs_of_factsFrom (r := 2784) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2846) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2842) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2838) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2834) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2830) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2826) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2822) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2784) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2818) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2814) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2810) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2806) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2802) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2798) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 2794) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 4170) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 4034) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 4030) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 4026) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 4022) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 4018) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 4014) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 4010) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 4170) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 4006) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 4002) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 3998) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 3994) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 3990) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 3986) hF (by lit_mem)).trans (by soft_val')
  · exact (PTX.Flow.regs_of_factsFrom (r := 3982) hF (by lit_mem)).trans (by soft_val')

/-- The address word and offset of a bias load. -/
def BldAddr (L : Launch) (g : Nat) (x : BitVec 64) (off : Int) : Prop :=
  (x = bAddr0 L g ∧ (off = 0 ∨ off = 16384)) ∨ ∃ n : Nat, (n : Int) ∈ bOffs ∧
    x = bAddr L g n ∧ off = 0

theorem bld_addr (L : Launch) (g : Nat) (c : Fin 16) : BldAddr L g (bldX L g c) (bldOff c) := by
  have key : ∀ i < 14, ∃ n : Nat, (n : Int) ∈ bOffs ∧ bOffs.getD i 0 = n := by
    intro i hi
    refine ⟨(bOffs.getD i 0).toNat, ?_, ?_⟩ <;> revert i <;> decide
  unfold BldAddr bldX bldOff
  by_cases h0 : c.val = 0
  · exact .inl ⟨by simp [h0], .inl (by simp [h0])⟩
  by_cases h8 : c.val = 8
  · exact .inl ⟨by simp [h8], .inr (by simp [h8])⟩
  obtain ⟨n, hn, he⟩ := key (if c.val < 8 then 14 - c.val else 15 - c.val) (by split <;> omega)
  exact .inr ⟨n, hn, by simp only [h0, h8, or_self, ↓reduceIte]; rw [he], by simp [h8]⟩

/-- The half (columns) of the window a bias address is in. -/
theorem BldAddr.row (hp : Pre p L m) (hw : g % L.block / 32 < 8) {x : BitVec 64} {off : Int}
    (h : BldAddr L g x off) : ∃ a : Fin 2,
      (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat / 128 =
        (L.sharedBase + 128 * (g % L.block % 128) + 32768 * (g % L.block / 32 / 4) + 166912 +
          16384 * a.val) / 128 := by
  have hs := hp.shared.2.1
  have hs1 := hp.shared.1
  rcases h with ⟨rfl, hoff⟩ | ⟨n, hn, rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := bAddr0_row (g := g) hp hw
    generalize (bAddr0 L g) = x at h1 h2 ⊢
    rcases hoff with rfl | rfl
    · refine ⟨0, ?_⟩
      simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
      simp only [Fin.val_zero]
      omega
    · refine ⟨1, ?_⟩
      simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
      simp only [Fin.val_one]
      omega
  · have hb : (166912 ≤ n ∧ n < 167040) ∨ 183296 ≤ n ∧ n < 183424 := by
      simp only [bOffs, List.mem_cons, List.not_mem_nil, or_false] at hn
      omega
    have h1 := bAddr_row (g := g) hp hw (n := n) (by omega)
    generalize (bAddr L g n) = x at h1 ⊢
    have h2 : x.toNat < 2 ^ 32 := by omega
    rcases hb with hb | hb
    · refine ⟨0, ?_⟩
      simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
      simp only [Fin.val_zero]
      omega
    · refine ⟨1, ?_⟩
      simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
      simp only [Fin.val_one]
      omega

/-- **A bias read** is of one word in the lane's row of one of its stage's two boxes. -/
theorem bld_acc (hp : Pre p L m) (hw : g % L.block / 32 < 8) {b : Bool} {c : Fin 16}
    {k : Fin 4} {v : V} {ac : List Value} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code p L g).AtD ⟨.bld b c, v, k, ac⟩ t)
    (hc : kernel.code[(Site.bld b c).pc]? = some ins) {pc : Nat}
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) {acc : Acc}
    {bs : List (Option Byte)} (hk : e.kind = .rd acc bs) :
    acc.size = 4 ∧ acc.loc.space = .shared ∧ acc.loc.cta = g / L.block ∧ acc.loc.addr % 4 = 0 ∧
      ∃ a : Fin 2, acc.loc.addr / 128 =
        (L.sharedBase + 128 * (g % L.block % 128) + 32768 * (g % L.block / 32 / 4) + 166912 +
          16384 * a.val) / 128 := by
  obtain ⟨ins', ds, hc', hds, hE⟩ := bld_tmpl b c
  obtain rfl := Option.some.inj (hc.symm.trans hc')
  have hr := bld_reg b c k v ac hat
  obtain ⟨a, ha⟩ := (bld_addr L g c).row hp hw
  rw [hE] at hf
  unfold loadTmpl at hf
  rw [effAddr_shared32 hr] at hf
  have hsub : t.sub = k.val := hat.2.1
  have hk4 := k.isLt
  generalize (truncBits 32 (truncBits 32 (bldX L g c) + BitVec.ofInt 64 (bldOff c))).toNat = A
    at ha hf
  by_cases hal : A % 16 = 0
  · have hA : ∀ j, elemAcc ⟨.shared, g / L.block, A⟩ (32 / 8) ds.length j =
        .ok { loc := Loc.at ⟨.shared, g / L.block, A⟩ (4 * j), size := 4, elem := j } := by
      intro j
      unfold elemAcc
      rw [hds, ite_eq_right (by simp [hal])]
      rfl
    simp only [bind, Except.bind, hA, hsub, Bool.false_eq_true, ↓reduceIte, Fires] at hf
    obtain ⟨bytes, -, hek, -⟩ := hf
    rw [hek] at hk
    simp only [Kind.rd.injEq] at hk
    obtain ⟨rfl, -⟩ := hk
    refine ⟨rfl, rfl, rfl, ?_, a, ?_⟩
    · simp only [Loc.at]
      omega
    · simp only [Loc.at]
      omega
  · have hA : ∀ j, elemAcc ⟨.shared, g / L.block, A⟩ (32 / 8) ds.length j =
        .error .misaligned := by
      intro j
      unfold elemAcc
      rw [hds, ite_eq_left (by simp [hal])]
      rfl
    simp only [bind, Except.bind, hA, Fires] at hf
    rw [hf.1] at hk
    cases hk

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
