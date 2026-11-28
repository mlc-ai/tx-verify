-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QBar2
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Elect
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.BlockPointer
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.BlockRead

@[expose] public section

/-! # The strict spans of a preload block: the form of the facts and the closing tactics -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- The data facts name only registers of `Dk`. -/
theorem dF_keysIn {d : Data.D} {Dk : List Nat} {s : Site} (hs : d.c.site = s)
    (h : ∀ τ ∈ Data.tags s, τ.reg ∈ Dk) : ∀ p ∈ Data.dF Q L g d, p.1 ∈ Dk := by
  intro p hp
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hp
  exact h τ (hs ▸ hτ)

/-- An old exact stretch as a strict stretch of a preload site's value machine. -/
macro "pre_br" Dk:term "," t:term : tactic => `(tactic|
  exact PTX.Flow.Havoc.SegQ.of_seg_pre (Dk := $Dk)
  (dF_keysIn rfl (by dsimp only [dS]; decide +kernel)) Lib.rulesFrame $t rfl
  (by decide +kernel) (by decide +kernel)
  (PTX.Flow.Havoc.PlainSegs.mono (plainSegs_pro (a := 27) (b := 574) le_rfl) (by decide +kernel)
    (by decide +kernel)) (by decide +kernel) (by decide +kernel))

/-- The block-table words after the load of half `h` of block `b`. -/
def payUp (v : Data.Vals) (b : Fin 3) (h : Fin 2) (x : Value) : Data.Vals :=
  ⟨Function.update v.pay b (Function.update (v.pay b) h x), v.q⟩

theorem mul_u32 (a b : Nat) :
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

theorem mad_u32 (x a b c : Nat) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) *
      truncBits 32 (BitVec.ofNat 64 (a % 2 ^ 32)) + truncBits 32 (truncBits 32
        (truncBits 32 (BitVec.ofNat 64 (b % 2 ^ 32)) *
          truncBits 32 (BitVec.ofNat 64 (c % 2 ^ 32)))))) =
    u32 ((Lib.word (b32 x)).toNat * a + b * c) := by
  unfold u32 b32
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [Lib.word, Value.regBits, truncBits, BitVec.toNat_mul, BitVec.toNat_add,
    BitVec.toNat_ofNat, Option.getD_some]
  have h1 (x : Nat) : x % 2 ^ 32 % 2 ^ 64 = x % 2 ^ 32 :=
    Nat.mod_eq_of_lt (by have := Nat.mod_lt x (by norm_num : 0 < 2 ^ 32); omega)
  have h2 (m : Nat) : m % 2 ^ 64 % 2 ^ 32 = m % 2 ^ 32 :=
    Nat.mod_mod_of_dvd m (by norm_num)
  have h3 (m : Nat) : m % 2 ^ 32 % 2 ^ 64 % 2 ^ 32 = m % 2 ^ 32 := by rw [h1, Nat.mod_mod]
  simp only [h1, h2, h3, Nat.mod_mod]
  simp only [Nat.add_mod (_ * _) (_ * _), Nat.mul_mod _ a, Nat.mul_mod b c, Nat.mod_mod, h1, h2]
  generalize x % 2 ^ 32 * (a % 2 ^ 32) = A
  generalize b % 2 ^ 32 * (c % 2 ^ 32) = B
  omega

theorem mad2_u32 (x a n : Nat) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) *
      truncBits 32 (BitVec.ofNat 64 (a % 2 ^ 32)) + truncBits 32 (BitVec.ofNat 64 (n % 2 ^ 32)))) =
    u32 ((Lib.word (b32 x)).toNat * a + n) := by
  unfold u32 b32
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [Lib.word, Value.regBits, truncBits, BitVec.toNat_mul, BitVec.toNat_add,
    BitVec.toNat_ofNat, Option.getD_some]
  have h1 (x : Nat) : x % 2 ^ 32 % 2 ^ 64 = x % 2 ^ 32 :=
    Nat.mod_eq_of_lt (by have := Nat.mod_lt x (by norm_num : 0 < 2 ^ 32); omega)
  have h2 (m : Nat) : m % 2 ^ 64 % 2 ^ 32 = m % 2 ^ 32 :=
    Nat.mod_mod_of_dvd m (by norm_num)
  have h3 (m : Nat) : m % 2 ^ 32 % 2 ^ 64 % 2 ^ 32 = m % 2 ^ 32 := by rw [h1, Nat.mod_mod]
  simp only [h1, h2, h3, Nat.mod_mod]
  simp only [Nat.add_mod (_ * _) _, Nat.mul_mod _ a, Nat.mod_mod, h1, h2]
  generalize x % 2 ^ 32 * (a % 2 ^ 32) = A
  omega

theorem col_u32 (bc : Value) (n : Nat) :
    Value.bits 32 (truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 6)).toNat ≥ 32
      then 0 else truncBits 32 (truncBits 32 (andi (Lib.word bc) 1) <<<
        (truncBits 32 (BitVec.ofInt 64 6)).toNat)) + truncBits 32 (BitVec.ofNat 64 (n % 2 ^ 32)))) =
    u32 (64 * ((Lib.word bc).toNat % 2) + 0 + n) := by
  have h6 : (truncBits 32 (BitVec.ofInt 64 6)).toNat = 6 := by decide
  have h1 : (BitVec.ofInt 64 1).toNat = 1 := by decide
  rw [h6]
  simp only [ge_iff_le, Nat.reduceLeDiff, ↓reduceIte]
  unfold u32 b32
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, andi, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
    BitVec.toNat_and]
  rw [h1]
  simp only [Nat.mod_mod, Nat.reduceMod, Nat.reducePow]
  generalize (bc.regBits.getD 0).toNat = z
  simp only [Nat.and_one_is_mod, Nat.shiftLeft_eq]
  omega

theorem cmp_lt64 (n : Nat) (h : n < 128) :
    PTX.compare .lt .u 32 (truncBits 32 (BitVec.ofNat 64 n)) (truncBits 32 (BitVec.ofInt 64 64)) =
      decide (n < 64) := by
  simp [PTX.compare, truncBits]
  omega

theorem valueOf_copy {d : Control.D} {r : Nat} (h : copyReg r = true) :
    valueOf Q L g w d r = copyValue L d.broadcast r := by simp [valueOf, h]

/-- Close a computed register value against the stated one (multiplications added). -/
macro "pre_vals" : tactic => `(tactic| first
  | (simp (disch := decide +kernel) only [valueOf_copy, copyValue, Arith32.shl, andi,
      Lib.word, Value.regBits, Option.getD_some, r32, i32, truncBits_idem]; done)
  | (simp (disch := decide +kernel) only [valueOf_copy] <;> rfl)
  | (simp (disch := decide +kernel) only [valueOf_plain, registerValue, Option.getD_some,
      cmp_lt64 _ (Nat.mod_lt _ (by decide : 128 > 0))]; simp [queryReg, voteReg]; done)
  | pro_vals
  | (rw [mul_u32]; done)
  | (rw [mad_u32]; done)
  | (rw [mad2_u32]; done)
  | (rw [col_u32]; done))

/-- Normalize the data facts of a concrete preload site to explicit facts. -/
macro "pre_facts" : tactic => `(tactic| simp (config := {decide := true}) only [dFacts, dFactsAt,
  Data.dF, Data.tags, Data.pos, Data.early, Data.oldTags, Data.qTags, Data.qhs, List.map_cons,
  List.map_nil, List.cons_append, List.nil_append, Data.Tag.reg, Data.Tag.val, ↓reduceIte,
  Site.pc, Data.rowVal, Data.colVal, List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero,
  Fin.val_one, Fin.val_two, Nat.reduceAdd, Nat.reduceMul, elPc, initPc, Bool.false_eq_true,
  List.append_nil, arrPc, lbPc, pbPc, pshPc, pelPc, ptcPc, Control.lbBar, payUp,
  Function.update_self, Function.update_apply])

/-- A strict span inside a preload block. -/
macro "pre_seg" : tactic => `(tactic| (pre_facts; segq_ctlt proQt,
    (plainRules_pro (a := 27) (b := 574) le_rfl),
    (plainSegs_pro (a := 27) (b := 574) le_rfl), Lib.rulesFrame using pre_vals))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
