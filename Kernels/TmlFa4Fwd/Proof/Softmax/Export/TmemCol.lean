-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemAddr
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Kernels.TmlFa4Fwd.Flow.Code.Part054
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part079
import Kernels.TmlFa4Fwd.Flow.Code.Part080
import Kernels.TmlFa4Fwd.Flow.Code.Part101
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Flow.Code.Part105
import Kernels.TmlFa4Fwd.Flow.Code.Part115
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Lemmas.Flow.ElemAccess
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The columns of the softmax warps' Tensor Memory accesses

A score load `c` of a round reads the 32 columns `128 st + 32 c …` (`sld_col`), a P store `q` writes
the 16 columns `128 st + 64 + 16 q …` (`pst_col`), both with the shape `.32x32b`; `st` is the stage
of the lane's warp. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The first column of the lane's stage. -/
def colS (L : Launch) (g : Nat) : Nat := if stg L g then 128 else 0

theorem or32_col (x y : BitVec 64) :
    (or32 x y).toNat % 65536 = x.toNat % 65536 ||| y.toNat % 65536 := by
  simp only [or32, r32, truncBits, BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.or_mod_two_pow]
  congr 1 <;> omega

theorem tmS_col (L : Launch) (g : Nat) : (tmS L g).toNat % 65536 = colS L g := by
  unfold tmS colS
  rw [or32_col, andi_low, Nat.or_zero]
  cases stg L g <;> decide

theorem colS_cases (L : Launch) (g : Nat) : colS L g = 0 ∨ colS L g = 128 := by
  unfold colS; split <;> simp

theorem ori_low_eq (x : BitVec 64) {n : Nat} (hn : n < 128) :
    (Mma.ori x n).toNat % 65536 = x.toNat % 65536 ||| n := by
  simp only [Mma.ori, r32, i32, truncBits, BitVec.toNat_or, BitVec.toNat_ofNat,
    BitVec.toNat_ofInt]
  rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.or_mod_two_pow]
  congr 1 <;> omega

theorem ori_col (L : Launch) (g : Nat) {n : Nat} (hn : n < 128) :
    (Mma.ori (tmS L g) n).toNat % 65536 = colS L g + n := by
  rw [ori_low_eq _ hn, tmS_col]
  rcases colS_cases L g with hc | hc <;> rw [hc]
  · simp
  · simpa using (Nat.two_pow_add_eq_or_of_lt (i := 7) hn 1).symm

/-- The stage's first column is `128 st`, for a lane of the softmax warps. -/
theorem colS_eq (hw : g % L.block / 32 < 8) : colS L g = 128 * (g % L.block / 32 / 4) := by
  unfold colS stg warpW
  generalize g % L.block / 32 = w at hw ⊢
  interval_cases w <;> rfl

set_option hygiene false in
/-- A load site whose address register holds `X` of column `n`. -/
macro "col_ld " X:term:max n:num : tactic => `(tactic| (
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨rfl, rfl, hl⟩ := ld_at (a0 := ($X).toNat) hat hc
    (by rw [← b32_toNat]; exact Flow.mem_factsFrom (by lit_mem))
    (by first | exact tmS_lt L g | exact ori_lt _ _) hf hk
  refine ⟨rfl, ?_, hl⟩
  first | exact tmS_col L g | exact ori_col L g (n := $n) (by decide)))

set_option hygiene false in
/-- A store site whose address register holds `X` of column `n`. -/
macro "col_st " X:term:max n:num : tactic => `(tactic| (
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨rfl, rfl, hl⟩ := st_at (a0 := ($X).toNat) hat hc
    (by rw [← b32_toNat]; exact Flow.mem_factsFrom (by lit_mem))
    (by first | exact tmS_lt L g | exact ori_lt _ _) hf hk
  exact ⟨rfl, ori_col L g (n := $n) (by decide), hl⟩))

set_option hygiene false in
/-- A plain round's store site. -/
macro "col_stp " X:term:max n:num : tactic => `(tactic| (
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨rfl, rfl, hl⟩ := st_at (a0 := ($X).toNat) hat hc
    (pst_plain_mem (by lit_mem) rfl (by kernel_rfl)) (ori_lt _ _) hf hk
  exact ⟨rfl, ori_col L g (n := $n) (by decide), hl⟩))

set_option maxHeartbeats 4000000 in
/-- **A score load's columns.** -/
theorem sld_col {r : Rd} {c : Fin 4} {v : V} {k : Fin 4} {acc : List Value} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (hat : (Softmax.code p L g).AtD ⟨.sld r c, v, k, acc⟩ t)
    (hc : kernel.code[(Site.sld r c).pc]? = some ins)
    (hf : Fires (Site.sld r c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.ld a vals sh)) :
    sh = .s32x32b ∧ a % 65536 = colS L g + 32 * c.val ∧ vals.length = 32 := by
  cases r <;> fin_cases c <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢
  · col_ld (tmS L g) 0
  · col_ld (Mma.ori (tmS L g) 32) 32
  · col_ld (Mma.ori (tmS L g) 64) 64
  · col_ld (Mma.ori (tmS L g) 96) 96
  · col_ld (tmS L g) 0
  · col_ld (Mma.ori (tmS L g) 32) 32
  · col_ld (Mma.ori (tmS L g) 64) 64
  · col_ld (Mma.ori (tmS L g) 96) 96
  · col_ld (tmS L g) 0
  · col_ld (Mma.ori (tmS L g) 32) 32
  · col_ld (Mma.ori (tmS L g) 64) 64
  · col_ld (Mma.ori (tmS L g) 96) 96

set_option maxHeartbeats 4000000 in
/-- **A P store's columns.** -/
theorem pst_col {r : Rd} {q : Fin 4} {v : V} {k : Fin 4} {acc : List Value} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (hat : (Softmax.code p L g).AtD ⟨.pst r q, v, k, acc⟩ t)
    (hc : kernel.code[(Site.pst r q).pc]? = some ins)
    (hf : Fires (Site.pst r q).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    sh = .s32x32b ∧ a % 65536 = colS L g + (64 + 16 * q.val) ∧ vals.length = 16 := by
  cases r <;> fin_cases q <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢
  · col_st (Mma.ori (tmS L g) 64) 64
  · col_st (Mma.ori (tmS L g) 80) 80
  · col_st (Mma.ori (tmS L g) 96) 96
  · col_st (Mma.ori (tmS L g) 112) 112
  · col_st (Mma.ori (tmS L g) 64) 64
  · col_st (Mma.ori (tmS L g) 80) 80
  · col_st (Mma.ori (tmS L g) 96) 96
  · col_st (Mma.ori (tmS L g) 112) 112
  · col_st (Mma.ori (tmS L g) 64) 64
  · col_st (Mma.ori (tmS L g) 80) 80
  · col_st (Mma.ori (tmS L g) 96) 96
  · col_st (Mma.ori (tmS L g) 112) 112

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
