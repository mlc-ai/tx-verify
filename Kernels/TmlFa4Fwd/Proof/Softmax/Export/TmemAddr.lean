-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Code
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Softmax.PlainMaxK
public import Lemmas.Flow.TcLdTmpl
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Kernels.TmlFa4Fwd.Flow.Code.Part054
import Kernels.TmlFa4Fwd.Flow.Code.Part079
import Kernels.TmlFa4Fwd.Flow.Code.Part080
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Flow.Code.Part105
import Lemmas.Flow.TcAddr
import Lemmas.Flow.ElemAccess
import Tactics.KernelRfl

@[expose] public section

/-! # The softmax warps' Tensor Memory addresses

Every `tcgen05.ld` (the score loads `sld`, `sldw`) and `tcgen05.st` (the P stores `pst`) of a
softmax warp is of shape `.32x32b` at an address whose column field is the stage's score base
`tmS` (0 or 128, the lane quarter in bits 21 and 22) or-ed with an offset below 128, so below 256;
with 32 (load) or 16 (store) registers the access stays below column 512 (`soft_tc`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem andi_low (x : BitVec 64) : (andi x 6291456).toNat % 65536 = 0 := by
  simp only [andi, r32, i32, truncBits, BitVec.toNat_and, BitVec.toNat_ofNat,
    BitVec.toNat_ofInt]
  rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.and_mod_two_pow]
  have : (6291456 : Int) % (2 ^ 64 : Nat) = 6291456 := by norm_num
  rw [this]
  simp

theorem or32_low {x y : BitVec 64} (hx : x.toNat % 65536 < 256) (hy : y.toNat % 65536 = 0) :
    (or32 x y).toNat % 65536 < 256 := by
  simp only [or32, r32, truncBits, BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.or_mod_two_pow]
  refine Nat.or_lt_two_pow (n := 8) ?_ ?_ <;> omega

theorem tmS_low (L : Launch) (g : Nat) : (tmS L g).toNat % 65536 < 256 := by
  refine or32_low ?_ (andi_low _)
  simp only [sel]
  split <;> decide

theorem tmS_lt (L : Launch) (g : Nat) : (tmS L g).toNat < 2 ^ 32 := by
  simp only [tmS, or32, r32, truncBits, BitVec.toNat_or, BitVec.toNat_ofNat]
  exact Nat.or_lt_two_pow (by omega) (by omega)

theorem ori_low {x : BitVec 64} (hx : x.toNat % 65536 < 256) {n : Int} (h0 : 0 ≤ n)
    (h1 : n < 256) : (Mma.ori x n).toNat % 65536 < 256 := by
  simp only [Mma.ori, r32, i32, truncBits, BitVec.toNat_or, BitVec.toNat_ofNat,
    BitVec.toNat_ofInt]
  rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.or_mod_two_pow]
  refine Nat.or_lt_two_pow (n := 8) ?_ ?_ <;> omega

theorem ld_at {d : D} {t : TState} {gd : Option (Nat × Bool)} {ds : List Nat} {ta a0 : Nat}
    {e : Event} {o : Option TState}
    (hat : (Softmax.code p L g).AtD d t)
    (_hc : kernel.code[d.site.pc]? = some ⟨gd, .tcLd ds ta .s32x32b none⟩)
    (hm : (ta, b32 a0) ∈ facts p L g d) (ha0 : a0 < 2 ^ 32)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t (Op.tcLd ds ta .s32x32b none)) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.ld a vals sh)) :
    a = a0 ∧ sh = .s32x32b ∧ vals.length = ds.length := by
  have hr := holds_mem hat.2.2.2.2 hm
  obtain ⟨vals', he⟩ := fires_tcLd_at hr ha0 hf ⟨a, vals, sh, hk⟩
  have hl := fires_tcLd_len (by intro s hs; cases hs) hf hk
  rw [he] at hk
  simp only [Kind.tc.injEq, TcKind.ld.injEq] at hk
  obtain ⟨rfl, rfl, rfl⟩ := hk
  exact ⟨rfl, rfl, hl⟩

theorem st_at {d : D} {t : TState} {gd : Option (Nat × Bool)} {ss : List Opnd} {ta a0 : Nat}
    {e : Event} {o : Option TState}
    (hat : (Softmax.code p L g).AtD d t)
    (_hc : kernel.code[d.site.pc]? = some ⟨gd, .tcSt ta ss .s32x32b⟩)
    (hm : (ta, b32 a0) ∈ facts p L g d) (ha0 : a0 < 2 ^ 32)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t (Op.tcSt ta ss .s32x32b)) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    a = a0 ∧ sh = .s32x32b ∧ vals.length = ss.length := by
  have hr := holds_mem hat.2.2.2.2 hm
  obtain ⟨rfl, rfl⟩ := fires_tcSt_at hr ha0 hf hk
  exact ⟨rfl, rfl, fires_tcSt_len (by intro s hs; cases hs) hf hk⟩

/-- A register of a plain round's P store that the round's data table does not name holds its
control table's value. -/
theorem pst_plain_mem {q : Fin 4} {v : V} {k : Fin 4} {acc : List Value} {r : Nat}
    {X : BitVec 64} (hr : r ∈ liveD (livePc ⟨.pst .plain q, v, k, acc⟩))
    (hv : valueOf p L g ⟨.pst .plain q, v, k, acc⟩ r = .bits 32 X)
    (hn : ((pPData p v).map Prod.fst).contains r = false) :
    (r, b32 X.toNat) ∈ factsD p L g ⟨.pst .plain q, v, k, acc⟩ := by
  rw [← b32_toNat, ← hv]
  have : valueOfD p L g ⟨.pst .plain q, v, k, acc⟩ r =
      valueOf p L g ⟨.pst .plain q, v, k, acc⟩ r := by
    simp only [valueOfD, valuesData, lookup_none_of_keys hn, Option.getD_none]
  rw [← this]
  exact Flow.mem_factsFrom hr

set_option hygiene false in
/-- A plain round's store site whose address register holds `X`. -/
macro "soft_stp " X:term : tactic => `(tactic| (
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨rfl, rfl, hl⟩ := st_at (a0 := ($X).toNat) hat hc
    (pst_plain_mem (by lit_mem) rfl
      (by kernel_rfl))
    (ori_lt _ _) hf hk
  refine ⟨rfl, ?_⟩
  rw [hl]
  have h : ∀ x : Nat, x < 256 → x + 16 ≤ 512 := fun x hx => by omega
  simp only [List.length_map, List.length_range, List.length_cons, List.length_nil]
  exact h _ (ori_low (tmS_low L g) (by norm_num) (by norm_num))))

set_option hygiene false in
/-- A load site whose address register holds `X`. -/
macro "soft_ld " X:term : tactic => `(tactic| (
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨rfl, rfl, hl⟩ := ld_at (a0 := ($X).toNat) hat hc
    (by rw [← b32_toNat]; exact Flow.mem_factsFrom (by lit_mem))
    (by first | exact tmS_lt L g | exact ori_lt _ _) hf hk
  refine ⟨rfl, ?_⟩
  rw [hl]
  have h : ∀ x : Nat, x < 256 → x + 32 ≤ 512 := fun x hx => by omega
  simp only [List.length_map, List.length_range, List.length_cons, List.length_nil]
  first
  | exact h _ (tmS_low L g)
  | exact h _ (ori_low (tmS_low L g) (by norm_num) (by norm_num))))

set_option hygiene false in
/-- A store site whose address register holds `X`. -/
macro "soft_st " X:term : tactic => `(tactic| (
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨rfl, rfl, hl⟩ := st_at (a0 := ($X).toNat) hat hc
    (by rw [← b32_toNat]; exact Flow.mem_factsFrom (by lit_mem))
    (by first | exact tmS_lt L g | exact ori_lt _ _) hf hk
  refine ⟨rfl, ?_⟩
  rw [hl]
  have h : ∀ x : Nat, x < 256 → x + 16 ≤ 512 := fun x hx => by omega
  simp only [List.length_map, List.length_range, List.length_cons, List.length_nil]
  exact h _ (ori_low (tmS_low L g) (by norm_num) (by norm_num))))

set_option maxHeartbeats 4000000 in
theorem sld_tc {r : Rd} {c : Fin 4} {v : V} {k : Fin 4} {acc : List Value} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (hat : (Softmax.code p L g).AtD ⟨.sld r c, v, k, acc⟩ t)
    (hc : kernel.code[(Site.sld r c).pc]? = some ins)
    (hf : Fires (Site.sld r c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.ld a vals sh)) :
    sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512 := by
  cases r <;> fin_cases c <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢
  · soft_ld tmS L g
  · soft_ld Mma.ori (tmS L g) 32
  · soft_ld Mma.ori (tmS L g) 64
  · soft_ld Mma.ori (tmS L g) 96
  · soft_ld tmS L g
  · soft_ld Mma.ori (tmS L g) 32
  · soft_ld Mma.ori (tmS L g) 64
  · soft_ld Mma.ori (tmS L g) 96
  · soft_ld tmS L g
  · soft_ld Mma.ori (tmS L g) 32
  · soft_ld Mma.ori (tmS L g) 64
  · soft_ld Mma.ori (tmS L g) 96

set_option maxHeartbeats 4000000 in
theorem sldw_tc {c : Fin 4} {v : V} {acc : List Value} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (hat : (Softmax.code p L g).AtD ⟨.sldw c, v, 0, acc⟩ t)
    (hc : kernel.code[(Site.sldw c).pc]? = some ins)
    (hf : Fires (Site.sldw c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.ld a vals sh)) :
    sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512 := by
  fin_cases c <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢
  · soft_ld tmS L g
  · soft_ld Mma.ori (tmS L g) 32
  · soft_ld Mma.ori (tmS L g) 64
  · soft_ld Mma.ori (tmS L g) 96

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
