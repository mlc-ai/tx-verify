-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Loads
public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.Correction.Shapes
public import Kernels.TmlFa4Fwd.Proof.Lib.TcAddr
public import Lemmas.Flow.ElemAccess
public import Lemmas.Flow.TcLdTmpl
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part126
import Kernels.TmlFa4Fwd.Flow.Code.Part127
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part129
import Kernels.TmlFa4Fwd.Flow.Code.Part130
import Kernels.TmlFa4Fwd.Flow.Code.Part131
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part133
import Kernels.TmlFa4Fwd.Flow.Code.Part134
import Kernels.TmlFa4Fwd.Flow.Code.Part135
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part138
import Kernels.TmlFa4Fwd.Flow.Code.Part139
import Kernels.TmlFa4Fwd.Flow.Code.Part140
import Kernels.TmlFa4Fwd.Flow.Code.Part141

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Shape

@[expose] public section

/-! # The correction warps' Tensor Memory addresses

Every `tcgen05.ld` and `tcgen05.st` of a correction warp is of shape `.32x32b` at an address
whose column field is `256 + 16 c` (plus 128 in the second stage) for a rescale chunk `c` and
`256 + 8 j` (plus 128) for a final chunk `j`, the base `tm0` of the table (`%r1629`, the lane
quarter in bits 21 and 22, column 256); with sixteen (rescale) or eight (final) registers the
access stays below column 512 (`corr_tc`). The address register's value is read off the role's
table at the site (`ld_at`, `st_at`), the column by `bv_decide` on the table's word. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem ld_at {d : Control.D} {t : TState} {gd : Option (Nat × Bool)} {ds : List Nat} {ta a0 : Nat}
    {e : Event} {o : Option TState}
    (hat : (Control.code p L g).AtD d t)
    (_hc : kernel.code[d.site.pc]? = some ⟨gd, .tcLd ds ta .s32x32b none⟩)
    (hm : (ta, b32 a0) ∈ Control.facts p L g d) (ha0 : a0 < 2 ^ 32)
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

theorem st_at {d : Control.D} {t : TState} {gd : Option (Nat × Bool)} {ss : List Opnd} {ta a0 : Nat}
    {e : Event} {o : Option TState}
    (hat : (Control.code p L g).AtD d t)
    (_hc : kernel.code[d.site.pc]? = some ⟨gd, .tcSt ta ss .s32x32b⟩)
    (hm : (ta, b32 a0) ∈ Control.facts p L g d) (ha0 : a0 < 2 ^ 32)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t (Op.tcSt ta ss .s32x32b)) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    a = a0 ∧ sh = .s32x32b ∧ vals.length = ss.length := by
  have hr := holds_mem hat.2.2.2.2 hm
  obtain ⟨rfl, rfl⟩ := fires_tcSt_at hr ha0 hf hk
  exact ⟨rfl, rfl, fires_tcSt_len (by intro s hs; cases hs) hf hk⟩

theorem tm0_low (L : Launch) (g : Nat) : (tm0 L g).toNat % 65536 = 256 := by
  simp only [tm0, Mma.ori, shl, r32, i32, truncBits, BitVec.toNat_or, BitVec.toNat_ofNat,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofInt]
  generalize quarter L g = q
  norm_num [Nat.shiftLeft_eq]
  rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.or_mod_two_pow]
  have h : q.toNat * 2097152 % 4294967296 % 18446744073709551616 % 2 ^ 16 = 0 := by omega
  rw [h]
  rfl

theorem tm1_low (L : Launch) (g : Nat) : (tm1 L g).toNat % 65536 = 384 := by
  simp only [tm1, Mma.ori, shl, r32, i32, truncBits, BitVec.toNat_or, BitVec.toNat_ofNat,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofInt]
  generalize quarter L g = q
  norm_num [Nat.shiftLeft_eq]
  rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.or_mod_two_pow]
  have h : q.toNat * 2097152 % 4294967296 % 18446744073709551616 % 2 ^ 16 = 0 := by omega
  rw [h]
  rfl

theorem addi_low (x : BitVec 64) {n : Int} (h0 : 0 ≤ n) (h1 : n < 2 ^ 31) :
    (addi x n).toNat % 65536 = (x.toNat % 65536 + n.toNat) % 65536 := by
  simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  have : (n % (2 ^ 64 : Nat) : Int).toNat = n.toNat := by omega
  omega

set_option hygiene false in
/-- One Tensor Memory load site: the instruction, the address register's word, its column. -/
macro "corr_ld_case" : tactic => `(tactic| (
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨rfl, rfl, hl⟩ := ld_at hat hc
    (by rw [← b32_toNat]; exact Flow.mem_factsFrom (by lit_mem))
    (by first | exact truncBits_lt _ | exact ori_lt _ _) hf hk
  refine ⟨rfl, ?_⟩
  rw [hl]
  simp only [List.length_map, List.length_range, List.length_cons, List.length_nil, fStage]
  simp (disch := norm_num) only [addi_low, tm0_low, tm1_low]
  norm_num))

set_option hygiene false in
/-- One Tensor Memory store site. -/
macro "corr_st_case" : tactic => `(tactic| (
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨rfl, rfl, hl⟩ := st_at hat hc
    (by rw [← b32_toNat]; exact Flow.mem_factsFrom (by lit_mem))
    (by first | exact truncBits_lt _ | exact ori_lt _ _) hf hk
  refine ⟨rfl, ?_⟩
  rw [hl]
  simp only [List.length_map, List.length_range, List.length_cons, List.length_nil, fStage]
  simp (disch := norm_num) only [addi_low, tm0_low, tm1_low]
  norm_num))

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 40000000 in
theorem rld_tc {st : Fin 2} {c : Fin 8} {v : Control.V} {k : Fin 4} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : (Control.code p L g).AtD ⟨.rld st c, v, k⟩ t)
    (hc : kernel.code[(Site.rld st c).pc]? = some ins)
    (hf : Fires (Site.rld st c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.ld a vals sh)) :
    sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512 := by
  fin_cases st <;> fin_cases c <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢ <;>
    corr_ld_case

set_option maxHeartbeats 40000000 in
theorem rldw_tc {st : Fin 2} {c : Fin 8} {v : Control.V} {k : Fin 4} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : (Control.code p L g).AtD ⟨.rldw st c, v, k⟩ t)
    (hc : kernel.code[(Site.rldw st c).pc]? = some ins)
    (hf : Fires (Site.rldw st c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.ld a vals sh)) :
    sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512 := by
  fin_cases st <;> fin_cases c <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢ <;>
    corr_ld_case

set_option maxHeartbeats 40000000 in
theorem rst_tc {st : Fin 2} {c : Fin 8} {v : Control.V} {k : Fin 4} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : (Control.code p L g).AtD ⟨.rst st c, v, k⟩ t)
    (hc : kernel.code[(Site.rst st c).pc]? = some ins)
    (hf : Fires (Site.rst st c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512 := by
  fin_cases st <;> fin_cases c <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢ <;>
    corr_st_case

set_option maxHeartbeats 40000000 in
theorem fld_tc {st : Fin 2} {j : Fin 16} {v : Control.V} {k : Fin 4} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : (Control.code p L g).AtD ⟨.fld st j, v, k⟩ t)
    (hc : kernel.code[(Site.fld st j).pc]? = some ins)
    (hf : Fires (Site.fld st j).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.ld a vals sh)) :
    sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512 := by
  fin_cases st <;> fin_cases j <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢ <;>
    corr_ld_case

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 40000000 in
/-- **Every Tensor Memory load and store of a correction warp** is a `.32x32b` access below
column 512. -/
theorem corr_tc (hp : Pre p L m) {d : Control.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (Control.code p L g).AtD d t) (hi : (Control.code p L g).inv d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    (∀ a vals sh, e.kind = .tc (.ld a vals sh) →
      sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512) ∧
    (∀ a vals sh, e.kind = .tc (.st a vals sh) →
      sh = .s32x32b ∧ a % 65536 + vals.length ≤ 512) := by
  have shape := Control.shapeAt hp d hat hi hc hf
  obtain ⟨s, v, k⟩ := d
  refine ⟨fun a vals sh hk => ?_, fun a vals sh hk => ?_⟩
  · have hev := shape (by rw [hk]; nofun)
    cases s with
    | rld st c => exact rld_tc hat hc hf hk
    | rldw st c => exact rldw_tc hat hc hf hk
    | fld st j => exact fld_tc hat hc hf hk
    | _ => (simp only [Control.Ev, Control.D.scheduler, Ev] at hev; simp_all [rdOrUb, Epilogue.Ev,
        Site.toE]) <;>
      (unfold Epilogue.Ev at hev; split at hev <;> simp_all [Epilogue.isStore])
  · have hev := shape (by rw [hk]; nofun)
    cases s with
    | rst st c => exact rst_tc hat hc hf hk
    | _ => (simp only [Control.Ev, Control.D.scheduler, Ev] at hev; simp_all [rdOrUb, Epilogue.Ev,
        Site.toE]) <;>
      (unfold Epilogue.Ev at hev; split at hev <;> simp_all [Epilogue.isStore])

end PTX.Kernels.TmlFa4Fwd.Proof.Correction
