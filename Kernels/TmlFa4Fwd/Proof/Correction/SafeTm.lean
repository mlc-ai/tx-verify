-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
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
import Lemmas.Flow.TmplOkMore
import Lemmas.Flow.UbFree
import Lemmas.Flow.WordBound

@[expose] public section

/-! # The correction warps' Tensor Memory loads are no undefined behaviour

A Tensor Memory load (`tcgen05.ld.32x32b`) faults when its address's lane field leaves the warp's
lane quarter (`tcDataAddressOk`). Every load address of the correction warps is the warp's
quarter shifted to the lane field (`tm0`: `(tid % 128 / 32) << 21`, plus a column below
`2 ^ 16`), so its lane field is the warp's lane base (`laneBase`: `tid / 32 % 4 * 32`). No state
fact is needed: the addresses are the table's functions of the lane. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem tid_toNat (hp : Pre p L m) : (tidW L g).toNat = g % L.block := by
  have hb := hp.block
  have h1 : g % L.block < 512 := hb ▸ Nat.mod_lt g (by rw [hb]; decide)
  simp only [tidW, Launch.oneDim_tidOf hp.cluster.2.2, Dim3.get, truncBits, BitVec.toNat_ofNat]
  omega

/-- The load base: the warp's quarter in the lane field, column 256. -/
theorem tm0_toNat (hp : Pre p L m) :
    (tm0 L g).toNat = g % L.block % 128 / 32 * 2 ^ 21 + 256 := by
  have hb := hp.block
  have h1 : g % L.block < 512 := hb ▸ Nat.mod_lt g (by rw [hb]; decide)
  have ht := tid_toNat (g := g) hp
  have hq : (quarter L g).toNat = g % L.block % 128 / 32 := by
    have hr : (rowW L g).toNat = g % L.block % 128 := by
      simp only [rowW, andi, BitVec.toNat_and]
      rw [show (i32 127).toNat = 2 ^ 7 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
      rw [r32_of_lt (by omega), ht]
    simp only [quarter, shru]
    rw [show (i32 5).toNat = 5 by decide]
    simp only [show ¬ (5 ≥ 32) by decide, ↓reduceIte, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    rw [r32_of_lt (by omega), hr]
  have hs : (shl (quarter L g) 21).toNat = g % L.block % 128 / 32 * 2 ^ 21 := by
    have := toNat_shl (k := 21) (quarter L g) (by decide)
    rw [show ((21 : Nat) : Int) = 21 from rfl] at this
    rw [this, r32_of_lt (by omega), hq]
    omega
  simp only [tm0, PTX.Kernels.TmlFa4Fwd.Proof.Mma.ori]
  have h256 : (i32 256).toNat = 256 := by decide
  rw [BitVec.toNat_or, r32_of_lt (by omega), hs, h256]
  have := Nat.two_pow_add_eq_or_of_lt (i := 21) (b := 256) (by decide) (g % L.block % 128 / 32)
  rw [Nat.mul_comm] at this
  omega

/-- The load base: the warp's quarter in the lane field, column 384. -/
theorem tm1_toNat (hp : Pre p L m) :
    (tm1 L g).toNat = g % L.block % 128 / 32 * 2 ^ 21 + 384 := by
  have hb := hp.block
  have h1 : g % L.block < 512 := hb ▸ Nat.mod_lt g (by rw [hb]; decide)
  have ht := tid_toNat (g := g) hp
  have hq : (quarter L g).toNat = g % L.block % 128 / 32 := by
    have hr : (rowW L g).toNat = g % L.block % 128 := by
      simp only [rowW, andi, BitVec.toNat_and]
      rw [show (i32 127).toNat = 2 ^ 7 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
      rw [r32_of_lt (by omega), ht]
    simp only [quarter, shru]
    rw [show (i32 5).toNat = 5 by decide]
    simp only [show ¬ (5 ≥ 32) by decide, ↓reduceIte, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    rw [r32_of_lt (by omega), hr]
  have hs : (shl (quarter L g) 21).toNat = g % L.block % 128 / 32 * 2 ^ 21 := by
    have := toNat_shl (k := 21) (quarter L g) (by decide)
    rw [show ((21 : Nat) : Int) = 21 from rfl] at this
    rw [this, r32_of_lt (by omega), hq]
    omega
  simp only [tm1, PTX.Kernels.TmlFa4Fwd.Proof.Mma.ori]
  have h256 : (i32 384).toNat = 384 := by decide
  rw [BitVec.toNat_or, r32_of_lt (by omega), hs, h256]
  have := Nat.two_pow_add_eq_or_of_lt (i := 21) (b := 384) (by decide) (g % L.block % 128 / 32)
  rw [Nat.mul_comm] at this
  omega

theorem addi_tm0 (hp : Pre p L m) {n : Int} (h0 : 0 ≤ n) (hn : n < 2 ^ 15) :
    (addi (tm0 L g) n).toNat = g % L.block % 128 / 32 * 2 ^ 21 + (256 + n.toNat) := by
  have h := tm0_toNat (g := g) hp
  have hb := hp.block
  have h1 : g % L.block < 512 := hb ▸ Nat.mod_lt g (by rw [hb]; decide)
  simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  rw [h]
  omega

/-- **An address of the warp's quarter is a supported `.32x32b` address.** -/
theorem tm_ok (hp : Pre p L m) {a c : Nat} (ha : a = g % L.block % 128 / 32 * 2 ^ 21 + c)
    (hc : c < 2 ^ 16) : tcDataAddressOk L g .s32x32b a = true := by
  have hb := hp.block
  subst ha
  simp only [tcDataAddressOk, TcShape.splitOk, tmemLaneFieldOk, laneBase, TcShape.lanes,
    Bool.true_and, Bool.or_eq_true, Bool.and_eq_true]
  refine ⟨by decide, .inr ⟨decide_eq_true ?_, decide_eq_true ?_⟩⟩ <;>
    simp only [hb, Nat.reducePow] <;> omega

set_option maxHeartbeats 8000000 in
/-- **No Tensor Memory load of the correction warps is undefined behaviour.** -/
theorem ld_safe (hp : Pre p L m) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (code p L g).AtD d t)
    (hc : kernel.code[(code p L g).pc d]? = some ins)
    (hf : Fires ((code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : (∃ st c, d.site = .rld st c) ∨ ∃ st j, d.site = .fld st j) (f : Fault) :
    e.kind ≠ .ub f := by
  have hblk : L.block % 32 = 0 := by rw [hp.block]
  have hreg : ∀ r ∈ Flow.live (livePc d), t.regs r = some (valueOf p L g d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hq : g % L.block % 128 / 32 < 4 := by omega
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  intro hk
  have hu := fires_ub hf hk
  rcases hs with ⟨st, c, rfl⟩ | ⟨st, j, rfl⟩
  · fin_cases st <;> fin_cases c <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      refine tcLd_word_ok hblk (by decide) (hreg _ (by lit_mem)) ?_ ?_ f hu
      all_goals first
        | (rw [tm0_toNat hp]; omega)
        | (rw [addi_tm0 hp (by decide) (by decide)]; omega)
        | (exact tm_ok hp (tm0_toNat hp) (by decide))
        | (exact tm_ok hp (tm1_toNat hp) (by decide))
        | (rw [tm1_toNat hp]; omega)
        | (exact tm_ok hp (addi_tm0 hp (by decide) (by decide)) (by decide))
  · fin_cases st <;> fin_cases j <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      refine tcLd_word_ok hblk (by decide) (hreg _ (by lit_mem)) ?_ ?_ f hu
      all_goals try simp only [fStage]
      all_goals first
        | (rw [tm0_toNat hp]; omega)
        | (rw [addi_tm0 hp (by decide) (by decide)]; omega)
        | (exact tm_ok hp (tm0_toNat hp) (by decide))
        | (exact tm_ok hp (tm1_toNat hp) (by decide))
        | (rw [tm1_toNat hp]; omega)
        | (exact tm_ok hp (addi_tm0 hp (by decide) (by decide)) (by decide))

/-- `tcSt_ok` with a word address register and register operands of four bytes. -/
theorem tcSt_word_ok {t : TState} {ta : Nat} {ss : List Opnd} {sh : TcShape} {x : BitVec 64}
    (hb : L.block % 32 = 0) (hn : sh.countOk ss.length = true)
    (hr : t.regs ta = some (.bits 32 x)) (ha : x.toNat < 2 ^ 32)
    (hs : tcDataAddressOk L g sh x.toNat = true)
    (hss : ∀ i < ss.length, ∃ r v, ss[i]? = some (.reg r) ∧ t.regs r = some v ∧ v.bytes = 4)
    (f : Fault) : eventTmpl Assumptions.all L g t (.tcSt ta ss sh) ≠ .ub f := by
  obtain ⟨vals, hv, h4⟩ := mapM_regs_ok (L := L) (g := g) (t := t) hss
  have hr' : t.regs ta = some (b32 x.toNat) := by
    rw [hr]; simp only [b32, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact tcSt_ok hb hn hr' ha hs hv h4 f

set_option maxHeartbeats 16000000 in
/-- **No Tensor Memory store of the correction warps is undefined behaviour**: its address as
the loads', and its sixteen operands are the chunk's products, four-byte floats. -/
theorem st_safe (hp : Pre p L m) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (code p L g).AtD d t)
    (hc : kernel.code[(code p L g).pc d]? = some ins)
    (hf : Fires ((code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : ∃ st c, d.site = .rst st c) (f : Fault) : e.kind ≠ .ub f := by
  have hblk : L.block % 32 = 0 := by rw [hp.block]
  have hreg : ∀ r ∈ Flow.live (livePc d), t.regs r = some (valueOf p L g d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hq : g % L.block % 128 / 32 < 4 := by omega
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  intro hk
  have hu := fires_ub hf hk
  obtain ⟨st, c, rfl⟩ := hs
  fin_cases st <;> fin_cases c <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    refine tcSt_word_ok hblk (by decide) (hreg _ (by lit_mem)) ?_ ?_ ?_ f hu
    · first
        | (rw [tm0_toNat hp]; omega)
        | (rw [addi_tm0 hp (by decide) (by decide)]; omega)
        | (rw [tm1_toNat hp]; omega)
    · first
        | exact tm_ok hp (tm0_toNat hp) (by decide)
        | exact tm_ok hp (tm1_toNat hp) (by decide)
        | exact tm_ok hp (addi_tm0 hp (by decide) (by decide)) (by decide)
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i <;>
        exact ⟨_, _, rfl, hreg _ (by lit_mem), by
          simp [valueOf, values, rLoaded, rProducts, valuesRescale, valuesRound, valuesTile,
            lookupLit, fv, Value.bytes, FloatFmt.bytes]⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
