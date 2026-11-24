-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmGlobal
public import Kernels.InklingRelDecode.Proof.Thread.SmAll
public import Kernels.InklingRelDecode.Proof.Thread.EvSBias
public import Kernels.InklingRelDecode.Proof.Thread.SwShape
public import Lemmas.Flow.TmplOkMore
public import Lemmas.Flow.UbStop
public import Lemmas.Tcgen05.TcGroup

@[expose] public section

/-! # The softmax region's sites are not undefined behaviour

Every site. The synchronization sites, the bias loads (the pointer `%rd71` is 2-aligned:
`Ent.Ok.relAl`), the shared load of the row sum and the two arrivals and polls; the Tensor Memory
loads and stores from the allocated base's column field (`Ent.Ok.col`, `tmem_ok`); the shuffles
and the shared store of the rescale test (`stage_ok`) from the four-byte words of the stage
(`Inv.four`), the running maximum's `erealValue .f32` and the half sum's `.f32` value. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Tm
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- The shuffles and the shared store of the rescale test. -/
def Site.stage : Site → Bool
  | .shfl5 | .shfl6 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10
  | .shfl11 | .shfl12 => true
  | _ => false

/-- A full-mask shuffle with immediate lane and clamp of a register whose value has four bytes is
not undefined behaviour, in a launch of whole warps. -/
theorem shfl_four_ok {A : List Assumption} {mode : ShflMode} {dd r : Nat} {b c : Int}
    {v : Value} (hm : mode = .bfly ∨ mode = .idx) (hb : L.block % 32 = 0)
    (hr : t.regs r = some v) (hv : v.bytes = 4) (f : Fault) :
    eventTmpl A L g t (.warp { kind := .shfl mode, ty := some (.int .b 32),
                               dsts := [some dd], srcs := [.reg r, .imm b, .imm c],
                               mask := some (.imm (-1)) }) ≠ .ub f := by
  have hrule : WarpInstr.rule { kind := .shfl mode, ty := some (.int .b 32),
                                dsts := [some dd], srcs := [.reg r, .imm b, .imm c],
                                mask := some (.imm (-1)) } = some .threadShfl := by
    rcases hm with rfl | rfl <;> rfl
  simp only [eventTmpl, warpTmpl, hrule, shflTmpl, readValue, readReg, hr, readBits, pure,
    Except.pure]
  rw [show (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2 ^ 32 - 1 by decide]
  simp [hb, hv]

/-- **The shuffles and the shared store of the rescale test are not undefined behaviour**: the
shuffled words are the running maximum's `erealValue .f32`, the half sum's `.f32` value and the
stage's four-byte words (`Inv.four`); the store writes `cm4` at `sharedBase + 212992 + 4 w`. -/
theorem stage_ok (hpre : Pre Q L mem0) {d : D} {ins : Instr} (hi : Inv L g d)
    (hm : d.site.stage = true) (hsub : t.sub = 0) (hH : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hsa := hpre.sharedAlignment
  have hsr := hpre.sharedRange
  have h4 := hi.four
  cases hsd : d.site <;> rw [hsd] at hm hc <;> simp only [Site.stage] at hm <;>
    try exact absurd hm (by decide)
  case shfl5 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_5)
    exact shfl_four_ok (.inl rfl) hb (holds_reg hH (by rw [hsd]; live_dec) rfl)
      (by sm_vals; exact ownV_bytes _) f
  case shfl6 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_6)
    exact shfl_four_ok (.inl rfl) hb (holds_reg hH (by rw [hsd]; live_dec) rfl)
      (by sm_vals; exact hi.four.sw) f
  case shfl7 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_7)
    exact shfl_four_ok (.inl rfl) hb (holds_reg hH (by rw [hsd]; live_dec) rfl)
      (by rw [valueOf_r46]; exact readEReal_f32_bytes h4.al) f
  case shfl8 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_8)
    exact shfl_four_ok (.inl rfl) hb (holds_reg hH (by rw [hsd]; live_dec) rfl)
      (by rw [valueOf_cm1]; exact h4.cm1) f
  case shfl9 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_9)
    exact shfl_four_ok (.inl rfl) hb (holds_reg hH (by rw [hsd]; live_dec) rfl)
      (by rw [valueOf_cm2]; exact h4.cm2) f
  case shfl10 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_10)
    exact shfl_four_ok (.inl rfl) hb (holds_reg hH (by rw [hsd]; live_dec) rfl)
      (by rw [valueOf_cm3]; exact h4.cm3) f
  case shfl11 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_11)
    exact shfl_four_ok (.inl rfl) hb (holds_reg hH (by rw [hsd]; live_dec) rfl)
      (by rw [valueOf_ld]; exact h4.ld) f
  case shfl12 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_12)
    exact shfl_four_ok (.inl rfl) hb (holds_reg hH (by rw [hsd]; live_dec) rfl)
      (by rw [valueOf_r1082]; exact h4.m2) f
  case store10 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_10)
    have hw : g % L.block / 32 % 4 < 4 := Nat.mod_lt _ (by decide)
    have hr := holds_reg (r := 1533)
      (v := b32 ((L.sharedBase + 212992 + g % L.block / 32 % 4 * 4) % 2 ^ 32)) hH
      (by rw [hsd]; live_dec) (by sm_vals)
    have hv : t.regs 1534 = some d.stg.cm4 :=
      holds_reg hH (by rw [hsd]; live_dec) (valueOf_cm4 d)
    refine storeDirect_ok rfl rfl rfl rfl rfl (by decide) ?_ (by simp [hsub])
      ⟨_, readValue_reg hv, h4.cm4⟩ f
    unfold sharedBytes at hsr
    refine ⟨_, effAddr_b32_off (off := 0) hr (by omega), ?_⟩
    show ((L.sharedBase + 212992 + g % L.block / 32 % 4 * 4) % 2 ^ 32 + 0) % (32 / 8 * 1) = 0
    omega

/-- The address of a bias word is 2-aligned when the `Rel` pointer is. -/
theorem biasAddr_even (e : Ent) (T n j : Nat) (h : e.rel % 2 = 0) : biasAddr e T n j % 2 = 0 := by
  unfold biasAddr ptrAt p9 p262 p261 p260 p259
  omega

/-- The Tensor Memory loads and stores of the region: the S tile's load and the P tile's store at
`tileAddr`, the rescale's load and store of `O` at `oAddr`. -/
def Site.tmem : Site → Bool
  | .ldS | .ldO | .stO | .tmemSt => true
  | _ => false

/-- An address `w · 2 ^ 21 + c` of warp `w`'s lanes, with a column `c` that leaves room for the
half offset `o ≤ 64`, is a supported address of a `.16x32bx2` access. -/
theorem addr_ok {c n o : Nat} (ho : o ≤ 64) (hc : c + 64 < 2 ^ 16)
    (hn : n = g % L.block / 32 % 4) :
    tcDataAddressOk L g (.s16x32bx2 o) (n * 2097152 + c) = true := by
  refine tcDataAddressOk_of_lane_base ?_ ?_
  · simp only [TcShape.splitOk, decide_eq_true_eq]
    omega
  · unfold laneBase
    omega

/-- The address `b · 2 ^ 21 + c` with the recorded lane bits `b` (0 or the warp index, `Inv.bw`)
and a column `c` that leaves room for the half offset `o ≤ 64` is a supported address of a
`.16x32bx2` access: the lane field is 0 or the warp's lane base. -/
theorem addr_ok_bw (hi : Inv L g d) {c o : Nat} (ho : o ≤ 64) (hc : c + 64 < 2 ^ 16) :
    tcDataAddressOk L g (.s16x32bx2 o) (d.stg.bw * 2097152 + c) = true := by
  have hT := hi.tid
  rcases hi.bw with hb | hb
  · rw [hb]
    refine tcDataAddressOk_of_row_zero ?_ ?_
    · simp only [TcShape.splitOk, decide_eq_true_eq]
      omega
    · omega
  · rw [hb]
    exact addr_ok ho hc (by omega)

theorem tileAddr_lane (hi : Inv L g d) :
    tileAddr L g d = d.stg.bw * 2097152 + (d.i % 2 * 128 + d.e.tm) ∧
      d.i % 2 * 128 + d.e.tm + 64 < 2 ^ 16 := by
  have hc := hi.ok.col
  have hT := hi.tid
  have hb : d.stg.bw < 4 := by rcases hi.bw with h | h <;> omega
  unfold tileAddr r45
  omega

theorem oAddr_lane (hi : Inv L g d) :
    oAddr L g d = d.stg.bw * 2097152 + (d.e.tm + 256) ∧
      d.e.tm + 256 + 64 < 2 ^ 16 := by
  have hc := hi.ok.col
  have hT := hi.tid
  have hb : d.stg.bw < 4 := by rcases hi.bw with h | h <;> omega
  unfold oAddr
  omega

/-- **The region's Tensor Memory loads and stores are not undefined behaviour**: the address is
the warp's lanes and a column of the allocated base, which leaves room for the access
(`Ent.Ok.col`); the stored words have four bytes. -/
theorem tmem_ok (hpre : Pre Q L mem0) {d : D} {ins : Instr} (hi : Inv L g d)
    (hm : d.site.tmem = true) (hH : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨ht1, ht2⟩ := tileAddr_lane hi
  obtain ⟨ho1, ho2⟩ := oAddr_lane hi
  have hT := hi.tid
  cases hsd : d.site <;> rw [hsd] at hm hc <;> simp only [Site.tmem] at hm <;>
    try exact absurd hm (by decide)
  case ldS =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemLoad_0)
    have hr : t.regs 1676 = some (b32 (tileAddr L g d)) :=
      holds_reg hH (by rw [hsd]; live_dec) (by sm_vals; rfl)
    refine tcLd_ok hb (by decide) hr (Nat.mod_lt _ (by decide)) ?_ f
    rw [ht1]
    exact addr_ok_bw hi (by norm_num) ht2
  case tmemSt =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_0)
    have hr : t.regs 1676 = some (b32 (tileAddr L g d)) :=
      holds_reg hH (by rw [hsd]; live_dec) (by sm_vals; rfl)
    obtain ⟨vals, hv, h4⟩ := mapM_regs_ok (L := L) (g := g) (t := t) (ss := ((List.range 32).map
      fun w => Opnd.reg (1677 + w))) fun p hp => by
        simp only [List.length_map, List.length_range] at hp
        refine ⟨1677 + p, d.pwV p, by simp [hp], holds_reg hH ?_ (valueOf_pw d hp), pwV_bytes d p⟩
        rw [hsd]
        revert p
        decide +kernel
    refine tcSt_ok hb (by decide) hr (Nat.mod_lt _ (by decide)) ?_ hv h4 f
    rw [ht1]
    exact addr_ok_bw hi (by norm_num) ht2
  case ldO =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemLoad_1)
    have hr : t.regs 1611 = some (b32 (oAddr L g d)) :=
      holds_reg hH (by rw [hsd]; live_dec) (by sm_vals; rfl)
    refine tcLd_ok hb (by decide) hr (Nat.mod_lt _ (by decide)) ?_ f
    rw [ho1]
    exact addr_ok_bw hi (by norm_num) ho2
  case stO =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_1)
    have hr : t.regs 1611 = some (b32 (oAddr L g d)) :=
      holds_reg hH (by rw [hsd]; live_dec) (by sm_vals; rfl)
    obtain ⟨vals, hv, h4⟩ := mapM_regs_ok (L := L) (g := g) (t := t) (ss := ((List.range 64).map
      fun k => Opnd.reg (1612 + k))) fun p hp => by
        simp only [List.length_map, List.length_range] at hp
        refine ⟨1612 + p, _, by simp [hp], holds_reg hH ?_ (valueOf_prod d hp),
          prodO_bytes _ _⟩
        rw [hsd]
        revert p
        decide +kernel
    refine tcSt_ok hb (by decide) hr (Nat.mod_lt _ (by decide)) ?_ hv h4 f
    rw [ho1]
    exact addr_ok_bw hi (by norm_num) ho2

/-- **The softmax region's sites have no undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre Q L mem0) {d : D} {ins : Instr} (hi : Inv L g d)
    (hsub : t.sub = 0)
    (hH : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hsa := hpre.sharedAlignment
  have hsr := hpre.sharedRange
  by_cases hm : d.site.tmem = true
  · exact tmem_ok hpre hi hm hH hc f
  by_cases hs : d.site.stage = true
  · exact stage_ok hpre hi hs hsub hH hc f
  cases hsd : d.site <;> rw [hsd] at hs hc hm <;> simp only [Site.stage, Site.tmem,
    not_true_eq_false] at hs hm
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_1)
    exact plainOk_tmpl hb (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_19)
    exact barSync_imm_ok (id := 1) (by decide) f
  · rename_i j
    obtain ⟨gd, hcode⟩ := isGload_spec (gload_pre j.val j.isLt)
    have hc' : kernel.code[680 + 2 * j.val]? = some ins := hc
    obtain rfl := Option.some.inj (hc'.symm.trans hcode)
    have hr : t.regs (gloadBase (680 + 2 * j.val)) =
        some (b64 (biasAddr d.e (g % L.block) d.n j.val)) := by
      rw [gbase_pre j.val j.isLt]
      exact holds_reg hH (by rw [hsd]; exact glive_pre j.val j.isLt) (valueOf_ptrCur d j.isLt)
    exact gload_ok hr (Nat.mod_lt _ (by decide)) (Or.inl rfl)
      (biasAddr_even _ _ _ _ hi.ok.relAl) f
  · rename_i j
    obtain ⟨gd, hcode⟩ := isGload_spec (gload_nxt j.val j.isLt)
    have hc' : kernel.code[1124 + 2 * j.val]? = some ins := hc
    obtain rfl := Option.some.inj (hc'.symm.trans hcode)
    have hr : t.regs (gloadBase (1124 + 2 * j.val)) =
        some (b64 (biasAddr d.e (g % L.block) (d.n + d.e.splits) j.val)) := by
      rw [gbase_nxt j.val j.isLt]
      exact holds_reg hH (by rw [hsd]; exact glive_nxt j.val j.isLt) (valueOf_ptrNxt d j.isLt)
    exact gload_ok hr (Nat.mod_lt _ (by decide)) (Or.inl rfl)
      (biasAddr_even _ _ _ _ hi.ok.relAl) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_0)
    have hr := holds_reg (r := 874) (v := b32 ((L.sharedBase + d.i % 2 * 8 + 213280) % 2 ^ 32))
      hH (by rw [hsd]; live_dec) (by sm_vals)
    have hp := holds_reg (r := 875) (v := b32 (d.i / 2 % 2)) hH (by rw [hsd]; live_dec)
      (by sm_vals)
    refine mbarWait_bits_ok hr ?_ ⟨_, readBits_bits hp⟩ f
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_4)
    exact shfl_imm_ok (p := none) (x := BitVec.ofNat 64 (g % L.block / 32)) (.inr rfl) hb
      (holds_reg (v := b32 (g % L.block / 32)) hH (by rw [hsd]; live_dec) (by sm_vals)) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_1)
    exact plainOk_tmpl hb rfl f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_22)
    exact (bar_ok (id := 0) (n := 128) (by decide) (by decide) (by decide) (by decide) f).1
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_23)
    exact (bar_ok (id := 0) (n := 128) (by decide) (by decide) (by decide) (by decide) f).1
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_202)
    have hr := holds_reg (r := 500) (v := b32 ((L.sharedBase + g % L.block % 4 * 4) % 2 ^ 32))
      hH (by rw [hsd]; live_dec) (by sm_vals)
    refine loadDirect_ok rfl rfl rfl rfl rfl rfl (by decide) ?_ f
    exact ⟨_, effAddr_b32_off (off := 212992) hr (by omega),
      by simp [DType.width, MemAccess.regs]; omega⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_1)
    have hr := holds_reg (r := 623) (v := b32 ((L.sharedBase + 213312) % 2 ^ 32)) hH
      (by rw [hsd]; live_dec) (by sm_vals)
    have hp := holds_reg (r := 1532) (v := b32 ((d.i + 1) % 2)) hH (by rw [hsd]; live_dec)
      (by sm_vals)
    refine mbarWait_bits_ok hr ?_ ⟨_, readBits_bits hp⟩ f
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_2)
    exact plainOk_tmpl hb rfl f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_24)
    exact (bar_ok (id := 0) (n := 128) (by decide) (by decide) (by decide) (by decide) f).1
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_3)
    exact plainOk_tmpl hb rfl f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_20)
    exact (bar_ok (id := 0) (n := 128) (by decide) (by decide) (by decide) (by decide) f).1
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_0)
    exact plainOk_tmpl hb rfl f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_21)
    exact (bar_ok (id := 0) (n := 128) (by decide) (by decide) (by decide) (by decide) f).1
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_3)
    have hr := holds_reg (r := 1709)
      (v := b32 ((L.sharedBase + d.i % 2 * 8 + 213296) % 2 ^ 32)) hH (by rw [hsd]; live_dec)
      (by sm_vals)
    refine mbarArrive_imm_ok hr ?_ f
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
