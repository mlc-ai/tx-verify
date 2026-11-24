-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmLoader
public import Kernels.InklingRelDecode.Proof.Thread.MmaIssue
public import Kernels.InklingRelDecode.Proof.Launch

@[expose] public section

/-! # The MMA warp's sites are not undefined behaviour -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Tm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}


/-- A register of the table with value `v` holds `v`. -/
theorem reg_val {d : D} {r : Nat} {v : Value} (hH : Holds t.regs (facts L d))
    (hl : r ∈ Flow.live d.site.pc) (hv : valueOf L d r = v) : t.regs r = some v :=
  holds_mem hH (hv ▸ Flow.mem_factsFrom hl)

theorem reg_b32 {d : D} {r n : Nat} (hH : Holds t.regs (facts L d))
    (hl : r ∈ Flow.live d.site.pc) (hv : valueOf L d r = b32 n) : t.regs r = some (b32 n) :=
  reg_val hH hl hv

/-- A QK MMA at a state whose registers hold the table's descriptors is not undefined behaviour
(`qk_isMma`). -/
theorem qk_ok (hone : OneCta L g) (hg : g < L.threads) {d : D} (hi : Inv d)
    (hH : Holds t.regs (facts L d)) (hsa : L.sharedBase % 1024 = 0)
    (hsr : L.sharedBase + sharedBytes ≤ 2 ^ 18) {ra rb en oa ob : Nat}
    (hla : ra ∈ Flow.live d.site.pc) (hlb : rb ∈ Flow.live d.site.pc)
    (hle : en ∈ Flow.live d.site.pc) (hld : 547 ∈ Flow.live d.site.pc)
    (hli : 548 ∈ Flow.live d.site.pc) (hva : valueOf L d ra = desc (qLo L + oa))
    (hvb : valueOf L d rb = desc (kLo L (d.i % 3) + ob))
    (hvd : valueOf L d 547 = b32 (d.tm + 128 * (d.i % 2))) (hvi : valueOf L d 548 = b32 qkIdesc)
    (hoa : oa ≤ 518) (hob : ob ≤ 1030) (hen : ∃ b, valueOf L d en = .pred b)
    (f : Fault) :
    eventTmpl asms L g t (.tcMma (.dense .one false .f16 547 (.smem (.reg ra)) (.reg rb)
      (.reg 548) masks0 (.reg en))) ≠ .ub f := by
  have hsr' : L.sharedBase ≤ 2 ^ 18 := by omega
  have hq : qLo L + oa < 2 ^ 15 := by unfold qLo; omega
  have hk : kLo L (d.i % 3) + ob < 2 ^ 15 := by unfold kLo; omega
  obtain ⟨b, hb⟩ := hen
  have hrd := reg_val hH hld hvd
  have hra := reg_val hH hla hva
  have hrb := reg_val hH hlb hvb
  have hri := reg_val hH hli hvi
  have hre := reg_val hH hle hb
  refine not_ub_of_fires (pc := 0) (fun f hf => ?_) f
  have := qk_isMma hone hg hrd (by have := hi.tm; omega) hra (by omega) (by omega) hrb (by omega)
    (by omega) hri ⟨b, by simp [mmaEnable, readReg, hre, bind, Except.bind, pure, Except.pure]⟩ hf
  simp [isMma] at this

/-- The A operand of a PV MMA, `[%r565 + aoff]` with `%r565 = tm + 128 x` (`x ≤ 1`) and
`aoff ≤ 56`, stays in the column field when the base's does (`Inv.col`). -/
theorem pv_offset {tm x : Nat} {aoff : Int} (hcol : tm + 512 ≤ 2 ^ 16) (hx : x ≤ 1)
    (h0 : 0 ≤ aoff) (h1 : aoff ≤ 56) : ∃ a', tmemOffset (tm + 128 * x) aoff = .ok a' := by
  have e : ((tm + 128 * x : Nat) : Int) % 2 ^ 16 = ((tm + 128 * x : Nat) : Int) :=
    Int.emod_eq_of_lt (by omega) (by omega)
  have h : 0 ≤ ((tm + 128 * x : Nat) : Int) % 2 ^ 16 + aoff ∧
      ((tm + 128 * x : Nat) : Int) % 2 ^ 16 + aoff < 2 ^ 16 := by
    rw [e]; omega
  unfold tmemOffset
  simp only [h, and_self, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- A PV MMA at a state whose registers hold the table's columns and descriptors is not
undefined behaviour (`pv_isMma`). -/
theorem pv_ok (hone : OneCta L g) (hg : g < L.threads) {d : D} (hi : Inv d)
    (hH : Holds t.regs (facts L d)) (hsa : L.sharedBase % 1024 = 0)
    (hsr : L.sharedBase + sharedBytes ≤ 2 ^ 18) {rb en ob : Nat} {aoff : Int}
    (hld : 564 ∈ Flow.live d.site.pc) (hla : 565 ∈ Flow.live d.site.pc)
    (hlb : rb ∈ Flow.live d.site.pc) (hli : 566 ∈ Flow.live d.site.pc)
    (hle : en ∈ Flow.live d.site.pc)
    (hvd : valueOf L d 564 = b32 (d.tm + 256))
    (hva : valueOf L d 565 = b32 (d.tm + 128 * ((d.i - 1) % 2)))
    (hvb : valueOf L d rb = vdesc (vLo L ((d.i - 1) % 3) + ob))
    (hvi : valueOf L d 566 = b32 pvIdesc) (h0 : 0 ≤ aoff) (h1 : aoff ≤ 56) (hob : ob ≤ 896)
    (hen : ∃ b, valueOf L d en = .pred b) (f : Fault) :
    eventTmpl asms L g t (.tcMma (.dense .one false .f16 564 (.tmem 565 aoff) (.reg rb)
      (.reg 566) masks0 (.reg en))) ≠ .ub f := by
  have hsr' : L.sharedBase ≤ 2 ^ 18 := by omega
  have hcol := hi.col
  have hx : (d.i - 1) % 2 ≤ 1 := by omega
  obtain ⟨b, hb⟩ := hen
  have hrd := reg_val hH hld hvd
  have hra := reg_val hH hla hva
  have hrb := reg_val hH hlb hvb
  have hri := reg_val hH hli hvi
  have hre := reg_val hH hle hb
  refine not_ub_of_fires (pc := 0) (fun f hf => ?_) f
  have := pv_isMma hone hg hrd (by omega) hra (by omega) (pv_offset hcol hx h0 h1) hrb
    (by unfold vLo; omega) hri
    ⟨b, by simp [mmaEnable, readReg, hre, bind, Except.bind, pure, Except.pure]⟩ hf
  simp [isMma] at this

/-- **The MMA warp's sites have no undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre Q L mem0) (hg : g < L.threads) {d : D} {ins : Instr} (hi : Inv d)
    {w : Nat} (hw : d.pro 464 = b32 w) (hH : Holds t.regs (facts L d))
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hsa := hpre.sharedAlignment
  have hsr := hpre.sharedRange
  have hv := hpre.launchValid.1
  have hu := clusterPlaces_unit hpre
  have hnc := hpre.nclusters
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_7)
    exact plainOk_tmpl hb (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_207)
    refine loadAccess_ok rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) ?_ f
    exact ⟨_, accessLoc_sharedSym (off := 212996) rfl rfl rfl (by omega),
      by simp [DType.width]; omega⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_30)
    exact barSync_imm_ok (id := 1) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_5)
    exact warpBar_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_3)
    have hr := reg_b32 (r := 474) (n := L.sharedBase + 213216 + 8 * (i % 3)) hH (by live_dec)
      (by simp [valueOf, values, lookupLit])
    have hp := reg_b32 (r := 545) (n := i / 3 % 2) hH (by live_dec)
      (by simp [valueOf, values, lookupLit])
    refine mbarWait_bits_ok hr ?_ ⟨_, readBits_bits hp⟩ f
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_13)
    exact shfl_imm_ok (p := none) (x := BitVec.ofNat 64 w) (.inr rfl) hb
      (reg_b32 (r := 464) (n := w) hH (by live_dec)
        (by simpa [valueOf, values, lookupLit] using hw))
      f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_6)
    exact warpBar_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_28)
    exact elect_imm_ok f
  · rename_i j
    have hone := oneCta hpre hg
    fin_cases j
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_0)
      exact qk_ok hone hg hi hH hsa hsr (oa := 0) (ob := 0) (by live_dec) (by live_dec)
        (by live_dec) (by live_dec) (by live_dec) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by omega) (by omega)
        ⟨false, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_1)
      exact qk_ok hone hg hi hH hsa hsr (oa := 2) (ob := 2) (by live_dec) (by live_dec)
        (by live_dec) (by live_dec) (by live_dec) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by omega) (by omega)
        ⟨true, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_2)
      exact qk_ok hone hg hi hH hsa hsr (oa := 4) (ob := 4) (by live_dec) (by live_dec)
        (by live_dec) (by live_dec) (by live_dec) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by omega) (by omega)
        ⟨true, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_3)
      exact qk_ok hone hg hi hH hsa hsr (oa := 6) (ob := 6) (by live_dec) (by live_dec)
        (by live_dec) (by live_dec) (by live_dec) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by omega) (by omega)
        ⟨true, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_4)
      exact qk_ok hone hg hi hH hsa hsr (oa := 512) (ob := 1024) (by live_dec) (by live_dec)
        (by live_dec) (by live_dec) (by live_dec) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by omega) (by omega)
        ⟨true, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_5)
      exact qk_ok hone hg hi hH hsa hsr (oa := 514) (ob := 1026) (by live_dec) (by live_dec)
        (by live_dec) (by live_dec) (by live_dec) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by omega) (by omega)
        ⟨true, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_6)
      exact qk_ok hone hg hi hH hsa hsr (oa := 516) (ob := 1028) (by live_dec) (by live_dec)
        (by live_dec) (by live_dec) (by live_dec) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by omega) (by omega)
        ⟨true, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_7)
      exact qk_ok hone hg hi hH hsa hsr (oa := 518) (ob := 1030) (by live_dec) (by live_dec)
        (by live_dec) (by live_dec) (by live_dec) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by omega) (by omega)
        ⟨true, by simp [valueOf, values, lookupLit]⟩ f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_0)
    have hr := reg_b32 (r := 549) (n := L.sharedBase + 213280 + 8 * (i % 2)) hH (by live_dec)
      (by simp [valueOf, values, lookupLit])
    refine tcCommit_ok hr ?_ hv hg hu hnc f
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_6)
    exact warpBar_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_7)
    exact warpBar_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_4)
    have hr := reg_b32 (r := 557) (n := L.sharedBase + 213296 + 8 * ((i - 1) % 2)) hH
      (by live_dec) (by simp [valueOf, values, lookupLit])
    have hp := reg_b32 (r := 558) (n := (i - 1) / 2 % 2) hH (by live_dec)
      (by simp [valueOf, values, lookupLit])
    refine mbarWait_bits_ok hr ?_ ⟨_, readBits_bits hp⟩ f
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_14)
    exact shfl_imm_ok (p := none) (x := BitVec.ofNat 64 w) (.inr rfl) hb
      (reg_b32 (r := 464) (n := w) hH (by live_dec)
        (by simpa [valueOf, values, lookupLit] using hw))
      f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_8)
    exact warpBar_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_29)
    exact elect_imm_ok f
  · rename_i j
    have hone := oneCta hpre hg
    fin_cases j
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_8)
      exact pv_ok hone hg hi hH hsa hsr (rb := 2044) (en := 14) (ob := 0) (aoff := 0)
        (by live_dec) (by live_dec) (by live_dec) (by live_dec) (by live_dec)
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by norm_num) (by norm_num) (by norm_num)
        ⟨decide (i ≠ 1), by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_9)
      exact pv_ok hone hg hi hH hsa hsr (rb := 2045) (en := 16) (ob := 128) (aoff := 8)
        (by live_dec) (by live_dec) (by live_dec) (by live_dec) (by live_dec)
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by norm_num) (by norm_num) (by norm_num) ⟨true, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_10)
      exact pv_ok hone hg hi hH hsa hsr (rb := 2046) (en := 16) (ob := 256) (aoff := 16)
        (by live_dec) (by live_dec) (by live_dec) (by live_dec) (by live_dec)
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by norm_num) (by norm_num) (by norm_num) ⟨true, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_11)
      exact pv_ok hone hg hi hH hsa hsr (rb := 2047) (en := 16) (ob := 384) (aoff := 24)
        (by live_dec) (by live_dec) (by live_dec) (by live_dec) (by live_dec)
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by norm_num) (by norm_num) (by norm_num) ⟨true, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_12)
      exact pv_ok hone hg hi hH hsa hsr (rb := 2048) (en := 16) (ob := 512) (aoff := 32)
        (by live_dec) (by live_dec) (by live_dec) (by live_dec) (by live_dec)
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by norm_num) (by norm_num) (by norm_num) ⟨true, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_13)
      exact pv_ok hone hg hi hH hsa hsr (rb := 2049) (en := 16) (ob := 640) (aoff := 40)
        (by live_dec) (by live_dec) (by live_dec) (by live_dec) (by live_dec)
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by norm_num) (by norm_num) (by norm_num) ⟨true, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_14)
      exact pv_ok hone hg hi hH hsa hsr (rb := 2050) (en := 16) (ob := 768) (aoff := 48)
        (by live_dec) (by live_dec) (by live_dec) (by live_dec) (by live_dec)
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by norm_num) (by norm_num) (by norm_num) ⟨true, by simp [valueOf, values, lookupLit]⟩ f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_15)
      exact pv_ok hone hg hi hH hsa hsr (rb := 2051) (en := 16) (ob := 896) (aoff := 56)
        (by live_dec) (by live_dec) (by live_dec) (by live_dec) (by live_dec)
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by simp [valueOf, values, lookupLit]) (by simp [valueOf, values, lookupLit])
        (by norm_num) (by norm_num) (by norm_num) ⟨true, by simp [valueOf, values, lookupLit]⟩ f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_1)
    have hr := reg_b32 (r := 567) (n := L.sharedBase + 213248 + 8 * ((i - 1) % 3)) hH
      (by live_dec) (by simp [valueOf, values, lookupLit])
    refine tcCommit_ok hr ?_ hv hg hu hnc f
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_2)
    have hr := reg_b32 (r := 568) (n := L.sharedBase + 213312) hH (by live_dec)
      (by simp [valueOf, values, lookupLit])
    refine tcCommit_ok hr ?_ hv hg hu hnc f
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_8)
    exact warpBar_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_9)
    exact warpBar_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_30)
    exact elect_imm_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_3)
    have hr := reg_b32 (r := 572) (n := L.sharedBase + 213328) hH (by live_dec)
      (by simp [valueOf, values, lookupLit])
    refine tcCommit_ok hr ?_ hv hg hu hnc f
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_31)
    exact barSync_imm_ok (id := 1) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_8)
    exact plainOk_tmpl hb (by decide) f

end
end PTX.Kernels.InklingRelDecode.Proof.Mma
