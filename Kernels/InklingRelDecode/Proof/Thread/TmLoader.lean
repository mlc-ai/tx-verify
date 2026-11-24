-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmIdle
public import Kernels.InklingRelDecode.Proof.Thread.TmGlobal
public import Kernels.InklingRelDecode.Proof.Thread.LoaderRing
public import Kernels.InklingRelDecode.Proof.Thread.LoaderSound
public import Kernels.InklingRelDecode.Proof.Thread.TmCopy

@[expose] public section

/-! # The loader's sites are not undefined behaviour

Every site. The two block-table loads read at the block-table base, which is 4-aligned
(`Worker.Pins.bt`), plus multiples of 4. The eight tensor copies (`cp_ok`, from `kvCopy_ok`):
`%rd1` is `param_1` (`Worker.Pins.rd1`); the destination is `sharedBase + 32768 (i % 3) + c` with
`c` a multiple of 8192, the barrier `sharedBase + 213216 + 8 (i % 3)` for a counter below `2 ^ 31`;
for every 32-bit counter the code's slot offsets are multiples of 32768 and 8 (`kOff_cases`,
`bOff_cases`), which is all the alignment needs; the box column is `head_cols · kvh` plus a multiple
of 64, a multiple of 8 (`Worker.Pins.w70`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Tm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- The tensor copies. -/
def Site.cp : Site → Bool
  | .cp0a | .cp0b | .cp1a | .cp1b | .cp2a | .cp2b | .cp3a | .cp3b => true
  | _ => false

/-- **A loader copy is not undefined behaviour**: the copy of the tile at offset `c` of the slot,
with box column `col` and any row. -/
theorem cp_ok (hpre : Pre Q L mem0) (hg : g < L.threads) {i c col row dst rc rr : Nat}
    (hc8 : c % 8192 = 0) (hcol : col % 8 = 0)
    (hmap : t.regs 1949 = some (.ptr 64 true (.param (param "1")) 0))
    (hd : t.regs dst = some (b32 ((L.sharedBase + kOff i + c) % 2 ^ 32)))
    (hb : t.regs 580 = some (b32 ((L.sharedBase + bOff i + 213216) % 2 ^ 32)))
    (hcr : t.regs rc = some (b32 (col % 2 ^ 32))) (hr : t.regs rr = some (b32 (row % 2 ^ 32)))
    (f : Fault) :
    eventTmpl asms L g t (.cpTensor false false dst 0 (.reg 1949) [.reg rc, .reg rr] 580 0 none
      .tile none) ≠ .ub f := by
  have hsa := hpre.sharedAlignment
  have hsr := hpre.sharedRange
  unfold sharedBytes at hsr
  have hk := kOff_cases i
  have hbo := bOff_cases i
  have hcta : g / L.block < L.grid := by
    rw [Launch.threads] at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  exact kvCopy_ok hpre hcta hmap hd hb hcr hr (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (by omega) (by omega) (by omega) f

/-- A barrier register of the iteration is 8-aligned, for every counter. -/
theorem bar_al {L : Launch} (hsa : L.sharedBase % 1024 = 0) (i c : Nat) (hc : c % 8 = 0) :
    (L.sharedBase + bOff i + c) % 2 ^ 32 % 8 = 0 := by
  have hbo := bOff_cases i
  omega

/-- The address of an 8-aligned barrier register, read with offset 0, is 8-aligned. -/
theorem wrap_al (N : Nat) (h : N < 2 ^ 32) (h8 : N % 8 = 0) :
    wrapAddr 32 (truncBits 32 (BitVec.ofNat 64 N)) (0 : Int) % 8 = 0 := by
  rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
  omega

/-- `mad.wide.s32 a, 4, c` is a multiple of 4 when `c` is. -/
theorem madWide4_al (a c : BitVec 64) (hc : c.toNat % 4 = 0) :
    (madWideW a (BitVec.ofInt 64 4) c).toNat % 4 = 0 := by
  unfold madWideW intBits intOf truncBits
  have h4 : toSigned 32 (rdW (BitVec.ofInt 64 4)) = 4 := by decide
  have hc' : (toSigned 64 (BitVec.ofNat 64 (c.toNat % 2 ^ 64))) % 4 = 0 := by
    unfold toSigned
    have := c.isLt
    simp only [BitVec.toNat_ofNat]
    split <;> omega
  simp only [↓reduceIte, h4, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  generalize toSigned 32 (rdW a) = x at *
  generalize toSigned 64 (BitVec.ofNat 64 (c.toNat % 2 ^ 64)) = y at *
  omega

/-- `add.s64 a, 4` is a multiple of 4 when `a` is. -/
theorem add64_4_al (a : BitVec 64) (ha : a.toNat % 4 = 0) :
    (add64W a (BitVec.ofInt 64 4)).toNat % 4 = 0 := by
  unfold add64W truncBits
  have h4 : (BitVec.ofInt 64 4).toNat = 4 := by decide
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, h4]
  have := a.isLt
  omega

/-- A global load through a 64-bit register whose bits are a multiple of 4. -/
theorem gload_al4 {base dst : Nat} {x : BitVec 64} (hr : t.regs base = some (.bits 64 x))
    (hal : x.toNat % 4 = 0) (f : Fault) :
    eventTmpl asms L g t (.mem (EvD.gload base dst 32)) ≠ .ub f := by
  have hr' : t.regs base = some (b64 x.toNat) := by simpa [b64] using hr
  exact gload_ok hr' x.isLt (.inr rfl) hal f

/-- The tensor copies of the loader have no undefined-behaviour template. -/
theorem tmpl_ok_cp (hpre : Pre Q L mem0) (hg : g < L.threads) {d : D} {ins : Instr}
    (hcp : d.site.cp = true) (hbt : natOf64 (d.pro 2020) % 4 = 0)
    (hw70 : natOf (d.pro 531) % 8 = 0)
    (hrd1 : d.pro 1949 = .ptr 64 true (.param (param "1")) 0)
    (hH : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hsa := hpre.sharedAlignment
  have hsr := hpre.sharedRange
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  have hmap : ∀ s', 1949 ∈ Flow.live s'.pc →
      Holds t.regs (facts L g ⟨s', pro, i, n, p0, p1, ln⟩) →
      t.regs 1949 = some (.ptr 64 true (.param (param "1")) 0) := fun s' hl hH' =>
    holds_mem hH' (tbl_mem hl (by simp [valueOf, table, PTX.Flow.lookupLit]; exact hrd1))
  have hbar : ∀ s', Holds t.regs (facts L g ⟨s', pro, i, n, p0, p1, ln⟩) →
      580 ∈ Flow.live s'.pc →
      t.regs 580 = some (b32 ((L.sharedBase + bOff i + 213216) % 2 ^ 32)) := by
    intro s' hH' hlv
    have := holds_mem hH' (tbl_mem (L := L) (g := g) (r := 580)
      (v := .bits 32 (addW (barW L i) (BitVec.ofInt 64 213216))) hlv
      (by simp [valueOf, table, PTX.Flow.lookupLit]))
    have hw := barc_word L i 213216
    simp only [Nat.cast_ofNat] at hw
    rwa [hw] at this
  have hm8 : natOf (pro 531) * ctaY L g % 8 = 0 := by
    rw [Nat.mul_mod, hw70, Nat.zero_mul, Nat.zero_mod]
  cases s
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_12)
    refine cp_ok hpre hg (i := i) (c := 0) (col := natOf (pro 531) * ctaY L g)
      (row := p0 * natOf (pro 529) + natOf (pro 530) * ctaY L g) (by decide)
      (by omega) (hmap _ (by live_dec) hH) ?_ (hbar .cp0a hH (by live_dec))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit])))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit]))) f
    · have := holds_mem hH (tbl_mem (L := L) (g := g) (r := 582) (v := .bits 32 (kvW L i))
        (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit]))
      rw [Nat.add_zero]
      rwa [kv_word L i] at this
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_13)
    refine cp_ok hpre hg (i := i) (c := 16384) (col := natOf (pro 531) * ctaY L g + 64)
      (row := p0 * natOf (pro 529) + natOf (pro 530) * ctaY L g) (by decide)
      (by omega) (hmap _ (by live_dec) hH) ?_ (hbar .cp0b hH (by live_dec))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit])))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit]))) f
    · have := holds_mem hH (tbl_mem (L := L) (g := g) (r := 585)
        (v := .bits 32 (addW (kvW L i) (BitVec.ofInt 64 16384))) (by live_dec)
        (by simp [valueOf, table, PTX.Flow.lookupLit]))
      have hw := kvc_word L i 16384
      simp only [Nat.cast_ofNat] at hw
      rwa [hw] at this
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_14)
    refine cp_ok hpre hg (i := i) (c := 98304) (col := natOf (pro 531) * ctaY L g + 128)
      (row := p0 * natOf (pro 529) + natOf (pro 530) * ctaY L g) (by decide)
      (by omega) (hmap _ (by live_dec) hH) ?_ (hbar .cp1a hH (by live_dec))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit])))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit]))) f
    · have := holds_mem hH (tbl_mem (L := L) (g := g) (r := 587)
        (v := .bits 32 (addW (kvW L i) (BitVec.ofInt 64 98304))) (by live_dec)
        (by simp [valueOf, table, PTX.Flow.lookupLit]))
      have hw := kvc_word L i 98304
      simp only [Nat.cast_ofNat] at hw
      rwa [hw] at this
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_15)
    refine cp_ok hpre hg (i := i) (c := 114688) (col := natOf (pro 531) * ctaY L g + 192)
      (row := p0 * natOf (pro 529) + natOf (pro 530) * ctaY L g) (by decide)
      (by omega) (hmap _ (by live_dec) hH) ?_ (hbar .cp1b hH (by live_dec))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit])))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit]))) f
    · have := holds_mem hH (tbl_mem (L := L) (g := g) (r := 589)
        (v := .bits 32 (addW (kvW L i) (BitVec.ofInt 64 114688))) (by live_dec)
        (by simp [valueOf, table, PTX.Flow.lookupLit]))
      have hw := kvc_word L i 114688
      simp only [Nat.cast_ofNat] at hw
      rwa [hw] at this
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_16)
    refine cp_ok hpre hg (i := i) (c := 8192) (col := natOf (pro 531) * ctaY L g)
      (row := p1 * natOf (pro 529) + natOf (pro 530) * ctaY L g) (by decide)
      (by omega) (hmap _ (by live_dec) hH) ?_ (hbar .cp2a hH (by live_dec))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit])))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit]))) f
    · have := holds_mem hH (tbl_mem (L := L) (g := g) (r := 592)
        (v := .bits 32 (addW (kvW L i) (BitVec.ofInt 64 8192))) (by live_dec)
        (by simp [valueOf, table, PTX.Flow.lookupLit]))
      have hw := kvc_word L i 8192
      simp only [Nat.cast_ofNat] at hw
      rwa [hw] at this
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_17)
    refine cp_ok hpre hg (i := i) (c := 24576) (col := natOf (pro 531) * ctaY L g + 64)
      (row := p1 * natOf (pro 529) + natOf (pro 530) * ctaY L g) (by decide)
      (by omega) (hmap _ (by live_dec) hH) ?_ (hbar .cp2b hH (by live_dec))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit])))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit]))) f
    · have := holds_mem hH (tbl_mem (L := L) (g := g) (r := 594)
        (v := .bits 32 (addW (kvW L i) (BitVec.ofInt 64 24576))) (by live_dec)
        (by simp [valueOf, table, PTX.Flow.lookupLit]))
      have hw := kvc_word L i 24576
      simp only [Nat.cast_ofNat] at hw
      rwa [hw] at this
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_18)
    refine cp_ok hpre hg (i := i) (c := 106496) (col := natOf (pro 531) * ctaY L g + 128)
      (row := p1 * natOf (pro 529) + natOf (pro 530) * ctaY L g) (by decide)
      (by omega) (hmap _ (by live_dec) hH) ?_ (hbar .cp3a hH (by live_dec))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit])))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit]))) f
    · have := holds_mem hH (tbl_mem (L := L) (g := g) (r := 595)
        (v := .bits 32 (addW (kvW L i) (BitVec.ofInt 64 106496))) (by live_dec)
        (by simp [valueOf, table, PTX.Flow.lookupLit]))
      have hw := kvc_word L i 106496
      simp only [Nat.cast_ofNat] at hw
      rwa [hw] at this
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_19)
    refine cp_ok hpre hg (i := i) (c := 122880) (col := natOf (pro 531) * ctaY L g + 192)
      (row := p1 * natOf (pro 529) + natOf (pro 530) * ctaY L g) (by decide)
      (by omega) (hmap _ (by live_dec) hH) ?_ (hbar .cp3b hH (by live_dec))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit])))
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit]))) f
    · have := holds_mem hH (tbl_mem (L := L) (g := g) (r := 596)
        (v := .bits 32 (addW (kvW L i) (BitVec.ofInt 64 122880))) (by live_dec)
        (by simp [valueOf, table, PTX.Flow.lookupLit]))
      have hw := kvc_word L i 122880
      simp only [Nat.cast_ofNat] at hw
      rwa [hw] at this
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp

/-- The loader's sites other than the tensor copies have no undefined-behaviour template. -/
theorem tmpl_ok_rest (hpre : Pre Q L mem0) (_hg : g < L.threads) {d : D} {ins : Instr}
    (hcp : d.site.cp = false) (hbt : natOf64 (d.pro 2020) % 4 = 0)
    (hw70 : natOf (d.pro 531) % 8 = 0)
    (hrd1 : d.pro 1949 = .ptr 64 true (.param (param "1")) 0)
    (hH : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hsa := hpre.sharedAlignment
  have hsr := hpre.sharedRange
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  have hmap : ∀ s', 1949 ∈ Flow.live s'.pc →
      Holds t.regs (facts L g ⟨s', pro, i, n, p0, p1, ln⟩) →
      t.regs 1949 = some (.ptr 64 true (.param (param "1")) 0) := fun s' hl hH' =>
    holds_mem hH' (tbl_mem hl (by simp [valueOf, table, PTX.Flow.lookupLit]; exact hrd1))
  have hbar : ∀ s', Holds t.regs (facts L g ⟨s', pro, i, n, p0, p1, ln⟩) →
      580 ∈ Flow.live s'.pc →
      t.regs 580 = some (b32 ((L.sharedBase + bOff i + 213216) % 2 ^ 32)) := by
    intro s' hH' hlv
    have := holds_mem hH' (tbl_mem (L := L) (g := g) (r := 580)
      (v := .bits 32 (addW (barW L i) (BitVec.ofInt 64 213216))) hlv
      (by simp [valueOf, table, PTX.Flow.lookupLit]))
    have hw := barc_word L i 213216
    simp only [Nat.cast_ofNat] at hw
    rwa [hw] at this
  have hm8 : natOf (pro 531) * ctaY L g % 8 = 0 := by
    rw [Nat.mul_mod, hw70, Nat.zero_mul, Nat.zero_mod]
  cases s
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_5)
    exact plainOk_tmpl hb (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_204)
    refine loadAccess_ok rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) ?_ f
    exact ⟨_, accessLoc_sharedSym (off := 212992) rfl rfl rfl (by omega),
      by simp [DType.width]; omega⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_204)
    refine loadAccess_ok rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) ?_ f
    exact ⟨_, accessLoc_sharedSym (off := 212992) rfl rfl rfl (by omega),
      by simp [DType.width]; omega⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_28)
    exact barSync_imm_ok (id := 1) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_2)
    have hr : t.regs 578 =
        some (.bits 32 (BitVec.ofNat 64 ((L.sharedBase + bOff i + 213248) % 2 ^ 32))) := by
      have := holds_mem hH (tbl_mem (L := L) (g := g) (r := 578)
        (v := .bits 32 (addW (barW L i) (BitVec.ofInt 64 213248))) (by live_dec)
        (by simp [valueOf, table, PTX.Flow.lookupLit]))
      have hw := barc_word L i 213248
      simp only [Nat.cast_ofNat] at hw
      rwa [hw] at this
    have hal := bar_al hsa i 213248 (by norm_num)
    obtain ⟨x, hp⟩ : ∃ x, t.regs 579 = some (.bits 32 x) :=
      ⟨_, holds_mem hH (tbl_mem (v := .bits 32 (andW (notW (quotW i)) (BitVec.ofInt 64 1)))
        (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit]))⟩
    refine mbarWait_bits_ok hr ?_ ⟨_, readBits_bits hp⟩ f
    exact wrap_al _ (Nat.mod_lt _ (by norm_num)) hal
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_0)
    exact warpBar_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_4)
    have hr : t.regs 580 =
        some (.bits 32 (BitVec.ofNat 64 ((L.sharedBase + bOff i + 213216) % 2 ^ 32))) :=
      hbar .arrive hH (by live_dec)
    have hal := bar_al hsa i 213216 (by norm_num)
    refine mbarArrive_imm_ok hr ?_ f
    exact wrap_al _ (Nat.mod_lt _ (by norm_num)) hal
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_205)
    have r : t.regs 2053 = some (valueOf L g ⟨.ldb0, pro, i, n, p0, p1, ln⟩ 2053) :=
      holds_mem hH (Flow.mem_factsFrom (by live_dec))
    simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] at r
    refine gload_al4 r (madWide4_al _ _ ?_) f
    simp only [BitVec.toNat_ofNat]
    simp only at hbt
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_1)
    exact warpBar_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_24)
    exact elect_imm_ok f
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_2)
    exact warpBar_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_25)
    exact elect_imm_ok f
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_206)
    have r : t.regs 2054 = some (valueOf L g ⟨.ldb1, pro, i, n, p0, p1, ln⟩ 2054) :=
      holds_mem hH (Flow.mem_factsFrom (by live_dec))
    simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] at r
    refine gload_al4 r (add64_4_al _ (madWide4_al _ _ ?_)) f
    simp only [BitVec.toNat_ofNat]
    simp only at hbt
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_3)
    exact warpBar_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_26)
    exact elect_imm_ok f
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_4)
    exact warpBar_ok f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_27)
    exact elect_imm_ok f
  · simp [Site.cp] at hcp
  · simp [Site.cp] at hcp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_29)
    exact barSync_imm_ok (id := 1) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_6)
    exact plainOk_tmpl hb (by decide) f

/-- **The loader's sites that need nothing but the launch have no undefined-behaviour
template.** -/
theorem tmpl_ok (hpre : Pre Q L mem0) (hg : g < L.threads) {d : D} {ins : Instr}
    (_hi : Inv L g d) (hbt : natOf64 (d.pro 2020) % 4 = 0) (hw70 : natOf (d.pro 531) % 8 = 0)
    (hrd1 : d.pro 1949 = .ptr 64 true (.param (param "1")) 0)
    (hH : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  cases hcp : d.site.cp
  · exact tmpl_ok_rest hpre hg hcp hbt hw70 hrd1 hH hc f
  · exact tmpl_ok_cp hpre hg hcp hbt hw70 hrd1 hH hc f

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
