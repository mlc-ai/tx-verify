-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmSm
public import Kernels.InklingRelDecode.Proof.Thread.ProASound
public import Kernels.InklingRelDecode.Proof.Thread.EvDProLoad
public import Kernels.InklingRelDecode.Proof.Thread.LpQLoad
public import Kernels.InklingRelDecode.Proof.Thread.TmProQ
public import Kernels.InklingRelDecode.Proof.Thread.TmProC

@[expose] public section

/-! # The prologue's sites are not undefined behaviour

Proved: the sites whose instruction has no register operand (`Tm.staticAt`: the register request,
the two proxy fences, the named barriers, the elections, the warp barriers), the three request-word
loads (`cu_seqlens_q`, `seq_lens`: the pointers are the launch's and aligned), the six
block-table loads and the 64 query loads (`qload_ok`: the launch pointers are aligned), the two
shared stores of words at fixed addresses (`word_ok`), the 32 elements of the query stores
(`stq_ok`, `TmProQ.lean`), the twelve K/V copies (`ptc_ok`, `TmProC.lean`), the twelve
`mbarrier.init` and three `mbarrier.arrive.expect_tx` (barrier addresses at the shared base plus
a multiple of 8) and the three broadcasts of the warp index. `Site.tmRest` lists the others. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Tm
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- The sites proved here besides the static ones. -/
def Site.proved : Site → Bool
  | .ldCu0 | .ldCu1 | .ldSk => true
  | .in0 | .in1 | .in2 | .in3 | .in4 | .in5 | .in6 | .in7 | .in8 | .in9 | .in10 | .in11 => true
  | .arr0 | .arr1 | .arr2 | .psh0 | .psh1 | .psh2 => true
  | _ => false

/-- The global loads of the block table and of the query tile, proved from the alignment of
the two launch pointers (`qload_ok`). -/
def Site.qload (s : Site) : Bool := decide (s ∈ lbSites) || decide (s ∈ ldqSites)

/-- The two shared stores at the end of the prologue: `st8` (`st.shared.b32` of an immediate at
`global_smem + 213336`) and `st9_0`, `st9_1` (the elements of `st.shared.v2.b32` of `%r32`,
`%r26` at `global_smem + 212992`). -/
def Site.word : Site → Bool
  | .st8 | .st9_0 | .st9_1 => true
  | _ => false

/-- The elements of the eight query stores. -/
def Site.qstore (s : Site) : Bool := decide (s ∈ stqSites)

/-- The twelve K/V copies. -/
def Site.ptc (s : Site) : Bool := decide (s ∈ ptcSites)

theorem ptcSites_idx {s : Site} (h : s ∈ ptcSites) : ∃ i < 12, s = ptcSite i := by
  revert h; revert s; decide

/-- The sites not proved here: those whose instruction reads a register and that `Site.proved`,
`Site.qload`, `Site.word` and `Site.qstore` do not list. -/
def Site.tmRest (s : Site) : Bool :=
  !(staticAt s.pc || s.proved || s.qload || s.word || s.qstore || s.ptc)

/-- **Every site of the prologue is proved**: none is left in `Site.tmRest`. -/
theorem Site.tmRest_eq_false (s : Site) : s.tmRest = false := by
  cases s <;> decide +kernel

/-- The twelve barrier addresses of the prologue, as the table holds them. -/
theorem mbar_regs (L : Launch) (g : Nat) (dt : Dat) (h : L.sharedBase + 213328 < 2 ^ 32) :
    v_r152 L g dt = BitVec.ofNat 64 (L.sharedBase + 213216) ∧
    v_r153 L g dt = BitVec.ofNat 64 (L.sharedBase + 213248) ∧
    v_r154 L g dt = BitVec.ofNat 64 (L.sharedBase + 213224) ∧
    v_r155 L g dt = BitVec.ofNat 64 (L.sharedBase + 213256) ∧
    v_r156 L g dt = BitVec.ofNat 64 (L.sharedBase + 213232) ∧
    v_r157 L g dt = BitVec.ofNat 64 (L.sharedBase + 213264) ∧
    v_r158 L g dt = BitVec.ofNat 64 (L.sharedBase + 213280) ∧
    v_r159 L g dt = BitVec.ofNat 64 (L.sharedBase + 213296) ∧
    v_r160 L g dt = BitVec.ofNat 64 (L.sharedBase + 213288) ∧
    v_r161 L g dt = BitVec.ofNat 64 (L.sharedBase + 213304) ∧
    v_r162 L g dt = BitVec.ofNat 64 (L.sharedBase + 213312) ∧
    v_r163 L g dt = BitVec.ofNat 64 (L.sharedBase + 213328) := by
  have key : ∀ c : Nat, L.sharedBase + c < 2 ^ 32 →
      wAdd32 (v_r205 L g dt) (BitVec.ofInt 64 (c : Int)) = BitVec.ofNat 64 (L.sharedBase + c) := by
    intro c hc
    simp only [v_r205]
    rw [wAdd32_smem L _ (by omega), Int.toNat_natCast, Nat.mod_eq_of_lt hc]
  exact ⟨key 213216 (by omega), key 213248 (by omega), key 213224 (by omega),
    key 213256 (by omega), key 213232 (by omega), key 213264 (by omega), key 213280 (by omega),
    key 213296 (by omega), key 213288 (by omega), key 213304 (by omega), key 213312 (by omega),
    key 213328 (by omega)⟩

/-- **A request-word load is not undefined behaviour**: its address is `cuBase + 4 req`,
`cuBase + 4 (req + 1)` or `seqBase + 4 req`, 4-aligned. -/
theorem cuLoad_ok (hpre : Pre Q L mem0) (hg : g < L.threads) {s : Site} {dt : Dat} {ins : Instr}
    (hi : Inv L g ⟨s, dt⟩) (hs : s = .ldCu0 ∨ s = .ldCu1 ∨ s = .ldSk)
    (hH : Holds t.regs (facts L g ⟨s, dt⟩))
    (hc : kernel.code[Site.pc s]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hm : s ∈ wordLoadSites := by
    rcases hs with rfl | rfl | rfl <;> simp [wordLoadSites]
  obtain ⟨gd, hcode⟩ := isGload_spec (wordLoad_gload _ hm)
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  obtain ⟨x, hx⟩ := wordLoad_bits L g dt _ hm
  have hr : t.regs (gloadBase s.pc) = some (b64 x.toNat) :=
    holds_reg hH (wordLoad_live _ hm) (hx.trans (bits64_eq x))
  have hA : loadAddr L g dt s = x.toNat := by simp [loadAddr, hx]
  obtain ⟨h0, h1, h2⟩ := cu_addrs hpre hg hi.args
  have hc4 := hpre.cuAlign
  have hs4 := hpre.seqAlign
  refine gload_ok hr x.isLt (Or.inr rfl) ?_ f
  rw [← hA]
  rcases hs with rfl | rfl | rfl
  · rw [h0]; omega
  · rw [h1]; omega
  · rw [h2]; omega

/-! ### The global loads of the block table and of the query tile

The address of each is a launch pointer (`btBase`, 4-aligned; `qBase`, 2-aligned) plus multiples
of the access size, in the 64-bit arithmetic of the code (`mad.wide`, `add.s64`, `shl.b64`), for
any values of the other operands. -/

/-- `mad.wide.s32 a, 4, c` is a multiple of 4 when `c` is. -/
theorem madWideS4_al (a c : BitVec 64) (hc : c.toNat % 4 = 0) :
    (wMadWideS32 a (BitVec.ofInt 64 4) c).toNat % 4 = 0 := by
  have e4 : BitVec.ofInt 64 4 = BitVec.ofNat 64 4 := by decide
  rw [e4]
  unfold wMadWideS32 intBits intOf truncBits
  have h4 : toSigned 32 (BitVec.ofNat 64 (4 % 2 ^ 64 % 2 ^ 32)) = 4 := by decide
  have hc' : (toSigned (2 * 32) (BitVec.ofNat 64 (c.toNat % 2 ^ (2 * 32)))) % 4 = 0 := by
    unfold toSigned
    have := c.isLt
    simp only [BitVec.toNat_ofNat]
    split <;> omega
  simp only [↓reduceIte, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  rw [h4]
  generalize toSigned 32 (BitVec.ofNat 64 (a.toNat % 2 ^ 32)) = x at *
  generalize toSigned (2 * 32) (BitVec.ofNat 64 (c.toNat % 2 ^ (2 * 32))) = y at *
  omega

/-- `add.s64 a, 4` is a multiple of 4 when `a` is. -/
theorem add64_4_al (a : BitVec 64) (ha : a.toNat % 4 = 0) :
    (wAdd64 a (BitVec.ofInt 64 4)).toNat % 4 = 0 := by
  unfold wAdd64 truncBits
  have h4 : (BitVec.ofInt 64 4).toNat = 4 := by decide
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, h4]
  have := a.isLt
  omega

/-- The base of a group of query loads, `mad.wide.u32 a, 2, (x0 + (m << 1))`, is even when
`x0` is. -/
theorem qbase_even (a m x0 : BitVec 64) (h : x0.toNat % 2 = 0) :
    (wMadWideU32 a (BitVec.ofInt 64 2) (wAdd64 (truncBits 64 x0)
      (wShl64 m (BitVec.ofInt 64 1)))).toNat % 2 = 0 := by
  have h1 : (truncBits 32 (BitVec.ofInt 64 1)).toNat = 1 := by decide
  have h2 : (truncBits 32 (BitVec.ofInt 64 2)).toNat = 2 := by decide
  unfold wMadWideU32 wAdd64 wShl64 intBits intOf
  simp only [h1, h2, show ¬ ((1 : Nat) ≥ 64) by omega, reduceCtorEq, ↓reduceIte]
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofInt, Nat.shiftLeft_eq]
  have := x0.isLt
  have := m.isLt
  generalize (a.toNat % 2 ^ 32 % 2 ^ 64 % 2 ^ 32 : Nat) = p
  omega

/-- `mul.wide.u32 a, 2` is even. -/
theorem mulWideU2_even (a : BitVec 64) :
    (wMulWideU32 a (BitVec.ofInt 64 2)).toNat % 2 = 0 := by
  have h2 : (truncBits 32 (BitVec.ofInt 64 2)).toNat = 2 := by decide
  unfold wMulWideU32
  simp only [show (some IType.u == some IType.s) = false by decide, Bool.false_eq_true,
    ↓reduceIte, h2, BitVec.toNat_ofNat]
  have := (truncBits 32 a).isLt
  omega


/-- The base registers of the four groups of query loads are even when the `Q` pointer is. -/
theorem qReg_even (L : Launch) (g : Nat) (dt : Dat) (h : dt.pro.x0.toNat % 2 = 0) (j : Nat) :
    qReg L g dt j % 2 = 0 := by
  unfold qReg
  split
  · exact qbase_even _ _ _ h
  · exact qbase_even _ _ _ h
  · exact qbase_even _ _ _ h
  · exact qbase_even _ _ _ h

/-- **A query load is not undefined behaviour**: its address is the `Q` pointer plus even
offsets. -/
theorem ldq_ok {dt : Dat} {k : Nat} {ins : Instr} (hk : k < 64) (hx0 : dt.pro.x0.toNat % 2 = 0)
    (hH : Holds t.regs (facts L g ⟨ldqSite k, dt⟩))
    (hc : kernel.code[(ldqSite k).pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  obtain ⟨gd, hcode⟩ := isGload_spec (ldq_gload k hk)
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  obtain ⟨x, hx, hxn⟩ := ldq_reg L g dt hk
  have hr : t.regs (gloadBase (ldqSite k).pc) = some (b64 x.toNat) :=
    holds_reg hH (ldq_live k hk) (hx.trans (bits64_eq x))
  refine gload_ok hr x.isLt (Or.inl rfl) ?_ f
  rw [hxn]
  have e1 := qReg_even L g dt hx0 (k / 16)
  have e2 := mulWideU2_even (v_r28 L g dt)
  have e3 : qOff (k % 16) % 2 = 0 := by unfold qOff; split <;> omega
  simp only [v_rd257]
  omega

theorem lbSites_idx {s : Site} (h : s ∈ lbSites) : ∃ k < 6, s = lbSite k := by
  simp only [lbSites, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩

/-- The address registers of the six block-table loads are multiples of 4 when the block-table
base is. -/
theorem lb_al4 (L : Launch) (g : Nat) (dt : Dat) (h : dt.pro.btB % 4 = 0) {k : Nat}
    (hk : k < 6) : loadAddr L g dt (lbSite k) % 4 = 0 := by
  have h7 : (v_rd7 L g dt).toNat % 4 = 0 := by
    refine madWideS4_al _ _ ?_
    simp only [v_rd72, BitVec.toNat_ofNat]
    omega
  interval_cases k
  · have e : valueOf L g dt (gloadBase (lbSite 0).pc) = .bits 64 (v_rd123 L g dt) := rfl
    rw [loadAddr, e]
    exact madWideS4_al _ _ h7
  · have e : valueOf L g dt (gloadBase (lbSite 1).pc) = .bits 64 (v_rd124 L g dt) := rfl
    rw [loadAddr, e]
    exact add64_4_al _ (madWideS4_al _ _ h7)
  · have e : valueOf L g dt (gloadBase (lbSite 2).pc) = .bits 64 (v_rd125 L g dt) := rfl
    rw [loadAddr, e]
    exact madWideS4_al _ _ h7
  · have e : valueOf L g dt (gloadBase (lbSite 3).pc) = .bits 64 (v_rd126 L g dt) := rfl
    rw [loadAddr, e]
    exact add64_4_al _ (madWideS4_al _ _ h7)
  · have e : valueOf L g dt (gloadBase (lbSite 4).pc) = .bits 64 (v_rd127 L g dt) := rfl
    rw [loadAddr, e]
    exact madWideS4_al _ _ h7
  · have e : valueOf L g dt (gloadBase (lbSite 5).pc) = .bits 64 (v_rd128 L g dt) := rfl
    rw [loadAddr, e]
    exact add64_4_al _ (madWideS4_al _ _ h7)

/-- **A block-table load is not undefined behaviour**. -/
theorem lb_ok {dt : Dat} {k : Nat} {ins : Instr} (hk : k < 6) (hbt : dt.pro.btB % 4 = 0)
    (hH : Holds t.regs (facts L g ⟨lbSite k, dt⟩))
    (hc : kernel.code[(lbSite k).pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hm : lbSite k ∈ wordLoadSites := by
    interval_cases k <;> decide
  obtain ⟨gd, hcode⟩ := isGload_spec (wordLoad_gload _ hm)
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  obtain ⟨x, hx⟩ := wordLoad_bits L g dt _ hm
  have hr : t.regs (gloadBase (lbSite k).pc) = some (b64 x.toNat) :=
    holds_reg hH (wordLoad_live _ hm) (hx.trans (bits64_eq x))
  have hA : loadAddr L g dt (lbSite k) = x.toNat := by simp [loadAddr, hx]
  refine gload_ok hr x.isLt (Or.inr rfl) ?_ f
  rw [← hA]
  exact lb_al4 L g dt hbt hk


/-- **A block-table load or a query load is not undefined behaviour.** -/
theorem qload_ok {s : Site} {dt : Dat} {ins : Instr} (hq : s.qload = true)
    (hbt : dt.pro.btB % 4 = 0) (hx0 : dt.pro.x0.toNat % 2 = 0)
    (hH : Holds t.regs (facts L g ⟨s, dt⟩)) (hc : kernel.code[s.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  simp only [Site.qload, Bool.or_eq_true, decide_eq_true_eq] at hq
  rcases hq with hq | hq
  · obtain ⟨k, hk, rfl⟩ := lbSites_idx hq
    exact lb_ok hk hbt hH hc f
  · obtain ⟨k, hk, rfl⟩ := ldqSites_idx hq
    exact ldq_ok hk hx0 hH hc f

/-- **The two shared stores of words at fixed addresses are not undefined behaviour.** -/
theorem word_ok {s : Site} {dt : Dat} {ins : Instr} (hw : s.word = true)
    (hsa : L.sharedBase % 1024 = 0) (hsr : L.sharedBase + sharedBytes ≤ 2 ^ 18)
    (hsub : t.sub = s.sub) (hH : Holds t.regs (facts L g ⟨s, dt⟩))
    (hc : kernel.code[s.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  cases s <;> simp only [Site.word] at hw <;> try exact absurd hw (by decide)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_8)
    refine storeAccess_ok (o := .imm 16777730) rfl rfl rfl rfl rfl rfl (by decide) (by decide)
      (by decide) ?_ (by simp [hsub, Site.sub]) ⟨_, rfl, rfl⟩ f
    exact ⟨_, accessLoc_sharedSym (off := 213336) rfl rfl rfl
      (by unfold sharedBytes at hsr; omega), by simp [DType.width]; omega⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_9)
    refine storeAccess_ok (o := .reg 493) rfl rfl rfl rfl rfl rfl (by decide) (by decide)
      (by decide) ?_ (by simp [hsub, Site.sub]) ⟨_, readValue_reg (holds_reg
        (v := .bits 32 (v_r32 L g dt)) hH (by live_dec) (by simp [valueOf, table, lookupLit])),
        rfl⟩ f
    exact ⟨_, accessLoc_sharedSym (off := 212992) rfl rfl rfl
      (by unfold sharedBytes at hsr; omega), by simp [DType.width]; omega⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_9)
    refine storeAccess_ok (o := .reg 487) rfl rfl rfl rfl rfl rfl (by decide) (by decide)
      (by decide) ?_ (by simp [hsub, Site.sub]) ⟨_, readValue_reg (holds_reg
        (v := .bits 32 (v_r26 L g dt)) hH (by live_dec) (by simp [valueOf, table, lookupLit])),
        rfl⟩ f
    exact ⟨_, accessLoc_sharedSym (off := 212992) rfl rfl rfl
      (by unfold sharedBytes at hsr; omega), by simp [DType.width]; omega⟩

/-- **The prologue's other sites have no undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre Q L mem0) (hg : g < L.threads) {d : D} {ins : Instr}
    (hi : Inv L g d) (hbt : d.dt.pro.btB % 4 = 0) (hx0 : d.dt.pro.x0.toNat % 2 = 0)
    (hrd1 : d.dt.pro.rest 1949 = .ptr 64 true (.param (param "1")) 0)
    (hw70 : d.dt.pro.w70 % 8 = 0)
    (hsub : t.sub = d.site.sub) (hs : d.site.tmRest = false) (hH : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hsa := hpre.sharedAlignment
  have hsr := hpre.sharedRange
  by_cases hst : staticAt d.site.pc = true
  · exact static_tmpl hb hst hc f
  by_cases hq : d.site.qload = true
  · exact qload_ok hq hbt hx0 hH hc f
  by_cases hw : d.site.word = true
  · exact word_ok hw hsa hsr hsub hH hc f
  by_cases hqs : d.site.qstore = true
  · obtain ⟨s, dt⟩ := d
    obtain ⟨i, hi32, rfl⟩ := stqSites_idx (of_decide_eq_true hqs)
    exact stq_ok hi32 hi.args.tid (by unfold SbRoom sharedBytes at *; omega) hsa hi.qb hsub hH hc f
  by_cases hpt : d.site.ptc = true
  · obtain ⟨s, dt⟩ := d
    obtain ⟨i, hi12, rfl⟩ := ptcSites_idx (of_decide_eq_true hpt)
    exact ptc_ok hpre hg hi12 hrd1 hw70 hH hc f
  have hp : d.site.proved = true := by
    simp only [Site.tmRest, Bool.not_eq_false', Bool.or_eq_true] at hs
    exact ((((hs.resolve_right hpt).resolve_right hqs).resolve_right hw).resolve_right
      hq).resolve_left hst
  obtain ⟨s, dt⟩ := d
  have hmb := mbar_regs L g dt (by omega)
  obtain ⟨e152, e153, e154, e155, e156, e157, e158, e159, e160, e161, e162, e163⟩ := hmb
  cases s <;> simp only [Site.proved] at hp <;> try exact absurd hp (by decide)
  · exact cuLoad_ok hpre hg hi (Or.inl rfl) hH hc f
  · exact cuLoad_ok hpre hg hi (Or.inr (Or.inl rfl)) hH hc f
  · exact cuLoad_ok hpre hg hi (Or.inr (Or.inr rfl)) hH hc f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_0)
    exact mbarInit_one_ok (a := L.sharedBase + 213216) (holds_reg (v := b32 (L.sharedBase + 213216))
      hH (by live_dec) (by simp [valueOf, table, lookupLit, e152, b32])) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_1)
    exact mbarInit_one_ok (a := L.sharedBase + 213248) (holds_reg (v := b32 (L.sharedBase + 213248))
      hH (by live_dec) (by simp [valueOf, table, lookupLit, e153, b32])) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_2)
    exact mbarInit_one_ok (a := L.sharedBase + 213224) (holds_reg (v := b32 (L.sharedBase + 213224))
      hH (by live_dec) (by simp [valueOf, table, lookupLit, e154, b32])) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_3)
    exact mbarInit_one_ok (a := L.sharedBase + 213256) (holds_reg (v := b32 (L.sharedBase + 213256))
      hH (by live_dec) (by simp [valueOf, table, lookupLit, e155, b32])) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_4)
    exact mbarInit_one_ok (a := L.sharedBase + 213232) (holds_reg (v := b32 (L.sharedBase + 213232))
      hH (by live_dec) (by simp [valueOf, table, lookupLit, e156, b32])) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_5)
    exact mbarInit_one_ok (a := L.sharedBase + 213264) (holds_reg (v := b32 (L.sharedBase + 213264))
      hH (by live_dec) (by simp [valueOf, table, lookupLit, e157, b32])) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_6)
    exact mbarInit_one_ok (a := L.sharedBase + 213280) (holds_reg (v := b32 (L.sharedBase + 213280))
      hH (by live_dec) (by simp [valueOf, table, lookupLit, e158, b32])) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_7)
    exact mbarInit_one_ok (a := L.sharedBase + 213296) (holds_reg (v := b32 (L.sharedBase + 213296))
      hH (by live_dec) (by simp [valueOf, table, lookupLit, e159, b32])) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_8)
    exact mbarInit_one_ok (a := L.sharedBase + 213288) (holds_reg (v := b32 (L.sharedBase + 213288))
      hH (by live_dec) (by simp [valueOf, table, lookupLit, e160, b32])) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_9)
    exact mbarInit_one_ok (a := L.sharedBase + 213304) (holds_reg (v := b32 (L.sharedBase + 213304))
      hH (by live_dec) (by simp [valueOf, table, lookupLit, e161, b32])) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_10)
    exact mbarInit_one_ok (a := L.sharedBase + 213312) (holds_reg (v := b32 (L.sharedBase + 213312))
      hH (by live_dec) (by simp [valueOf, table, lookupLit, e162, b32])) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_11)
    exact mbarInit_one_ok (a := L.sharedBase + 213328) (holds_reg (v := b32 (L.sharedBase + 213328))
      hH (by live_dec) (by simp [valueOf, table, lookupLit, e163, b32])) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_0)
    have hr : t.regs 613 = some (.bits 32 (BitVec.ofNat 64 (L.sharedBase + 213216))) :=
      holds_reg hH (by live_dec) (by simp [valueOf, table, lookupLit, e152])
    refine mbarArrive_imm_ok hr ?_ f
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_1)
    exact shfl_imm_ok (p := none) (x := BitVec.ofNat 64 (tidOf L g / 32)) (.inr rfl) hb
      (holds_reg (v := .bits 32 (BitVec.ofNat 64 (tidOf L g / 32))) hH (by live_dec)
        (by simp [valueOf, table, lookupLit, v_r3])) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_1)
    have hr : t.regs 615 = some (.bits 32 (BitVec.ofNat 64 (L.sharedBase + 213224))) :=
      holds_reg hH (by live_dec) (by simp [valueOf, table, lookupLit, e154])
    refine mbarArrive_imm_ok hr ?_ f
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_2)
    exact shfl_imm_ok (p := none) (x := BitVec.ofNat 64 (tidOf L g / 32)) (.inr rfl) hb
      (holds_reg (v := .bits 32 (BitVec.ofNat 64 (tidOf L g / 32))) hH (by live_dec)
        (by simp [valueOf, table, lookupLit, v_r3])) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_2)
    have hr : t.regs 617 = some (.bits 32 (BitVec.ofNat 64 (L.sharedBase + 213232))) :=
      holds_reg hH (by live_dec) (by simp [valueOf, table, lookupLit, e156])
    refine mbarArrive_imm_ok hr ?_ f
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, wrapAddr_ofNat (by omega)]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_3)
    exact shfl_imm_ok (p := none) (x := BitVec.ofNat 64 (tidOf L g / 32)) (.inr rfl) hb
      (holds_reg (v := .bits 32 (BitVec.ofNat 64 (tidOf L g / 32))) hH (by live_dec)
        (by simp [valueOf, table, lookupLit, v_r3])) f

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
