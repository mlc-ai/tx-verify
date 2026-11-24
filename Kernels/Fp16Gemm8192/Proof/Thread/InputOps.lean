-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RingUsers
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderTasks
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Layout
public import Lemmas.Flow.TensorRoute
public import Lemmas.Flow.NotTcMma
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.TcTmpl
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.Base

@[expose] public section

/-! # The input ring's copies and operand reads at their sites

The loader's load of block `b`, part `j`, copies the map's 64 x 128 box into tile `j` of slot
`b % 4` of the loader's CTA (`Loader.load_stage`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-! ## The kernel's loads and MMAs are at the loader's and the MMA thread's sites -/

/-- The positions of the loader's loads. -/
def loadPcs : List Nat := [Flow.tensorCopy_0, Flow.tensorCopy_1, Flow.tensorCopy_2,
    Flow.tensorCopy_3, Flow.tensorCopy_4, Flow.tensorCopy_5, Flow.tensorCopy_6, Flow.tensorCopy_7,
    Flow.tensorCopy_8, Flow.tensorCopy_9, Flow.tensorCopy_10, Flow.tensorCopy_11,
    Flow.tensorCopy_12, Flow.tensorCopy_13, Flow.tensorCopy_14, Flow.tensorCopy_15,
    Flow.tensorCopy_16, Flow.tensorCopy_17, Flow.tensorCopy_18, Flow.tensorCopy_19,
    Flow.tensorCopy_20, Flow.tensorCopy_21, Flow.tensorCopy_22, Flow.tensorCopy_23]

/-- The positions of the MMA thread's MMAs. -/
def mmaPcs : List Nat := [Flow.mma_0, Flow.mma_1, Flow.mma_2, Flow.mma_3, Flow.mma_4, Flow.mma_5,
    Flow.mma_6, Flow.mma_7, Flow.mma_8, Flow.mma_9, Flow.mma_10, Flow.mma_11, Flow.mma_12,
    Flow.mma_13, Flow.mma_14, Flow.mma_15]

/-- The kernel's tensor loads are the loader's (decided on the code, in one pass). -/
theorem kernel_load_pcs : OpPcsFast kernel.code tensorOp loadPcs = true := by
  decide +kernel

/-- The kernel's MMAs are the MMA thread's (decided on the code, in one pass). -/
theorem kernel_mma_pcs : OpPcsFast kernel.code tcMmaOp mmaPcs = true := by
  decide +kernel

/-- A state at a load position is the loader at a load. -/
theorem load_state {L : Launch} {g : Nat} {d : ThreadD} (h : (code L g).pc d ∈ loadPcs) :
    ∃ l b j, d = .inr (.loader l) ∧ l.site = .load b j := by
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  all_goals change site.pc ∈ _ at h
  all_goals (cases site <;> first
    | exact ⟨_, _, _, rfl, rfl⟩
    | (exfalso; clear * - h; revert h; decide +kernel +revert))

/-- A state at an MMA position is the MMA thread at an MMA. -/
theorem mma_state {L : Launch} {g : Nat} {d : ThreadD} (h : (code L g).pc d ∈ mmaPcs) :
    ∃ m s j, d = .inr (.mma m) ∧ m.site = .mma s j := by
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  all_goals change site.pc ∈ _ at h
  all_goals (cases site <;> first
    | exact ⟨_, _, _, rfl, rfl⟩
    | (exfalso; clear * - h; revert h; decide +kernel +revert))

namespace Loader

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t u : TState} {e : Event}

/-- A tensor load through a map held as the A or B parameter, to a destination held as a 32-bit
shared address: the copy of the map's 64 x 128 box into that address of the thread's CTA. -/
theorem copy_stage (hpre : Pre P L mem0) {dst mb r : Nat} {cs : List Opnd} {pc : Nat}
    (hf : Fires pc (eventTmpl Prod L g t (.cpTensor true true dst 0 (.reg r) cs mb 0 none .tile))
      e (some u))
    {name : String} (hr0 : t.regs r = some (.ptr 64 true (.param name) 0))
    (hn : name = "gemm_kernel_param_0" ∨ name = "gemm_kernel_param_1")
    {st : Nat} (hd : t.regs dst = some (b32 st)) (hst : st < 2 ^ 32) :
    ∃ a sp, e = ⟨pc, .tensorIssue a sp⟩ ∧ ∃ base cls origin,
      sp = stageCopy (Fp16Gemm8192.mapA base cls) origin (g / L.block) st sp.mbar true .two ∧
      L.tensorMaps a = some ⟨1, Fp16Gemm8192.mapA base cls⟩ ∧
      (L.paramObjects "gemm_kernel_param_0" = some (mapParam "gemm_kernel_param_0", a) ∨
        L.paramObjects "gemm_kernel_param_1" = some (mapParam "gemm_kernel_param_1", a)) ∧
      TensorCopy.RoutingOk L (g / L.block) sp := by
  obtain ⟨a, sp, rfl, hma, ⟨d, hd', hdesc⟩, hrows, hdst, hca, hgrp⟩ := fires_cpTensor_box hf
  have hroute := (fires_cpTensor_route hf rfl).1
  obtain ⟨M, base, cls, hpar, h1, h2, hD⟩ : ∃ M base cls,
      L.paramObjects name = some (mapParam name, M) ∧ M % 128 = 0 ∧ M + 128 ≤ 2 ^ 64 ∧
      L.tensorMaps M = some ⟨1, Fp16Gemm8192.mapA base cls⟩ := by
    rcases hn with rfl | rfl
    · exact ⟨_, _, _, hpre.paramA, hpre.mapAlignment.1, hpre.mapRange.1, hpre.mapA⟩
    · exact ⟨_, _, _, hpre.paramB, hpre.mapAlignment.2.1, hpre.mapRange.2.1, hpre.mapB⟩
  obtain rfl : a = M := by
    simp only [tensorMapAddress, readValue, readReg, hr0, hpar, mapParam, ParamObjectDecl.bytes,
      bind, Except.bind, pure, Except.pure, le_refl, Nat.ofNat_pos, h1,
      show M + 128 ≤ 2 ^ 64 from h2, and_self, ↓reduceIte, Except.ok.injEq] at hma
    exact hma.symm
  refine ⟨a, sp, rfl, base, cls, ?_⟩
  obtain ⟨⟨outer, desc, origin, sb, rows⟩, mbar, ca, grp⟩ := sp
  rw [hD] at hd'
  simp only [Option.some.injEq] at hd'
  cases hd'
  simp only [TensorMode.transfer] at hdesc
  subst hdesc
  simp only [iff_true] at hrows
  subst hrows
  simp only at hca hgrp
  subst hca hgrp
  have hsb : sb = ⟨.shared, g / L.block, st⟩ := by
    simp only [sharedEffAddr, readReg, hd, b32, bind, Except.bind, pure, Except.pure, readBits,
      Except.ok.injEq] at hdst
    rw [← hdst]
    simp only [truncBits]
    simp
    omega
  subst hsb
  refine ⟨origin, rfl, hD, ?_, hroute⟩
  rcases hn with rfl | rfl
  · exact .inl hpar
  · exact .inr hpar

set_option maxHeartbeats 8000000 in
/-- **The loader's loads.** The load at block `b`, part `j`, is a tensor issue completing on slot
`b % 4`'s full barrier in the cluster's leader CTA: the copy of the A or B map's 64 x 128 box
into tile `j` of slot `b % 4` of the loader's CTA. -/
theorem load_stage (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {ins : Instr} (b : Fin 8)
    (j : Fin 3) (hs : d.site = .load b j) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    ∃ a sp, e = ⟨d.site.pc, .tensorIssue a sp⟩ ∧
      sp.mbar = InputRing.fullLoc L ((g / L.block) / 2) (InputRing.slotOf b) ∧
      ∃ base cls origin, sp = stageCopy (Fp16Gemm8192.mapA base cls) origin (g / L.block)
        (L.sharedBase + InputRing.stageOff (InputRing.slotOf b).val j.val) sp.mbar true .two ∧
        L.tensorMaps a = some ⟨1, Fp16Gemm8192.mapA base cls⟩ ∧
        (L.paramObjects "gemm_kernel_param_0" = some (mapParam "gemm_kernel_param_0", a) ∨
          L.paramObjects "gemm_kernel_param_1" = some (mapParam "gemm_kernel_param_1", a)) ∧
        TensorCopy.RoutingOk L (g / L.block) sp := by
  obtain ⟨a, sp, he, hm⟩ := load_event hpre hg b j hs h hc hf
  refine ⟨a, sp, he, hm, ?_⟩
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf he ⊢
  subst hs
  have key : ∃ base cls origin, sp = stageCopy (Fp16Gemm8192.mapA base cls) origin (g / L.block)
      (L.sharedBase + InputRing.stageOff (InputRing.slotOf b).val j.val) sp.mbar true .two ∧
      L.tensorMaps a = some ⟨1, Fp16Gemm8192.mapA base cls⟩ ∧
      (L.paramObjects "gemm_kernel_param_0" = some (mapParam "gemm_kernel_param_0", a) ∨
        L.paramObjects "gemm_kernel_param_1" = some (mapParam "gemm_kernel_param_1", a)) ∧
      TensorCopy.RoutingOk L (g / L.block) sp := by
    have hst : L.sharedBase + InputRing.stageOff (InputRing.slotOf b).val j.val < 2 ^ 32 := by
      have := InputRing.stageOff_lt (InputRing.slotOf b).isLt j.isLt
      omega
    fin_cases b <;> fin_cases j
    all_goals
      code_at hc
      subst hc
      obtain ⟨a', sp', he', base, cls, origin, hrest⟩ := copy_stage hpre hf
        ((reg_at h.2.2.2.2 (by lit_mem)).trans (congrArg some (by loader_values; rfl))) (by simp)
        ((reg_at h.2.2.2.2 (by lit_mem)).trans (congrArg some (by
          loader_values; simp [InputRing.stageOff, InputRing.slotOf]))) hst
      rw [he] at he'
      simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at he'
      obtain ⟨-, rfl, rfl⟩ := he'
      exact ⟨base, cls, origin, hrest⟩
  exact key

end Loader

namespace Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t u : TState} {e : Event}

/-- The MMAs' CTA pair: the two CTAs of the issuing thread's cluster. -/
theorem make_operands (hpre : Pre P L mem0) (hg : g < L.threads) (da db : TcShared.Descriptor) :
    TcMma.makeOperands L (g / L.block) InputRing.mmaDescriptor da db =
      some ⟨InputRing.mmaDescriptor, da, db, g / L.block / 2 * 2, g / L.block / 2 * 2 + 1, none,
        {}⟩ := by
  have hcta : g / L.block < 1024 := by
    simp only [Launch.threads, hpre.grid, hpre.block] at hg ⊢
    omega
  have hc : g / L.block < L.grid := by rw [hpre.grid]; exact hcta
  simp [TcMma.makeOperands, Launch.ctaGroup, Launch.ctaGroupRanks, InputRing.mmaDescriptor,
    CtaGroup.size, rankOfCta_eq hpre, List.range_succ, peerCta_eq hpre hc]

/-- An MMA instruction of the kernel, from its register facts: the MMA of the two shared
descriptors' K step `j` over the cluster's CTA pair. -/
theorem mma_tmpl (hpre : Pre P L mem0) (hg : g < L.threads) {ra rb pred : Nat}
    {c sa sb j : Nat} {acc : Bool} (hd : t.regs 861 = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs ra = some (b64 (descC + sa + 2 * j)))
    (hB : t.regs rb = some (b64 (descC + sb + 2 * j)))
    (hI : t.regs 862 = some (b32 272629776)) (hZ : t.regs 863 = some (b32 0))
    (hp : t.regs pred = some (.pred acc)) (hsa : sa + 2 * j < 32768) (hsb : sb + 2 * j < 32768) :
    eventTmpl Prod L g t (.tcMma (.dense .two false .f16 861 (.smem (.reg ra)) (.reg rb)
      (.reg 862) [.reg 863, .reg 863, .reg 863, .reg 863, .reg 863, .reg 863,
        .reg 863, .reg 863] (.reg pred))) =
      .tc (.mma c ⟨InputRing.mmaDescriptor, stepDescriptor (16 * sa) 0 j,
        stepDescriptor (16 * sb) 0 j, g / L.block / 2 * 2, g / L.block / 2 * 2 + 1, none, {}⟩ acc
        (List.replicate 8 0)) (PTX.next t) := by
  have hz : readBits L g t 32 (.reg 863) = .ok (BitVec.ofNat 64 0) :=
    readBits_b32 hZ (by decide)
  have hm : [Opnd.reg 863, .reg 863, .reg 863, .reg 863, .reg 863,
      .reg 863, .reg 863, .reg 863].mapM (readBits L g t 32) =
      .ok (List.replicate 8 (BitVec.ofNat 64 0)) := by
    simp [List.mapM_cons, hz]
    rfl
  simp only [eventTmpl]
  rw [tc_mma hg hd hc hA (by unfold descC; omega) hB (by unfold descC; omega) hI (by decide) hm
    (by rfl) hp (production_descriptor hsa rfl) (production_descriptor hsb rfl) (by rfl)
    (make_operands hpre hg _ _)]
  rfl

/-- The A descriptor of slot `s`, K step `j`, of MMA warp `8 + w % 2`, as the code builds it. -/
theorem aDesc_units (L : Launch) (hsb : L.sharedBase % 1024 = 0) (w s j : Nat) :
    aDesc L w + 2048 * s + 2 * j =
      descC + (L.sharedBase + InputRing.stageOff s (w % 2)) / 16 + 2 * j := by
  unfold aDesc InputRing.stageOff
  have := Nat.mod_lt w (show 0 < 2 by decide)
  split_ifs <;> omega

/-- The B descriptor of slot `s`, K step `j`, as the code builds it. -/
theorem bDesc_units (L : Launch) (hsb : L.sharedBase % 1024 = 0) (s j : Nat) :
    descC + bBase L + 1024 * s + 2 * j =
      descC + (L.sharedBase + InputRing.stageOff s 2) / 16 + 2 * j := by
  unfold bBase InputRing.stageOff
  simp only [↓reduceIte]
  omega

/-- The register holding the A descriptor of the MMA at slot `s`, K step `j`. -/
def aReg : Fin 4 → Fin 4 → Nat
  | 0, 0 => 934
  | 0, 1 => 936
  | 0, 2 => 938
  | 0, 3 => 940
  | 1, 0 => 942
  | 1, 1 => 944
  | 1, 2 => 946
  | 1, 3 => 948
  | 2, 0 => 950
  | 2, 1 => 952
  | 2, 2 => 954
  | 2, 3 => 956
  | 3, 0 => 958
  | 3, 1 => 960
  | 3, 2 => 962
  | 3, 3 => 964

/-- The register holding the B descriptor of the MMA at slot `s`, K step `j`. -/
def bReg : Fin 4 → Fin 4 → Nat
  | 0, 0 => 935
  | 0, 1 => 937
  | 0, 2 => 939
  | 0, 3 => 941
  | 1, 0 => 943
  | 1, 1 => 945
  | 1, 2 => 947
  | 1, 3 => 949
  | 2, 0 => 951
  | 2, 1 => 953
  | 2, 2 => 955
  | 2, 3 => 957
  | 3, 0 => 959
  | 3, 1 => 961
  | 3, 2 => 963
  | 3, 3 => 965

/-- The predicate register of the MMA at slot `s`, K step `j` (whether it accumulates). -/
def pReg : Fin 4 → Fin 4 → Nat
  | 0, 0 => 1007
  | 0, 1 => 1008
  | 0, 2 => 1009
  | 0, 3 => 1010
  | 1, 0 => 1012
  | 1, 1 => 1013
  | 1, 2 => 1014
  | 1, 3 => 1015
  | 2, 0 => 1017
  | 2, 1 => 1018
  | 2, 2 => 1019
  | 2, 3 => 1020
  | 3, 0 => 1022
  | 3, 1 => 1023
  | 3, 2 => 1024
  | 3, 3 => 1025

/-- The MMA at slot `s`, K step `j`, with its registers. -/
theorem code_mma_regs : ∀ s j : Fin 4, kernel.code[(Site.mma s j).pc]? =
    some ⟨none, .tcMma (.dense .two false .f16 861 (.smem (.reg (aReg s j))) (.reg (bReg s j))
      (.reg 862) [.reg 863, .reg 863, .reg 863, .reg 863, .reg 863, .reg 863,
        .reg 863, .reg 863] (.reg (pReg s j)))⟩
  | 0, 0 => Flow.code_mma_0
  | 0, 1 => Flow.code_mma_1
  | 0, 2 => Flow.code_mma_2
  | 0, 3 => Flow.code_mma_3
  | 1, 0 => Flow.code_mma_4
  | 1, 1 => Flow.code_mma_5
  | 1, 2 => Flow.code_mma_6
  | 1, 3 => Flow.code_mma_7
  | 2, 0 => Flow.code_mma_8
  | 2, 1 => Flow.code_mma_9
  | 2, 2 => Flow.code_mma_10
  | 2, 3 => Flow.code_mma_11
  | 3, 0 => Flow.code_mma_12
  | 3, 1 => Flow.code_mma_13
  | 3, 2 => Flow.code_mma_14
  | 3, 3 => Flow.code_mma_15

theorem aReg_live : ∀ s j : Fin 4, aReg s j ∈ Flow.live (Site.mma s j).pc := by
  intro s j
  fin_cases s <;> fin_cases j <;> table_decide

theorem bReg_live : ∀ s j : Fin 4, bReg s j ∈ Flow.live (Site.mma s j).pc := by
  intro s j
  fin_cases s <;> fin_cases j <;> table_decide

theorem pReg_live : ∀ s j : Fin 4, pReg s j ∈ Flow.live (Site.mma s j).pc := by
  intro s j
  fin_cases s <;> fin_cases j <;> table_decide

theorem fixed_live : ∀ s j : Fin 4, 861 ∈ Flow.live (Site.mma s j).pc ∧
    862 ∈ Flow.live (Site.mma s j).pc ∧ 863 ∈ Flow.live (Site.mma s j).pc := by
  intro s j
  fin_cases s <;> fin_cases j <;> exact ⟨by table_decide, by table_decide, by table_decide⟩

theorem aReg_value (L : Launch) (g : Nat) (d : D) : ∀ s j : Fin 4,
    valueOf L g d (aReg s j) = b64 (aDesc L d.w + 2048 * s.val + 2 * j.val) := by
  intro s j
  fin_cases s <;> fin_cases j
  all_goals (simp only [aReg]; mma_values)
  all_goals simp

theorem bReg_value (L : Launch) (g : Nat) (d : D) : ∀ s j : Fin 4,
    valueOf L g d (bReg s j) = b64 (descC + bBase L + 1024 * s.val + 2 * j.val) := by
  intro s j
  fin_cases s <;> fin_cases j
  all_goals (simp only [bReg]; mma_values)
  all_goals simp

theorem pReg_value (L : Launch) (g : Nat) (d : D) : ∀ s j : Fin 4,
    valueOf L g d (pReg s j) = .pred (accumulates d.q s.val j.val) := by
  intro s j
  fin_cases s <;> fin_cases j <;> simp only [pReg] <;> mma_values <;> simp [accumulates]

/-- **The MMA thread's MMAs.** The MMA at slot `s`, K step `j`, is the MMA of slot `s`'s A tile
of the thread's warp and B tile, K step `j`, over the cluster's CTA pair (`InputRing.mmaSpec`). -/
theorem mma_event (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {ins : Instr}
    {o : Option TState} (s j : Fin 4) (hs : d.site = .mma s j) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    e = ⟨d.site.pc, .tc (.mma (256 * (d.w % 2))
      (InputRing.mmaSpec L (g / L.block) d.w s.val j.val) (accumulates d.q s.val j.val)
      (List.replicate 8 0))⟩ := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  rw [hs] at hc hf ⊢
  rw [code_mma_regs s j] at hc
  obtain rfl := Option.some.inj hc
  have hF := h.2.2.2.2
  have hlive : ∀ r, r ∈ Flow.live (Site.mma s j).pc → r ∈ Flow.live d.site.pc := by
    intro r hr; rw [hs]; exact hr
  obtain ⟨l1, l2, l3⟩ := fixed_live s j
  replace l1 := hlive _ l1
  replace l2 := hlive _ l2
  replace l3 := hlive _ l3
  have hd : t.regs 861 = some (b32 (256 * (d.w % 2))) :=
    (reg_at hF l1).trans (congrArg some (by mma_values))
  have hI : t.regs 862 = some (b32 272629776) :=
    (reg_at hF l2).trans (congrArg some (by mma_values))
  have hZ : t.regs 863 = some (b32 0) := (reg_at hF l3).trans (congrArg some (by mma_values))
  have hpv := pReg_value L g d s j
  have hp : t.regs (pReg s j) = some (.pred (accumulates d.q s.val j.val)) :=
    (reg_at hF (hlive _ (pReg_live s j))).trans (congrArg some hpv)
  have hA : t.regs (aReg s j) = some (b64 (descC +
      (L.sharedBase + InputRing.stageOff s.val (d.w % 2)) / 16 + 2 * j.val)) :=
    (reg_at hF (hlive _ (aReg_live s j))).trans (congrArg some (by
      rw [aReg_value, aDesc_units L hal]))
  have hB : t.regs (bReg s j) = some (b64 (descC +
      (L.sharedBase + InputRing.stageOff s.val 2) / 16 + 2 * j.val)) :=
    (reg_at hF (hlive _ (bReg_live s j))).trans (congrArg some (by
      rw [bReg_value, bDesc_units L hal]))
  have hsa : (L.sharedBase + InputRing.stageOff s.val (d.w % 2)) / 16 + 2 * j.val < 32768 := by
    have := InputRing.stageOff_lt s.isLt (show d.w % 2 < 3 by omega)
    omega
  have hsb : (L.sharedBase + InputRing.stageOff s.val 2) / 16 + 2 * j.val < 32768 := by
    have := InputRing.stageOff_lt s.isLt (show 2 < 3 by omega)
    omega
  have hda : 16 * ((L.sharedBase + InputRing.stageOff s.val (d.w % 2)) / 16) =
      L.sharedBase + InputRing.stageOff s.val (d.w % 2) := by
    unfold InputRing.stageOff; split_ifs <;> omega
  have hdb : 16 * ((L.sharedBase + InputRing.stageOff s.val 2) / 16) =
      L.sharedBase + InputRing.stageOff s.val 2 := by
    unfold InputRing.stageOff; split_ifs <;> omega
  rw [mma_tmpl hpre hg hd (by omega) hA hB hI hZ hp hsa hsb] at hf
  obtain ⟨rfl, -⟩ := hf
  simp only [InputRing.mmaSpec, hda, hdb]

end Mma

end

end PTX.Kernels.Fp16Gemm8192.Proof
