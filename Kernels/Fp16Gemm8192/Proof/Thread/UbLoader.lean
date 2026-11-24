-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.InputIssues
public import Kernels.Fp16Gemm8192.Proof.Thread.AccessAddr
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcQuery
public import Lemmas.Flow.UbStop

@[expose] public section

/-! # The loader's sites are not undefined behaviour

At every site of the loader, the instruction's event is not undefined behaviour: its operands
evaluate to the barriers, buffers, map and coordinates of the site (`Loader.tmpl_ok`). The loads
use the A or B map through its parameter, a 1024-aligned stage of the CTA and the slot's full
barrier of the leader CTA (`Loader.copy_ok`); the queries hold a response, a cancelling one for
the first-CTA query (`QueryResp`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- A box of two-byte elements at coordinates `(x1, x2)` with `x1` a multiple of 8 below
`2 ^ 31` starts on a 16-byte boundary. -/
theorem boxAligned_coords {d : TensorDescriptor.Descriptor 1} (hf : d.format.bytes = 2)
    {x1 x2 : Nat} (hx1 : x1 % 8 = 0) (hx1' : x1 < 2 ^ 31) :
    TensorDescriptor.BoxAligned d (fun axis => (BitVec.ofNat 32
      ([truncBits 32 (BitVec.ofNat 64 x1), truncBits 32 (BitVec.ofNat 64 x2)].getD axis.val
        0).toNat).toInt) := by
  have h0 : (BitVec.ofNat 32 x1).toInt = x1 := by
    rw [BitVec.toInt_ofNat', Int.bmod_def]
    have h1 : ((x1 : Int) % (2 ^ 32 : Nat)) = x1 := by
      rw [Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
    push_cast at h1 ⊢
    rw [h1]
    split_ifs <;> omega
  simp only [TensorDescriptor.BoxAligned, List.getD_cons_zero, Fin.val_zero, truncBits,
    BitVec.toNat_ofNat]
  simp only [Nat.mod_eq_of_lt (show x1 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x1 < 2 ^ 32 by omega), h0, hf]
  omega

/-- A tile load of the A or B map, through its parameter, into a 128-aligned shared address of the
CTA, completing on a barrier of the cluster's leader CTA: the copy of the map's box at the
coordinates' origin. -/
theorem copy_tmpl (hpre : Pre P L mem0) (hg : g < L.threads) {dst mb r c1 c2 : Nat}
    {name : String} (hr0 : t.regs r = some (.ptr 64 true (.param name) 0))
    (hn : name = "gemm_kernel_param_0" ∨ name = "gemm_kernel_param_1")
    {st a x1 x2 : Nat} (hd : t.regs dst = some (b32 st)) (hst : st < 2 ^ 32) (h128 : st % 128 = 0)
    (hmb : t.regs mb = some (.ptr 32 false (.shared (g / L.block) (2 *
      (g / L.block / 2))) (BitVec.ofNat 64 a)))
    (ha : a < 2 ^ 32) (h8 : a % 8 = 0)
    (hc1 : t.regs c1 = some (b32 x1)) (hc2 : t.regs c2 = some (b32 x2)) (hx1 : x1 % 8 = 0)
    (hx1' : x1 < 2 ^ 31) :
    ∃ M base cls, L.tensorMaps M = some ⟨1, Fp16Gemm8192.mapA base cls⟩ ∧
      eventTmpl Prod L g t (.cpTensor true true dst 0 (.reg r) [.reg c1, .reg c2] mb 0 none .tile) =
        .tensorIssue M ⟨⟨1, Fp16Gemm8192.mapA base cls, fun axis => (BitVec.ofNat 32
          ([truncBits 32 (BitVec.ofNat 64 x1), truncBits 32 (BitVec.ofNat 64 x2)].getD axis.val
            0).toNat).toInt, ⟨.shared, g / L.block, st⟩, none⟩,
          ⟨.shared, 2 * (g / L.block / 2), a⟩, true, .two⟩ (PTX.next t) := by
  obtain ⟨M, base, cls, hpar, h1, h2, hD, hal⟩ : ∃ M base cls,
      L.paramObjects name = some (mapParam name, M) ∧ M % 128 = 0 ∧ M + 128 ≤ 2 ^ 64 ∧
      L.tensorMaps M = some ⟨1, Fp16Gemm8192.mapA base cls⟩ ∧ base % 16 = 0 := by
    rcases hn with rfl | rfl
    · exact ⟨_, _, _, hpre.paramA, hpre.mapAlignment.1, hpre.mapRange.1, hpre.mapA,
        hpre.inputAlignment.1⟩
    · exact ⟨_, _, _, hpre.paramB, hpre.mapAlignment.2.1, hpre.mapRange.2.1, hpre.mapB,
        hpre.inputAlignment.2.1⟩
  have hcta : g / L.block < L.grid := by
    have := hpre.block
    simp only [Launch.threads] at hg
    rw [this] at hg ⊢
    omega
  have hgrid := hpre.grid
  have hcl := hpre.cluster
  have hm : tensorMap L g t (.reg r) [.reg c1, .reg c2] .tile =
      .ok (M, ⟨1, Fp16Gemm8192.mapA base cls⟩) := by
    have h64 : M % 64 = 0 := by omega
    have h2' : M ≤ 18446744073709551488 := by omega
    simp [tensorMap, tensorMapAddress, readValue, readReg, hr0, hpar, mapParam,
      ParamObjectDecl.bytes, h1, h2', h64, hD, Fp16Gemm8192.mapA_valid hal, TensorMode.coordinates,
      bind, Except.bind, pure, Except.pure]
  have hdl : sharedEffAddr L g t true dst 0 = .ok ⟨.shared, g / L.block, st⟩ := by
    have h64 : st < 18446744073709551616 := by omega
    have h32 : st < 4294967296 := hst
    simp [sharedEffAddr, readReg, hd, b32, readBits, truncBits, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32, bind, Except.bind, pure, Except.pure]
  have hml := mbarClusterLoc_ptr (L := L) (g := g) hmb hg (by omega)
    (by simp only [clusterOfCta_eq hpre]; omega) ha h8
  refine ⟨M, base, cls, hD, cpTensor_tmpl hm hdl h128 hml (vs := [truncBits 32 (BitVec.ofNat 64 x1),
    truncBits 32 (BitVec.ofNat 64 x2)]) ?_ ?_ ?_⟩
  · simp [readBits, readReg, hc1, hc2, b32, bind, Except.bind, pure, Except.pure]
  · exact boxAligned_coords (by simp [Fp16Gemm8192.mapA, encodeTiled]; rfl) hx1 hx1'
  · simp only [TensorRoute, CtaInCluster, SameCtaGroup, Launch.ctaGroupRanks,
      clusterOfCta_eq hpre, rankOfCta_eq hpre, hgrid, CtaGroup.size]
    refine ⟨Launch.oneDimLaunch_clusterGridValid hpre.oneDimLaunch, ?_⟩
    and_intros <;> first | decide | omega | (intro h; cases h) | simp

/-- A tile load of the A or B map, through its parameter, into a 128-aligned shared address of the
CTA, completing on a barrier of the cluster's leader CTA, is not undefined behaviour. -/
theorem copy_ok (hpre : Pre P L mem0) (hg : g < L.threads) {dst mb r c1 c2 : Nat}
    {name : String} (hr0 : t.regs r = some (.ptr 64 true (.param name) 0))
    (hn : name = "gemm_kernel_param_0" ∨ name = "gemm_kernel_param_1")
    {st a x1 x2 : Nat} (hd : t.regs dst = some (b32 st)) (hst : st < 2 ^ 32) (h128 : st % 128 = 0)
    (hmb : t.regs mb = some (.ptr 32 false (.shared (g / L.block) (2 *
      (g / L.block / 2))) (BitVec.ofNat 64 a)))
    (ha : a < 2 ^ 32) (h8 : a % 8 = 0)
    (hc1 : t.regs c1 = some (b32 x1)) (hc2 : t.regs c2 = some (b32 x2)) (hx1 : x1 % 8 = 0)
    (hx1' : x1 < 2 ^ 31) (f : Fault) :
    eventTmpl Prod L g t (.cpTensor true true dst 0 (.reg r) [.reg c1, .reg c2] mb 0 none .tile) ≠
      .ub f := by
  obtain ⟨M, base, cls, -, h⟩ := copy_tmpl hpre hg hr0 hn hd hst h128 hmb ha h8 hc1 hc2 hx1 hx1'
  rw [h]
  simp

/-- A register of a state's facts holding a 32-bit integer. -/
theorem reg_b32 {live : List Nat} {val : Nat → Value} {r : Nat} {x : Nat}
    (h : Holds t.regs (Flow.factsFrom live val)) (hl : r ∈ live) (hv : val r = b32 x) :
    t.regs r = some (b32 x) :=
  (reg_at h hl).trans (congrArg some hv)

namespace Loader

/-- The response a state holds at its queries: any response at the status query, a cancelling
one at the first-CTA query. -/
def QueryResp (d : D) : Prop :=
  (d.site = .clcStatus → ∃ r, d.resp = .clc r) ∧
    (d.site = .clcFirst → ∃ r, d.resp = .clc r ∧ r.firstCta.isSome)

set_option maxHeartbeats 8000000 in
/-- The loader's loads are not undefined behaviour. -/
theorem load_ok (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {ins : Instr} (hi : Inv d)
    (b : Fin 8) (j : Fin 3) (hs : d.site = .load b j) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) : eventTmpl Prod L g t ins.op ≠ .ub f :=
      by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hq := hi.q
  have hq8 := hi.q8
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hq hq8 ⊢
  subst hs
  fin_cases b <;> fin_cases j
  all_goals
    code_at hc
    subst hc
    refine copy_ok hpre hg ((reg_at h.2.2.2.2 (by lit_mem)).trans
      (congrArg some (by loader_values; rfl)))
      (by simp) (reg_b32 h.2.2.2.2 (by lit_mem) (by loader_values; rfl)) (by omega) (by omega)
      ((reg_at h.2.2.2.2 (by lit_mem)).trans (congrArg some (by loader_values; rfl)))
      (by omega) (by omega) (reg_b32 h.2.2.2.2 (by lit_mem) (by loader_values; rfl))
      (reg_b32 h.2.2.2.2 (by lit_mem) (by loader_values; rfl)) (by omega) (by omega) f

set_option maxHeartbeats 4000000 in
/-- **No site of the loader has an undefined-behaviour template**, given the response its
queries hold. -/
theorem tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {ins : Instr} (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hq : QueryResp d) (f : Fault) : eventTmpl Prod L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  cases site with
  | wait b => exact not_ub_of_fires (pc := (Site.wait b).pc) (fun f hf => by
      obtain ⟨_, _, _, he⟩ := wait_event hpre b rfl h hc hf; cases he) f
  | load b j => exact load_ok hpre hg hi b j rfl h hc f
  | arrive b => exact not_ub_of_fires (pc := (Site.arrive b).pc) (fun f hf => by
      obtain ⟨_, _, he⟩ := arrive_event hpre hg b rfl h hc hf; cases he) f
  | clcWait => exact not_ub_of_fires (pc := Site.clcWait.pc) (fun f hf => by
      obtain ⟨_, _, _, _, -, he⟩ := clcWait_event hpre rfl h hc hf; cases he) f
  | drain i => exact not_ub_of_fires (pc := (Site.drain i).pc) (fun f hf => by
      obtain ⟨_, _, _, he⟩ := drain_event hpre i rfl h hc hf; cases he) f
  | clcLoad => exact not_ub_of_fires (pc := Site.clcLoad.pc) (fun f hf => by
      obtain ⟨_, _, he, -⟩ := clcLoad_read hpre rfl h hc hf; cases he) f
  | ack => exact not_ub_of_fires (pc := Site.ack.pc) (fun f hf => by
      obtain ⟨_, _, _, _, he⟩ := ack_event hpre hg rfl h hc hf; cases he) f
  | clcStatus =>
    obtain ⟨rr, hr⟩ := hq.1 rfl
    simp only at hr
    subst hr
    code_at hc
    subst hc
    exact query_ok (r := rr) ((holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by loader_values))) (.inl rfl) f
  | clcFirst =>
    obtain ⟨rr, hr, hs⟩ := hq.2 rfl
    simp only at hr
    subst hr
    code_at hc
    subst hc
    exact query_ok (r := rr) ((holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by loader_values))) (.inr hs) f
  | clcFence | exitArrive | exitWait | exit =>
    code_at hc
    subst hc
    exact plainOk_tmpl hb rfl f

end Loader

end

end PTX.Kernels.Fp16Gemm8192.Proof
