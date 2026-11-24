-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.UbCons
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad

@[expose] public section

/-! # No site of a consumer has an undefined-behaviour template

The consumer's sites, one by one (`Consumer.tmpl_ok`): the polls, arrivals and named barriers name
their barriers (the sites' event lemmas), the loads, stores and TMA stores are the epilogue's
(`Consumer.load_ok`, `store_ok`, `tma_ok`), and the remaining instructions are fences, waits,
cluster operations and the return. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

namespace Consumer

set_option maxHeartbeats 8000000 in
/-- **No site of a consumer has an undefined-behaviour template**, given the values its state
holds (`Held`). -/
theorem tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {ins : Instr} (hi : Inv d)
    (htid : tidOf L g < 256) (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins) (hh : Held d) (f : Fault) :
    eventTmpl Prod L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site with
  | clcWait => exact not_ub_of_fires (pc := Site.clcWait.pc) (fun f hf => by
      obtain ⟨_, _, _, _, -, he⟩ := clcWait_event hpre rfl hat.2.2.2.2 hc hf; cases he) f
  | clcLoad => exact not_ub_of_fires (pc := Site.clcLoad.pc) (fun f hf => by
      obtain ⟨_, _, he, -⟩ := clcLoad_read hpre rfl hat hc hf; cases he) f
  | clcBar => exact not_ub_of_fires (pc := Site.clcBar.pc) (fun f hf => by
      cases clcBar_event hpre hat hc hf rfl) f
  | ack => exact not_ub_of_fires (pc := Site.ack.pc) (fun f hf => by
      obtain ⟨_, _, _, _, he⟩ := ack_arrive hpre hg rfl hat.2.2.2.2 hc hf; cases he) f
  | accWait => exact not_ub_of_fires (pc := Site.accWait.pc) (fun f hf => by
      obtain ⟨_, _, _, he⟩ := accWait_event hpre rfl hi hat.2.2.2.2 hc hf; cases he) f
  | accArrive => exact not_ub_of_fires (pc := Site.accArrive.pc) (fun f hf => by
      obtain ⟨_, _, he⟩ := accArrive_event hpre hg rfl hat.2.2.2.2 hc hf; cases he) f
  | barA k => exact not_ub_of_fires (pc := (Site.barA k).pc) (fun f hf => by
      cases out_bar_event hpre hat hc hf (.inl rfl)) f
  | barB k => exact not_ub_of_fires (pc := (Site.barB k).pc) (fun f hf => by
      cases out_bar_event hpre hat hc hf (.inr rfl)) f
  | load j => exact load_ok hpre htid rfl hat hc f
  | store k i el => exact store_ok hpre htid rfl hat hc f
  | tma k => exact tma_ok hpre hi htid rfl hat hc f
  | clcStatus =>
    obtain ⟨rr, hr⟩ := hh.1 rfl
    simp only at hr
    subst hr
    code_at hc
    subst hc
    exact query_ok (r := rr) ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by cons_values))) (.inl rfl) f
  | clcFirst =>
    obtain ⟨rr, hr, hs⟩ := hh.2.1 rfl
    simp only at hr
    subst hr
    code_at hc
    subst hc
    exact query_ok (r := rr) ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by cons_values))) (.inr hs) f
  | ldBase =>
    code_at hc
    subst hc
    exact ld_ok (reg_b32 hat.2.2.2.2 (by lit_mem) (by cons_values; rfl)) (by omega) (by omega)
      hat.2.1 f
  | dealloc =>
    obtain ⟨w, v, hv⟩ := hh.2.2 rfl
    simp only at hv
    subst hv
    code_at hc
    subst hc
    exact tcDealloc_ok (w := w) (x :=
      v) hb ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by cons_values))) (reg_b32 hat.2.2.2.2 (by lit_mem) (by cons_values)) f
  | loadWait j =>
    rw [code_wait j] at hc
    cases hc
    exact plainOk_tmpl hb rfl f
  | drain k | fence k | commit k =>
    fin_cases k
    all_goals
      code_at hc
      subst hc
      exact plainOk_tmpl hb rfl f
  | setMaxReg | clcFence | finalDrain | exitArrive | exitWait | relinquish | exit =>
    code_at hc
    subst hc
    exact plainOk_tmpl hb rfl f

end Consumer

end

end PTX.Kernels.Fp16Gemm8192.Proof
