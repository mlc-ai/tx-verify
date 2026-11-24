-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.UbLoader
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcCount
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaDiscipline

@[expose] public section

/-! # The MMA thread's sites are not undefined behaviour

At every site of the MMA thread, the instruction's event is not undefined behaviour
(`Mma.tmpl_ok`): the election uses the full mask, the polls, arrivals, MMAs and commits name their
barriers and operands (the sites' event lemmas), and the queries hold a response, a cancelling one
for the first-CTA query (`Mma.QueryResp`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

namespace Mma

/-- The response a state holds at its queries: any response at the status query, a cancelling
one at the first-CTA query. -/
def QueryResp (d : D) : Prop :=
  (d.site = .clcStatus → ∃ r, d.resp = .clc r) ∧
    (d.site = .clcFirst → ∃ r, d.resp = .clc r ∧ r.firstCta.isSome)

set_option maxHeartbeats 4000000 in
/-- **No site of the MMA thread has an undefined-behaviour template**, given the response its
queries hold. -/
theorem tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {ins : Instr} (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hq : QueryResp d) (f : Fault) : eventTmpl Prod L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  cases site with
  | elect =>
    code_at hc
    subst hc
    exact elect_ok ((holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by mma_values))) f
  | clcWait => exact not_ub_of_fires (pc := Site.clcWait.pc) (fun f hf => by
      obtain ⟨_, _, _, _, -, he⟩ := clcWait_event hpre rfl h hc hf; cases he) f
  | clcLoad => exact not_ub_of_fires (pc := Site.clcLoad.pc) (fun f hf => by
      obtain ⟨_, _, he, -⟩ := clcLoad_read hpre rfl h hc hf; cases he) f
  | ack => exact not_ub_of_fires (pc := Site.ack.pc) (fun f hf => by
      obtain ⟨_, _, _, _, he⟩ := ack_arrive hpre hg rfl h hc hf; cases he) f
  | accWait => exact not_ub_of_fires (pc := Site.accWait.pc) (fun f hf => by
      obtain ⟨_, _, _, he⟩ := accWait_event hpre rfl hi h hc hf; cases he) f
  | full s => exact not_ub_of_fires (pc := (Site.full s).pc) (fun f hf => by
      obtain ⟨_, _, _, he⟩ := full_event hpre s rfl hi h hc hf; cases he) f
  | mma s j => exact not_ub_of_fires (pc := (Site.mma s j).pc) (fun f hf => by
      cases mma_event hpre hg s j rfl h hc hf) f
  | commit s => exact not_ub_of_fires (pc := (Site.commit s).pc) (fun f hf => by
      cases commit_event hpre hg s rfl h hc hf) f
  | accCommit => exact not_ub_of_fires (pc := Site.accCommit.pc) (fun f hf => by
      cases accCommit_spec hpre hg rfl h hc hf) f
  | clcStatus =>
    obtain ⟨rr, hr⟩ := hq.1 rfl
    simp only at hr
    subst hr
    code_at hc
    subst hc
    exact query_ok (r := rr) ((holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by mma_values))) (.inl rfl) f
  | clcFirst =>
    obtain ⟨rr, hr, hs⟩ := hq.2 rfl
    simp only at hr
    subst hr
    code_at hc
    subst hc
    exact query_ok (r := rr) ((holds_mem h.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by mma_values))) (.inr hs) f
  | clcFence | exitArrive | exitWait | exit =>
    code_at hc
    subst hc
    exact plainOk_tmpl hb rfl f

end Mma

end

end PTX.Kernels.Fp16Gemm8192.Proof
