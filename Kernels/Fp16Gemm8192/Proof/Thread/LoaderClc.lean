-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderLoop
public import Kernels.Fp16Gemm8192.Proof.Thread.Claims
public import Kernels.Fp16Gemm8192.Proof.Thread.Cluster
public import Lemmas.Flow.Pointer
public import Lemmas.Flow.Local
public import Lemmas.Flow.RoundTrip

@[expose] public section

/-! # The loader's handling of a CLC response

The read of the response, the status query, the first-CTA query and the fence. When the bytes
read are not a response after the code's move through two halves, the move or the query
faults and the thread is dead (`next` gives `none`, `Flow.response_step`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


theorem facts_set {L : Launch} {g pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt L g pc d, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

set_option maxHeartbeats 10000000 in
/-- The response read: a response value reaches the status query. -/
theorem step_clcLoad {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t u : TState} {e : Event} (_hpre : Pre P L mem0) (hs : d.site = .clcLoad) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t
      (.mem { kind := .load, space := some (.shared .cta), sem := .acquire,
              scope := some .cta, elem := .int .b 128, addr := ⟨.reg 814 32, 0⟩,
              dsts := [some 972] })) e (some u)) :
    (next L g d e = some none ∨
      ∃ d' t', next L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
          Inv d') ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) := by
  obtain ⟨s, m, n, q, cp, resp, x⟩ := d
  simp only at hs h hf ⊢
  subst hs
  obtain ⟨a, bs, rfl, rfl⟩ := fires_load rfl rfl hf
  have hr := Flow.response_step (K := kernel) (A := Prod) (L := L) (g := g) (bs := bs)
    (pc := Site.clcLoad.pc) (by decide) Flow.code_355 Flow.code_356 Flow.code_357 h.1 h.2.1
    h.2.2.1 h.2.2.2.1 prod_noUnpack128 prod_noPack128
  cases hq : Flow.responseOf bs with
  | none => exact .inr ⟨by simp [next, hq], hr.2 (Flow.responseOf_none.mp hq)⟩
  | some rr =>
    obtain ⟨t', hl, hpc, hsub, hacc, hf', hd, hframe⟩ := hr.1 rr (Flow.responseOf_some.mp hq)
    refine .inl (.inr ⟨⟨.clcStatus, m, n, q, cp, .clc rr, x⟩, t', by simp [next, hq], hl,
      ⟨by rw [hpc]; rfl, hsub, hacc, hf', ?_⟩, ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩)
    frame_fp h.2.2.2.2, hframe
    refine ⟨?_, trivial⟩
    rw [hd]
    simp only [valueOf, extra, List.lookup_cons, Nat.reduceBEq, Option.getD_some]

theorem resp_of {L : Launch} {g : Nat} {d : D} {t : TState} {r : ClcResponse}
    (h : At t d.site.pc (facts L g d)) (hlive : 973 ∈ Flow.live d.site.pc)
    (hr : readValue L g t 128 (.reg 973) = .ok (.clc r)) : d.resp = .clc r := by
  have hreg : t.regs 973 = some d.resp :=
    holds_mem h.2.2.2.2 (List.mem_map.mpr ⟨973, hlive, by simp only [valueOf, extra,
      List.lookup_cons, Nat.reduceBEq, Option.getD_some]⟩)
  simp only [readValue, readReg, hreg, pure, Except.pure] at hr
  exact Except.ok.inj hr

set_option maxHeartbeats 10000000 in
/-- The status query: a cancelling response reaches the first-CTA query, any other the fence. -/
theorem step_clcStatus {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t u : TState} {e : Event} (hpre : Pre P L mem0) (hs : d.site = .clcStatus) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t
      (.clcQuery .isCanceled 987 (.reg 973))) e (some u)) :
    ∃ d' t', next L g d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧ Inv d' :=
        by
  obtain ⟨s, m, n, q, cp, resp, x⟩ := d
  simp only at hs h hf ⊢
  subst hs
  obtain ⟨r, v, hr, hq, rfl, rfl⟩ := fires_clcQuery hf
  have hresp := resp_of (d := ⟨.clcStatus, m, n, q, cp, resp, x⟩) h
    (show 973 ∈ Flow.live Site.clcStatus.pc by table_decide) hr
  simp only at hresp
  subst hresp
  simp only [clcQueryValue] at hq
  cases hq
  have h1 := At.set (r := 987) (v := .pred r.firstCta.isSome) h
    (facts_set (show 987 ∉ Flow.live Site.clcStatus.pc by table_decide))
  have hix : Inv ⟨.clcFirst, m, n, q, cp, .clc r, none32⟩ :=
    ⟨hi.1, hi.2, hi.3, hi.4, hi.5, by show none32 < 2 ^ 32; decide⟩
  cases hc : r.firstCta with
  | some c =>
    rw [hc] at h1
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 3
        (PTX.next (setReg t 987 (.pred true))) = some t' ∧
        At t' Site.clcFirst.pc (facts L g ⟨.clcFirst, m, n, q, cp, .clc r, none32⟩) := by
      loader_seg h1 hpre
    refine ⟨⟨.clcFirst, m, n, q, cp, .clc r, none32⟩, t', ?_, run_rtg hr', ht', hix⟩
    simp [next, hc]
  | none =>
    rw [hc] at h1
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 4
        (PTX.next (setReg t 987 (.pred false))) = some t' ∧
        At t' Site.clcFence.pc (facts L g ⟨.clcFence, m, n, q, cp, .clc r, none32⟩) := by
      loader_seg h1 hpre
    refine ⟨⟨.clcFence, m, n, q, cp, .clc r, none32⟩, t', ?_, run_rtg hr', ht',
      ⟨hix.1, hix.2, hix.3, hix.4, hix.5, hix.6⟩⟩
    simp [next, hc]

set_option maxHeartbeats 10000000 in
/-- The first-CTA query records the claimed CTA and reaches the fence. -/
theorem step_clcFirst {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t u : TState} {e : Event} (hpre : Pre P L mem0) (hs : d.site = .clcFirst) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t
      (.clcQuery (.first .x) 815 (.reg 973))) e (some u)) :
    ∃ d' t', next L g d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧ Inv d' :=
        by
  obtain ⟨s, m, n, q, cp, resp, x⟩ := d
  simp only at hs h hf ⊢
  subst hs
  obtain ⟨r, v, hr, hq, rfl, rfl⟩ := fires_clcQuery hf
  have hresp := resp_of (d := ⟨.clcFirst, m, n, q, cp, resp, x⟩) h
    (show 973 ∈ Flow.live Site.clcFirst.pc by table_decide) hr
  simp only at hresp
  subst hresp
  obtain ⟨⟨cx, cy, cz⟩, hc⟩ : ∃ c, r.firstCta = some c := by
    cases hc : r.firstCta with
    | none => simp [clcQueryValue, hc] at hq
    | some c => exact ⟨c, rfl⟩
  simp only [clcQueryValue, hc, pure, Except.pure] at hq
  cases hq
  have hx : cx.toNat < 2 ^ 32 := cx.isLt
  -- the query overwrites `%r769`: drop its old value, record the new one, and read off the
  -- facts at the fence (no local step)
  have h0 : At t Site.clcFirst.pc (Flow.factsFrom ((Flow.live Site.clcFirst.pc).erase 815)
      (valueOf L g ⟨.clcFirst, m, n, q, cp, .clc r, x⟩)) :=
    At.mono h (Flow.holds_factsFrom_mono (live := Flow.live Site.clcFirst.pc) h.2.2.2.2
      (by table_decide))
  have h1 := At.set (r := 815) (v := .bits 32 (BitVec.ofNat 64 cx.toNat)) h0
    (not_mem_factsFrom (by table_decide))
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 0
      (PTX.next (setReg t 815 (.bits 32 (BitVec.ofNat 64 cx.toNat)))) = some t' ∧
      At t' Site.clcFence.pc (facts L g ⟨.clcFence, m, n, q, cp, .clc r, cx.toNat⟩) := by
    loader_seg h1 hpre
  refine ⟨⟨.clcFence, m, n, q, cp, .clc r, cx.toNat⟩, t', ?_, run_rtg hr', ht',
    ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hx⟩⟩
  simp [next, hc]

/-- The leader CTA's acknowledgement barrier, as `mapa` returns it. -/
abbrev ackPtr (L : Launch) (g : Nat) : Value :=
  .ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
      (BitVec.ofNat 64 (L.sharedBase + 128))

set_option maxHeartbeats 10000000 in
/-- The fence reaches the acknowledgement. -/
theorem step_clcFence {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t u : TState} {e : Event} (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .clcFence)
    (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t (.fence (.proxy (.async (some (.shared .cta))))))
      e (some u)) :
    ∃ d' t', next L g d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧ Inv d' :=
        by
  obtain ⟨s, m, n, q, cp, resp, x⟩ := d
  simp only at hs h hf ⊢
  subst hs
  have hadv : AdvancesOp (.fence (.proxy (.async (some (.shared .cta))))) := trivial
  obtain rfl := fires_next hadv hf
  have h1 := At.next h
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  -- two instructions, then the `mapa` of the acknowledgement barrier to the leader CTA
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 2 (PTX.next t) = some t1 ∧
      At t1 (Site.clcFence.pc + 3) (factsAt L g (Site.clcFence.pc + 3) ⟨.clcFence, m, n, q, cp,
        resp, x⟩) := by
    loader_seg h1 hpre
  have hl : ∀ r ∈ [817, 818], r ∈ Flow.live (Site.clcFence.pc + 3) := by table_decide
  have h771 := holds_mem ht1.2.2.2.2 (Flow.mem_factsFrom (val :=
    valueOf L g ⟨.clcFence, m, n, q, cp, resp, x⟩)
    (hl 817 (by simp)))
  have h772 := holds_mem ht1.2.2.2.2 (Flow.mem_factsFrom (val :=
    valueOf L g ⟨.clcFence, m, n, q, cp, resp, x⟩)
    (hl 818 (by simp)))
  simp only [valueOf, extra, List.lookup_cons, Nat.reduceBEq, Option.getD_some] at h771 h772
  have hr2 := Flow.run_mapa (K := kernel) (A := Prod) Flow.code_365 ht1
    (Flow.readSharedAddress_b32 hg (cta_lt hpre hg) (by omega) h771)
    (show readBits L g t1 32 (.reg 818) = .ok 0 by
      simp [readBits, readReg, h772, b32, truncBits, bind, Except.bind, pure, Except.pure])
    (map_zero hpre hg _)
    (hL := prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t1)
  have h2 := At.set (r := 819) (v := ackPtr L g) ht1 (facts_set (by table_decide))
  obtain ⟨t3, hr3, ht'⟩ : ∃ t3, run kernel Prod L g 2 (PTX.next (setReg t1 819 (ackPtr L g))) =
      some t3 ∧
      At t3 Site.ack.pc (facts L g ⟨.ack, m, n, q, cp, resp, x⟩) := by
    loader_seg h2 hpre
  have hr := run_comp (run_comp hr1 hr2) hr3
  refine ⟨⟨.ack, m, n, q, cp, resp, x⟩, t3, ?_, run_rtg hr, ht',
    ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
  simp [next]

set_option maxHeartbeats 40000000 in
/-- After the acknowledgement: no claimed CTA drains the slots; otherwise the claimed tile
(or the code's fallback tile) starts with the opposite CLC phase. -/
theorem step_ack {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .ack) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hadv : AdvancesOp ins.op)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    ∃ d' t', next L g d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧ Inv d' :=
        by
  obtain ⟨s, m, n, q, cp, resp, x⟩ := d
  simp only at hs h hf ⊢
  subst hs
  obtain rfl := fires_next hadv hf
  have hcp : cp < 2 := hi.cp
  have hx : x < 2 ^ 32 := hi.x
  have h1 := At.next h
  by_cases hnone : x = none32
  · -- no claimed CTA: the tests evaluate, and the code goes to the drain
    subst hnone
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 9 (PTX.next t) = some t' ∧
        At t' (Site.drain 0).pc (facts L g ⟨.drain 0, m, n, q, cp, resp, none32⟩) := by
      loader_seg h1 hpre
    refine ⟨⟨.drain 0, m, n, q, cp, resp, none32⟩, t', ?_, run_rtg hr, ht',
      ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
    simp [next]
  -- a claimed CTA: the test for it, then the branch at 370
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 1 (PTX.next t) = some t1 ∧
      At t1 Flow.bra_370 (factsAt L g Flow.bra_370 ⟨.ack, m, n, q, cp, resp, x⟩) := by
    loader_seg h1 hpre
  obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_370
    (decide (x = none32)) ht1 (holds_mem ht1.2.2.2.2 (Flow.mem_factsFrom (by table_decide)))
    (prod_localRule_bra L g _ _ _)
  rw [show decide (x = none32) = false by simp [hnone]] at ht2
  simp only [Bool.false_eq_true, ↓reduceIte] at ht2
  have hmn := claim_lt x
  -- the fallback tile, then the branch at 374 on whether the CTA is in the grid
  obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 3 t2 = some t3 ∧
      At t3 Flow.bra_374 (factsAt L g Flow.bra_374 ⟨.ack, 0, 0, q, cp, resp, x⟩) := by
    loader_seg ht2 hpre
  obtain ⟨t4, hr4, ht4⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_374
    (decide (x > 1023)) ht3 (holds_mem ht3.2.2.2.2 (Flow.mem_factsFrom (by table_decide)))
    (prod_localRule_bra L g _ _ _)
  -- both paths reach the continuation branch with the claimed tile and the flipped phase
  obtain ⟨k, t6, hr6, ht6⟩ : ∃ k t6, run kernel Prod L g k t4 = some t6 ∧
      At t6 Flow.bra_384 (factsAt L g Flow.bra_384 ⟨.ack, claimM x, claimN x, q, 1 - cp, resp,
        x⟩) := by
    by_cases hbig : x > 1023
    · rw [show decide (x > 1023) = true by simp [hbig]] at ht4
      simp only [↓reduceIte] at ht4
      have h0 : claimM x = 0 ∧ claimN x = 0 := by simp [claimM, claimN, hbig]
      rw [h0.1, h0.2]
      exact ⟨2, by loader_seg ht4 hpre [flip_bits cp hcp]⟩
    · rw [show decide (x > 1023) = false by simp [hbig]] at ht4
      simp only [Bool.false_eq_true, ↓reduceIte] at ht4
      have hx' : x < 1024 := by omega
      simp only [claimM, claimN, hbig, ↓reduceIte]
      exact ⟨9, by loader_seg ht4 hpre [claim_bits x hx', flip_bits cp hcp]⟩
  obtain ⟨t7, hr7, ht7⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_384
    (decide (x ≠ none32)) ht6 (holds_mem ht6.2.2.2.2 (Flow.mem_factsFrom (by table_decide)))
    (prod_localRule_bra L g _ _ _)
  rw [show decide (x ≠ none32) = true by simp [hnone]] at ht7
  simp only [↓reduceIte] at ht7
  obtain ⟨t8, hr8, ht8⟩ : ∃ t8, run kernel Prod L g 8 t7 = some t8 ∧
      At t8 (Site.wait 0).pc (facts L g ⟨.wait 0, claimM x, claimN x, 0, 1 - cp, resp, x⟩) := by
    loader_seg ht7 hpre [row_bits (claimM x) hmn.1]
  refine ⟨⟨.wait 0, claimM x, claimN x, 0, 1 - cp, resp, x⟩, t8, ?_,
    run_rtg (run_comp (run_comp (run_comp (run_comp hr1 hr2) (run_comp hr3 hr4)) hr6)
      (run_comp hr7 hr8)),
    ht8, ⟨hmn.1, hmn.2, by show 0 < 128; omega, by show 0 % 8 = 0; rfl, by show 1 - cp < 2; omega,
      hx⟩⟩
  simp [next, hnone]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
