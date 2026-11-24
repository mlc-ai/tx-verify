-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderLoop

@[expose] public section

/-! # The loader's poll of a slot's empty barrier -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-- The full-barrier pointer of blocks 1-3, computed from block 0's by an offset. -/
def ptrReg : Fin 8 → Nat
  | 1 => 770 | 2 => 790 | 3 => 810 | _ => 0

set_option maxHeartbeats 10000000 in
/-- Blocks 1-3 compute their full-barrier pointer by offsetting a shared pointer, whose bound
evaluation cannot decide; the segment is split at that instruction. -/
theorem wait_seg_ptr {P : Params} {L : Launch} {mem0 : Mem0} {g m n q cp x : Nat} {r : Value}
    {t : TState} (hpre : Pre P L mem0) (b : Fin 8) (hb : 1 ≤ b.val ∧ b.val ≤ 3)
    (hm : m < 16) (hq : q < 128)
    (h1 : At (PTX.next (setReg t (waitPred b) (.pred true))) ((Site.wait b).pc + 1)
      ((waitPred b, .pred true) :: facts L g ⟨.wait b, m, n, q, cp, r, x⟩)) :
    ∃ k t', run kernel Prod L g k (PTX.next (setReg t (waitPred b) (.pred true))) = some t' ∧
      At t' (Site.load b 0).pc (facts L g ⟨.load b 0, m, n, q, cp, r, x⟩) := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1,
    run kernel Prod L g 5 (PTX.next (setReg t (waitPred b) (.pred true))) =
      some t1 ∧ At t1 ((Site.wait b).pc + 7) (factsAt L g ((Site.wait b).pc + 7) ⟨.load b 0, m, n,
        q, cp, r, x⟩) := by
    obtain ⟨b, hb'⟩ := b
    simp only at hb
    obtain ⟨hb1, hb3⟩ := hb
    interval_cases b <;> loader_seg h1 hpre
  have hl : ∀ b : Fin 8, 1 ≤ b.val ∧ b.val ≤ 3 →
      750 ∈ Flow.live ((Site.wait b).pc + 7) ∧ ptrReg b ∉ Flow.live ((Site.wait b).pc + 7) := by
    table_decide
  have hv : valueOf L g ⟨.load b 0, m, n, q, cp, r, x⟩ 750 =
      .ptr 32 false (.shared (g / L.block) (2 *
        ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 8)) := by
    loader_values
  have hptr := hv ▸ Flow.mem_factsFrom (val :=
    valueOf L g ⟨.load b 0, m, n, q, cp, r, x⟩) (hl b hb).1
  have hc : kernel.code[(Site.wait b).pc + 7]? =
      some ⟨none, .int ⟨.add, .int .s 32, false, [some (ptrReg b)],
        [.reg 750, .imm ((8 * b.val : Nat) : Int)]⟩⟩ := by
    obtain ⟨b, hb'⟩ := b
    simp only at hb
    obtain ⟨hb1, hb3⟩ := hb
    interval_cases b
    · exact Flow.code_156
    · exact Flow.code_185
    · exact Flow.code_214
  have hr2 := run_add_sharedPtr (K := kernel) (A := Prod) (L := L) (g := g) hc ht1 hptr (by
    omega) (by omega) (hL := prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t1)
  have ht2 := At.set (r := ptrReg b)
    (v := .ptr 32 false (.shared (g / L.block) (2 *
    ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 8 + 8 * b.val)))
    ht1 (fun p hp he => (hl b hb).2 (he ▸ (by
      simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
      obtain ⟨r', hr', rfl⟩ := hp
      exact hr')))
  obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 1 (PTX.next (setReg t1 (ptrReg b)
      (.ptr 32 false (.shared (g / L.block) (2 *
        ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 8 + 8 * b.val))))) =
      some t3 ∧ At t3 (Site.load b 0).pc (facts L g ⟨.load b 0, m, n, q, cp, r, x⟩) := by
    obtain ⟨b, hb'⟩ := b
    simp only at hb
    obtain ⟨hb1, hb3⟩ := hb
    interval_cases b <;> loader_seg ht2 hpre
  exact ⟨5 + 1 + 1, t3, run_comp (run_comp hr1 hr2) hr3, ht3⟩

set_option maxHeartbeats 10000000 in
/-- A poll of block `b`: a failed poll returns to it, a successful one reaches the first load. -/
theorem step_wait {P : Params} {L : Launch} {mem0 : Mem0} {g m n q cp x : Nat} {r : Value}
    {t u : TState} {e : Event} {base par : Nat} (hpre : Pre P L mem0) (b : Fin 8)
    (hi : Inv ⟨.wait b, m, n, q, cp, r, x⟩)
    (h : At t (Site.wait b).pc (facts L g ⟨.wait b, m, n, q, cp, r, x⟩))
    (hf : Fires (Site.wait b).pc
      (eventTmpl Prod L g t (.mbarWait (waitPred b) base 0 (.reg par) true .cta)) e (some u)) :
    ∃ d' t', next L g ⟨.wait b, m, n, q, cp, r, x⟩ e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
        Inv d' := by
  have hm : m < 16 := hi.m
  have hn : n < 32 := hi.n
  have hq : q < 128 := hi.q
  rw [← h.1] at hf
  obtain ⟨mb, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := waitPred b) (v := .pred ok) h (not_live (waitPred_not_live b))
  cases ok with
  | false =>
    obtain ⟨t', hr, ht'⟩ : ∃ t',
      run kernel Prod L g 2 (PTX.next (setReg t (waitPred b) (.pred false))) =
        some t' ∧ At t' (Site.wait b).pc (facts L g ⟨.wait b, m, n, q, cp, r, x⟩) := by
      fin_cases b <;> loader_seg h1 hpre
    exact ⟨_, t', rfl, run_rtg hr, ht', hi⟩
  | true =>
    by_cases hb : 1 ≤ b.val ∧ b.val ≤ 3
    · obtain ⟨k, t', hr, ht'⟩ := wait_seg_ptr hpre b hb hm hq h1
      exact ⟨_, t', rfl, run_rtg hr, ht', ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
    · obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g (toLoads b)
          (PTX.next (setReg t (waitPred b) (.pred true))) = some t' ∧
          At t' (Site.load b 0).pc (facts L g ⟨.load b 0, m, n, q, cp, r, x⟩) := by
        fin_cases b <;> first | (simp at hb; done) | loader_seg h1 hpre
      exact ⟨_, t', rfl, run_rtg hr, ht', ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
