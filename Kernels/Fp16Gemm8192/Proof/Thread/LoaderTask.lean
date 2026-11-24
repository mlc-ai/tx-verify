-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderLoop

@[expose] public section

/-! # The loader at the end of a task

The CLC response poll, its read, the two queries, the fence and the acknowledgement; then
either the next task's first block or the drain of the four empty slots, and the common
exit. The branches after the acknowledgement depend on the claimed first CTA `x`; each is
evaluated by splitting the segment at the branch. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


/-- The predicate written by each poll at the end of a task. -/
def taskPred : Site → Nat
  | .clcWait => 986
  | .drain 0 => 990 | .drain 1 => 991 | .drain 2 => 992
  | .drain 3 => 993
  | _ => 0

theorem code_drain : ∀ i : Fin 4, ∃ base par, kernel.code[(Site.drain i).pc]? =
    some ⟨none, .mbarWait (taskPred (.drain i)) base 0 (.reg par) true .cta⟩
  | 0 => ⟨_, _, Flow.code_mbarWait_9⟩
  | 1 => ⟨_, _, Flow.code_mbarWait_10⟩
  | 2 => ⟨_, _, Flow.code_mbarWait_11⟩
  | 3 => ⟨_, _, Flow.code_mbarWait_12⟩

theorem code_taskWait (s : Site) (hs : s = .clcWait ∨ ∃ i, s = .drain i) :
    ∃ base par, kernel.code[s.pc]? = some ⟨none,
      .mbarWait (taskPred s) base 0 (.reg par) true .cta⟩ := by
  rcases hs with rfl | ⟨i, rfl⟩
  · exact ⟨_, _, Flow.code_mbarWait_8⟩
  · exact code_drain i

theorem taskPred_not_live (s : Site) (hs : s = .clcWait ∨ ∃ i, s = .drain i) :
    taskPred s ∉ Flow.live s.pc := by
  rcases hs with rfl | ⟨i, rfl⟩
  · table_decide
  · revert i
    table_decide

set_option maxHeartbeats 10000000 in
/-- A poll at the end of a task: retry, or continue to the read (CLC) or the next slot. -/
theorem step_taskWait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t u : TState} {e : Event} {base par : Nat} (hpre : Pre P L mem0)
    (hs : d.site = .clcWait ∨ ∃ i, d.site = .drain i) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc
      (eventTmpl Prod L g t (.mbarWait (taskPred d.site) base 0 (.reg par) true .cta)) e (some u)) :
    ∃ d' t', next L g d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
        Inv d' := by
  obtain ⟨s, m, n, q, cp, r, x⟩ := d
  simp only at hs h hf ⊢
  rw [← h.1] at hf
  obtain ⟨mb, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := taskPred s) (v := .pred ok) h (not_live (taskPred_not_live s hs))
  rcases hs with rfl | ⟨i, rfl⟩
  · cases ok with
    | false =>
      obtain ⟨t', hr, ht'⟩ : ∃ t',
        run kernel Prod L g 2 (PTX.next (setReg t (taskPred .clcWait) (.pred false))) =
          some t' ∧ At t' Site.clcWait.pc (facts L g ⟨.clcWait, m, n, q, cp, r, x⟩) := by
        loader_seg h1 hpre
      refine ⟨⟨.clcWait, m, n, q, cp, r, x⟩, t', ?_, run_rtg hr, ht',
        ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
      simp [next]
    | true =>
      obtain ⟨t', hr, ht'⟩ : ∃ t',
        run kernel Prod L g 2 (PTX.next (setReg t (taskPred .clcWait) (.pred true))) =
          some t' ∧ At t' Site.clcLoad.pc (facts L g ⟨.clcLoad, m, n, q, cp, r, x⟩) := by
        loader_seg h1 hpre
      refine ⟨⟨.clcLoad, m, n, q, cp, r, x⟩, t', ?_, run_rtg hr, ht',
        ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
      simp [next]
  · cases ok with
    | false =>
      obtain ⟨t', hr, ht'⟩ : ∃ t',
        run kernel Prod L g 2 (PTX.next (setReg t (taskPred (.drain i)) (.pred false))) =
          some t' ∧ At t' (Site.drain i).pc (facts L g ⟨.drain i, m, n, q, cp, r, x⟩) := by
        fin_cases i <;> loader_seg h1 hpre
      refine ⟨⟨.drain i, m, n, q, cp, r, x⟩, t', ?_, run_rtg hr, ht',
        ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
      simp [next]
    | true =>
      by_cases hl : i.val + 1 < 4
      · obtain ⟨t', hr, ht'⟩ : ∃ t',
        run kernel Prod L g 2 (PTX.next (setReg t (taskPred (.drain i)) (.pred true))) =
            some t' ∧ At t' (Site.drain ⟨i.val + 1, hl⟩).pc
              (facts L g ⟨.drain ⟨i.val + 1, hl⟩, m, n, q, cp, r, x⟩) := by
          fin_cases i <;> first | (simp at hl; done) | loader_seg h1 hpre
        refine ⟨⟨.drain ⟨i.val + 1, hl⟩, m, n, q, cp, r, x⟩, t', ?_, run_rtg hr, ht',
          ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
        simp [next, hl]
      · have hi3 : i = 3 := Fin.ext (by show i.val = 3; omega)
        subst hi3
        obtain ⟨t', hr, ht'⟩ : ∃ t',
          run kernel Prod L g 3 (PTX.next (setReg t (taskPred (.drain 3)) (.pred true))) =
            some t' ∧ At t' Site.exitArrive.pc (facts L g ⟨.exitArrive, m, n, q, cp, r, x⟩) := by
          loader_seg h1 hpre
        refine ⟨⟨.exitArrive, m, n, q, cp, r, x⟩, t', ?_, run_rtg hr, ht',
          ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
        simp [next]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
