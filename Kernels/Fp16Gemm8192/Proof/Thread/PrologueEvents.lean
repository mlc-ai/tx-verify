-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueSteps
public import Lemmas.Flow.Alloc

@[expose] public section

/-! # The prologue's events

For each prologue site: the event's effect on the thread and the local code to the next
site. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


/-- The obligation of one prologue event: a pending fault, or local steps to a concrete
state of the successor. -/
abbrev Step (L : Launch) (g : Nat) (d : D) (u : TState) (e : Event) : Prop :=
  next L g d e = some none ∨ ∃ d' t', next L g d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ Good L g d' t'

theorem at_set2 {t : TState} {pc : Nat} {F : List (Nat × Value)} {r1 r2 : Nat}
    {v1 v2 : Value} (h : At t pc F) (h1 : ∀ p ∈ F, p.1 ≠ r1)
    (h2 : ∀ p ∈ (r1, v1) :: F, p.1 ≠ r2) :
    At (PTX.next (setReg (setReg t r1 v1) r2 v2)) (pc + 1) ((r2, v2) :: (r1, v1) :: F) :=
  At.set ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, Function.update_self .., holds_update h.2.2.2.2 h1⟩ h2

theorem good_after {L : Launch} {g : Nat} {w : Nat} (hw : w < 12) {t : TState}
    (h : At t (afterElect L g w).pc (facts L g ⟨afterElect L g w, w⟩)) :
    Good L g (.inl ⟨afterElect L g w, w⟩) t :=
  good_of_at (by unfold afterElect afterInits; split_ifs <;> simp) h ⟨hw⟩

set_option maxHeartbeats 10000000 in
/-- The shuffle: a warp index of the block is followed to the election (warp 0) or to the
test for thread 0. -/
theorem step_shfl {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .shfl)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s, w0⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := some 1) hf
  simp only [Option.elim]
  cases recv
  case bits wd v =>
    by_cases hv : wd = 32 ∧ v.toNat < 12
    · obtain ⟨rfl, hv⟩ := hv
      right
      obtain ⟨w, hw⟩ : ∃ w, v.toNat = w := ⟨_, rfl⟩
      have hrecv : Value.bits 32 v = b32 w := by rw [← hw]; simp [b32]
      have hw12 : w < 12 := hw ▸ hv
      have hn : next L g ⟨.shfl, w0⟩ ⟨Site.shfl.pc, .shfl .idx av bv cv (.bits 32 v) ok⟩ =
          some (some (.inl ⟨if w = 0 then .elect else afterElect L g w, w⟩)) := by
        simp [next, hw, hw12]
      rw [hrecv] at hn ⊢
      have h1 := at_set2 (r1 := 48) (v1 := b32 w) (r2 := 1) (v2 := .pred ok) h
        (not_mem_factsFrom (live := Flow.live Site.shfl.pc) (by table_decide))
        (ne_cons (by decide) (not_mem_factsFrom (live := Flow.live Site.shfl.pc) (by table_decide)))
      obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 1
          (PTX.next (setReg (setReg t 48 (b32 w)) 1 (.pred ok))) = some t1 ∧
          At t1 Flow.bra_7 (factsAt L g Flow.bra_7 ⟨.shfl, w⟩) := by
        pro_seg h1 hpre
      obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_7
        (decide (w ≠ 0)) ht1 (reg_val ht1 (r := 2) (by table_decide) (by pro_values))
        (prod_localRule_bra L g _ _ _)
      by_cases hw0 : w = 0
      · subst hw0
        rw [show decide ((0 : Nat) ≠ 0) = false from rfl] at ht2
        simp only [Bool.false_eq_true, ↓reduceIte] at ht2
        obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 2 t2 = some t3 ∧
            At t3 Site.elect.pc (facts L g ⟨.elect, 0⟩) := by
          pro_seg ht2 hpre
        refine ⟨.inl ⟨.elect, 0⟩, t3, by simpa using hn, run_rtg (run_comp hr1 (run_comp hr2 hr3)),
          good_of_at (by simp) ht3 ⟨by omega⟩⟩
      · rw [show decide (w ≠ 0) = true by simp [hw0]] at ht2
        simp only [↓reduceIte] at ht2
        have ht2' : At t2 (Site.elect.pc + 10) (factsAt L g (Site.elect.pc + 10) ⟨.shfl, w⟩) :=
          At.mono ht2 (Flow.holds_factsFrom_mono ht2.2.2.2.2 (by table_decide))
        obtain ⟨k, t3, hr3, ht3⟩ := from_tid hpre hg ⟨hw12⟩ ht2'
        refine ⟨.inl ⟨afterElect L g w, w⟩, t3, by simpa [hw0] using hn,
          run_rtg (run_comp hr1 (run_comp hr2 hr3)), good_after hw12 ht3⟩
    · left
      simp [next, hv]
  all_goals left; simp [next]

set_option maxHeartbeats 10000000 in
/-- The election in warp 0: the leader prefetches the three tensor maps; every lane then
goes to the test for thread 0. -/
theorem step_elect {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .elect)
    (hi : Inv d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s, w⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0)
  obtain ⟨mk, inst, leader, rfl, rfl⟩ := fires_elect hf
  simp only [Option.elim]
  right
  have h1 := At.set (r := 976) (v := .pred (laneOf L g == leader)) h
    (not_mem_factsFrom (live := Flow.live Site.elect.pc) (by table_decide))
  have hmap : ∀ name base, L.paramObjects name = some (mapParam name, base) → base % 128 = 0 →
      base + 128 ≤ 2 ^ 64 → (mapParam name).name = name ∧ 0 < (mapParam name).bytes ∧
        0 < (mapParam name).alignment ∧ base % (mapParam name).alignment = 0 ∧
        base + (mapParam name).bytes ≤ 2 ^ 64 := by
    intro name base _ h128 hr
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [mapParam, ParamObjectDecl.bytes] <;> omega
  obtain ⟨k, t3, hr3, ht3⟩ : ∃ k t3, run kernel Prod L g k
      (PTX.next (setReg t 976 (.pred (laneOf L g == leader)))) = some t3 ∧
      At t3 (Site.elect.pc + 10) (factsAt L g (Site.elect.pc + 10) ⟨.elect, w⟩) := by
    cases hb : (laneOf L g == leader)
    · rw [hb] at h1
      exact ⟨3, by pro_seg h1 hpre⟩
    · rw [hb] at h1
      obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel Prod L g 4
          (PTX.next (setReg t 976 (.pred true))) = some t4 ∧
          At t4 (Site.elect.pc + 5) (factsAt L g (Site.elect.pc + 5) ⟨.elect, w⟩) := by
        pro_seg h1 hpre
      have hA := run_local (A := Prod) (L := L) (g :=
        g) Flow.code_15 rfl ht4 (exec_prefetchTensorMap
        (reg_val ht4 (r := 899) (by table_decide) (by pro_values)) (.inr rfl)
        hpre.paramA (hmap _ _ hpre.paramA hpre.mapAlignment.1 hpre.mapRange.1)
        (prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t4))
      obtain ⟨t5, hr5, ht5⟩ : ∃ t5, run kernel Prod L g 1 (PTX.next t4) = some t5 ∧
          At t5 (Site.elect.pc + 7) (factsAt L g (Site.elect.pc + 7) ⟨.elect, w⟩) := by
        pro_seg (At.next ht4) hpre
      have hB := run_local (A := Prod) (L := L) (g :=
        g) Flow.code_17 rfl ht5 (exec_prefetchTensorMap
        (reg_val ht5 (r := 900) (by table_decide) (by pro_values)) (.inr rfl)
        hpre.paramB (hmap _ _ hpre.paramB hpre.mapAlignment.2.1 hpre.mapRange.2.1)
        (prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t5))
      obtain ⟨t6, hr6, ht6⟩ : ∃ t6, run kernel Prod L g 1 (PTX.next t5) = some t6 ∧
          At t6 (Site.elect.pc + 9) (factsAt L g (Site.elect.pc + 9) ⟨.elect, w⟩) := by
        pro_seg (At.next ht5) hpre
      have hC := run_local (A := Prod) (L := L) (g :=
        g) Flow.code_19 rfl ht6 (exec_prefetchTensorMap
        (reg_val ht6 (r := 901) (by table_decide) (by pro_values)) (.inr rfl)
        hpre.paramD (hmap _ _ hpre.paramD hpre.mapAlignment.2.2 hpre.mapRange.2.2)
        (prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t6))
      exact ⟨_, _, run_comp (run_comp (run_comp (run_comp (run_comp hr4 hA) hr5) hB) hr6) hC,
        At.mono (At.next ht6) (Flow.holds_factsFrom_mono ht6.2.2.2.2 (by table_decide))⟩
  obtain ⟨k', t4, hr4, ht4⟩ := from_tid hpre hg hi ht3
  refine ⟨.inl ⟨afterElect L g w, w⟩, t4, ?_, run_rtg (run_comp hr3 hr4), ?_⟩
  · simp [next]
  · exact good_of_at (by unfold afterElect afterInits; split_ifs <;> simp) ht4 ⟨hi.w⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Prologue
