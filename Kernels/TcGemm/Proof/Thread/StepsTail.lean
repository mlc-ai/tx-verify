-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Thread.Steps

@[expose] public section

/-! # `tc_gemm`: the steps after the read

Each site from the poll of `bar0` on as a step of the abstract machine. Thread 0's successful
poll of `bar0` computes the MMA's descriptors; the MMA and the commit continue to `bar1`'s poll.
A successful poll of `bar1` reaches the fence and the computation of the row's Tensor Memory
address; the load writes the eight words; the row's address follows its wait; each element store
continues to the next element, the last to the fences and the barrier; warp 0 then frees the
columns and every thread exits. -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {g : Nat}

section
variable (hpre : Pre L A B D a b mem0) (hg : g < L.threads) {c : Nat} {vals : List Value}
  {t u : TState} {e : Event} {ins : Instr}
include hpre hg

omit hpre hg in
/-- Thread 0's poll of `bar0`: a failed poll polls again, a successful one computes the MMA's
operands. -/
theorem step_wait0 (hpre : Pre L A B D a b mem0) (hg : g < L.threads)
    (h : (code L A B D g).AtD ⟨.wait0, c, vals⟩ t) (hi : Inv g ⟨.wait0, c, vals⟩)
    (hc : kernel.code[Site.wait0.pc]? = some ins)
    (hf : Fires Site.wait0.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.wait0, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_0)
  obtain rfl := hi.zero rfl
  rw [tmpl_wait0 hpre hg (tc_reg h.2.2.2.2)] at hf
  obtain ⟨ok, rfl, hu⟩ := hf
  cases hu
  have h1 := At.set (r := 3) (v := .pred ok) (at_of rfl h)
    (not_mem_factsFrom (show 3 ∉ liveAt .wait0 by decide +kernel))
  have hcol : c < 2 ^ 16 := hi.col
  cases ok
  · obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] L 0 1 _ = some t' ∧
        At t' Site.wait0.pc (facts L A B D 0 ⟨.wait0, c, vals⟩) := by tc_seg h1 hpre
    exact step_to (d' := ⟨.wait0, c, vals⟩) (by simp [next]) (run_rtg hr) (atD_of rfl ht')
      (by inv_tac hi)
  · obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] L 0 12 _ = some t' ∧
        At t' Site.mma.pc (facts L A B D 0 ⟨.mma, c, vals⟩) := by tc_seg h1 hpre
    exact step_to (d' := ⟨.mma, c, vals⟩) (by simp [next]) (run_rtg hr) (atD_of rfl ht')
      (by inv_tac hi)

theorem step_mma (h : (code L A B D g).AtD ⟨.mma, c, vals⟩ t) (hi : Inv g ⟨.mma, c, vals⟩)
    (hc : kernel.code[Site.mma.pc]? = some ins)
    (hf : Fires Site.mma.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.mma, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_0)
  obtain rfl := hi.zero rfl
  have h4 : t.regs 4 = some (.pred false) := by
    rw [reg_at h.2.2.2.2 (by table_decide)]; tc_values; rfl
  change Fires Site.mma.pc (eventTmpl [] L 0 t (.tcMma (.dense .one false .i8 14 (.smem (.reg 42))
    (.reg 44) (.reg 19) [.reg 30, .reg 30, .reg 30, .reg 30] (.reg 4)))) e (some u) at hf
  rw [tmpl_mma hpre hg hi.col (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2)
    (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2) h4] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl

theorem step_commit (h : (code L A B D g).AtD ⟨.commit, c, vals⟩ t) (hi : Inv g ⟨.commit, c, vals⟩)
    (hc : kernel.code[Site.commit.pc]? = some ins)
    (hf : Fires Site.commit.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.commit, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_0)
  rw [tmpl_commit hpre hg (tc_reg h.2.2.2.2)] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl

/-- The poll of `bar1`: a failed poll polls again, a successful one reaches the fence. -/
theorem step_wait1 (h : (code L A B D g).AtD ⟨.wait1, c, vals⟩ t) (hi : Inv g ⟨.wait1, c, vals⟩)
    (hc : kernel.code[Site.wait1.pc]? = some ins)
    (hf : Fires Site.wait1.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.wait1, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_1)
  rw [tmpl_wait1 hpre hg (tc_reg h.2.2.2.2)] at hf
  obtain ⟨ok, rfl, hu⟩ := hf
  cases hu
  have h1 := At.set (r := 5) (v := .pred ok) (at_of rfl h)
    (not_mem_factsFrom (show 5 ∉ liveAt .wait1 by decide +kernel))
  cases ok
  · obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] L g 1 _ = some t' ∧
        At t' Site.wait1.pc (facts L A B D g ⟨.wait1, c, vals⟩) := by tc_seg h1 hpre
    exact step_to (d' := ⟨.wait1, c, vals⟩) (by simp [next]) (run_rtg hr) (atD_of rfl ht')
      (by inv_tac hi)
  · obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] L g 1 _ = some t' ∧
        At t' Site.fence1.pc (facts L A B D g ⟨.fence1, c, vals⟩) := by tc_seg h1 hpre
    exact step_to (d' := ⟨.fence1, c, vals⟩) (by simp [next]) (run_rtg hr) (atD_of rfl ht')
      (by inv_tac hi)

/-- The fence after the poll; the row's Tensor Memory address follows. -/
theorem step_fence1 (h : (code L A B D g).AtD ⟨.fence1, c, vals⟩ t) (hi : Inv g ⟨.fence1, c, vals⟩)
    (hc : kernel.code[Site.fence1.pc]? = some ins)
    (hf : Fires Site.fence1.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.fence1, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_0)
  rw [tmpl_fenceAfter] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  have hcol : c < 2 ^ 16 := hi.col
  have hg' := lt_block hpre hg
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] L g 2 (PTX.next t) = some t' ∧
      At t' Site.ld.pc (facts L A B D g ⟨.ld, c, vals⟩) := by
    have h1 := At.next (at_of rfl h)
    tc_seg h1 hpre [taddr]
  exact step_to (d' := ⟨.ld, c, vals⟩) (by simp [next]) (run_rtg hr) (atD_of rfl ht')
    (by inv_tac hi)

/-- The load of the row writes the eight loaded words. -/
theorem step_ld (h : (code L A B D g).AtD ⟨.ld, c, vals⟩ t) (hi : Inv g ⟨.ld, c, vals⟩)
    (hc : kernel.code[Site.ld.pc]? = some ins)
    (hf : Fires Site.ld.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.ld, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemLoad_0)
  rw [tmpl_ld hpre hg hi.col (tc_reg h.2.2.2.2)] at hf
  obtain ⟨vs, hl, rfl, hu⟩ := hf
  cases hu
  have h1 : t.regs 1 = some (valueOf L A B D g ⟨.ld, c, vals⟩ 1) := reg_at h.2.2.2.2
    (by table_decide)
  have h7 : t.regs 7 = some (valueOf L A B D g ⟨.ld, c, vals⟩ 7) := reg_at h.2.2.2.2
    (by table_decide)
  have h14 : t.regs 14 = some (valueOf L A B D g ⟨.ld, c, vals⟩ 14) :=
    reg_at h.2.2.2.2 (by table_decide)
  have hpc : t.pc = Flow.tmemLoad_0 := h.1
  match vs, hl with
  | [v0, v1, v2, v3, v4, v5, v6, v7], _ =>
    refine step_to (d' := ⟨.waitLd, c, [v0, v1, v2, v3, v4, v5, v6, v7]⟩) (by simp [next]) .refl
      ⟨by simp only [setRegs, setReg, PTX.next]; rw [hpc]; rfl,
        by simp only [setRegs, setReg, PTX.next]; exact h.2.1,
        by simp only [setRegs, setReg, PTX.next]; exact h.2.2.1,
        by simp only [setRegs, setReg, PTX.next]; exact h.2.2.2.1, ?_⟩ (by inv_tac hi)
    show Holds _ (Flow.factsFrom (Flow.live Flow.tmemWait_0) _)
    rw [show Flow.live Flow.tmemWait_0 = [1, 7, 14, 22, 23, 24, 25, 26, 27, 28, 29] by
      decide +kernel]
    simp only [Flow.factsFrom, List.map, Holds, setRegs, setReg, PTX.next, Function.update_apply,
      Nat.reduceEqDiff, ↓reduceIte, h1, h7, h14]
    tc_values
    simp [word]

/-- The wait for the load; the row's global address follows. -/
theorem step_waitLd (h : (code L A B D g).AtD ⟨.waitLd, c, vals⟩ t) (hi : Inv g ⟨.waitLd, c, vals⟩)
    (hc : kernel.code[Site.waitLd.pc]? = some ins)
    (hf : Fires Site.waitLd.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.waitLd, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_0)
  rw [tmpl_waitLd hpre] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  have hg' := lt_block hpre hg
  have hrD := hpre.rangeD
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] (explicitParams L (ps A B D)) g 4 (PTX.next t) =
      some t' ∧ At t' (Site.st 0).pc (facts L A B D g ⟨.st 0, c, vals⟩) := by
    have h1 := At.next (at_of rfl h)
    tc_seg h1 hpre [explicitParams]
  rw [params hpre] at hr
  exact step_to (d' := ⟨.st 0, c, vals⟩) (by simp [next]) (run_rtg hr) (atD_of rfl ht')
    (by inv_tac hi)

end

/-! ### The element stores -/

section
variable {c : Nat} {vals : List Value} {t : TState}

/-- The words of a store's vector are live there. -/
theorem st_regs {j : Nat} (hj : j < 8) (h : Holds t.regs (facts L A B D g ⟨.st j, c, vals⟩)) :
    ∀ i < 8, (j < 4 → i < 4) → (4 ≤ j → 4 ≤ i) → t.regs (22 + i) = some (word vals i) := by
  intro i hi h1 h2
  have hl : 22 + i ∈ liveAt (.st j) := by
    show 22 + i ∈ Flow.live (Site.st j).pc
    by_cases hj4 : j < 4
    · simp only [Site.pc, hj4, ↓reduceIte]
      have := h1 hj4
      interval_cases i <;> table_decide
    · simp only [Site.pc, hj4, ↓reduceIte]
      have := h2 (by omega)
      interval_cases i <;> table_decide
  rw [reg_at h hl]
  interval_cases i <;> tc_values

theorem st_47 {j : Nat} (h : Holds t.regs (facts L A B D g ⟨.st j, c, vals⟩)) :
    t.regs 47 = some (b64 (D + 32 * g)) := by
  have hl : 47 ∈ liveAt (.st j) := by
    show 47 ∈ Flow.live (Site.st j).pc
    by_cases hj4 : j < 4 <;> simp only [Site.pc, hj4, ↓reduceIte] <;> table_decide
  rw [reg_at h hl]; tc_values

/-- The next element of the same vector store. -/
theorem atD_st_succ {j : Nat} (hj : j % 4 < 3) (h : (code L A B D g).AtD ⟨.st j, c, vals⟩ t) :
    (code L A B D g).AtD ⟨.st (j + 1), c, vals⟩ { t with sub := t.sub + 1 } := by
  have hpc : (Site.st (j + 1)).pc = (Site.st j).pc := by
    simp only [Site.pc]; split_ifs <;> first | rfl | omega
  have hs : t.sub = j % 4 := h.2.1
  refine ⟨h.1.trans hpc.symm, show t.sub + 1 = (j + 1) % 4 by omega, h.2.2.1, h.2.2.2.1, ?_⟩
  show Holds t.regs
    (Flow.factsFrom (Flow.live (Site.st (j + 1)).pc) (valueOf L A B D g ⟨.st j, c, vals⟩))
  rw [hpc]
  exact h.2.2.2.2

end

section
variable (hpre : Pre L A B D a b mem0) (hg : g < L.threads) {c : Nat} {vals : List Value}
  {t u : TState} {e : Event} {ins : Instr}
include hpre hg

/-- An element store: the next element, after the last of the first vector the second vector,
after the last the fence. -/
theorem step_st {j : Nat} (h : (code L A B D g).AtD ⟨.st j, c, vals⟩ t)
    (hi : Inv g ⟨.st j, c, vals⟩) (hc : kernel.code[(Site.st j).pc]? = some ins)
    (hf : Fires (Site.st j).pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.st j, c, vals⟩ u e := by
  have hj := hi.st j rfl
  have hins : ins.op = if j < 4 then storeLo else storeHi := by
    by_cases hj4 : j < 4
    · simp only [Site.pc, hj4, ↓reduceIte] at hc ⊢
      rw [Option.some.inj (hc.symm.trans Flow.code_store_0)]
    · simp only [Site.pc, hj4, ↓reduceIte] at hc ⊢
      rw [Option.some.inj (hc.symm.trans Flow.code_store_1)]
  rw [hins, tmpl_st hpre hg hj h.2.1 (st_47 h.2.2.2.2) (st_regs hj h.2.2.2.2)] at hf
  cases hv : storeValue 32 (word vals j) with
  | ok v' =>
    simp only [hv] at hf
    obtain ⟨rfl, hu⟩ := hf
    cases hu
    have hs : t.sub = j % 4 := h.2.1
    have hlen : (if j < 4 then [Opnd.reg 22, .reg 23, .reg 24, .reg 25]
        else [Opnd.reg 26, .reg 27, .reg 28, .reg 29]).length = 4 := by split <;> rfl
    unfold afterStore
    rw [hlen, hs]
    by_cases h3 : j % 4 < 3
    · rw [ite_eq_left (by omega)]
      exact step_to (d' := ⟨.st (j + 1), c, vals⟩) (by simp [next]; omega) .refl
        (by rw [← hs]; exact atD_st_succ h3 h) (by inv_tac hi; omega)
    · rw [ite_eq_right (by omega)]
      obtain rfl | rfl : j = 3 ∨ j = 7 := by omega
      · exact step_to (d' := ⟨.st 4, c, vals⟩) (by simp [next]) .refl
          ⟨show t.pc + 1 = _ by rw [h.1]; rfl, rfl, h.2.2.1, h.2.2.2.1,
            Flow.holds_factsFrom_mono h.2.2.2.2 (by table_decide)⟩ (by inv_tac hi)
      · exact step_to (d' := ⟨.fenceB, c, vals⟩) (by simp [next]) .refl
          ⟨show t.pc + 1 = _ by rw [h.1]; rfl, rfl, h.2.2.1, h.2.2.2.1,
            Flow.holds_factsFrom_mono h.2.2.2.2 (by table_decide)⟩ (by inv_tac hi)
  | error f =>
    simp only [hv] at hf
    exact absurd hf.2 (by simp)

omit hpre hg in
theorem step_fenceB (h : (code L A B D g).AtD ⟨.fenceB, c, vals⟩ t) (hi : Inv g ⟨.fenceB, c, vals⟩)
    (hc : kernel.code[Site.fenceB.pc]? = some ins)
    (hf : Fires Site.fenceB.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.fenceB, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_1)
  rw [tmpl_fenceBefore] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl

omit hpre hg in
theorem step_bar1 (h : (code L A B D g).AtD ⟨.bar1, c, vals⟩ t) (hi : Inv g ⟨.bar1, c, vals⟩)
    (hc : kernel.code[Site.bar1.pc]? = some ins)
    (hf : Fires Site.bar1.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.bar1, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
  rw [tmpl_bar] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl

omit hpre hg in
/-- The fence after the second barrier: warp 0 goes on to free the columns, every other warp to
the exit. -/
theorem step_fence2 (h : (code L A B D g).AtD ⟨.fence2, c, vals⟩ t) (hi : Inv g ⟨.fence2, c, vals⟩)
    (hc : kernel.code[Site.fence2.pc]? = some ins)
    (hf : Fires Site.fence2.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.fence2, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_2)
  rw [tmpl_fenceAfter] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  have h57 := At.next (at_of rfl h)
  have h1 : (PTX.next t).regs 1 = some (.pred (decide (g / 32 ≠ 0))) := by
    show t.regs 1 = _
    rw [reg_at h.2.2.2.2 (by table_decide)]; tc_values
  obtain ⟨v, hv, hatv⟩ := run_bra (K := kernel) (A := []) (L := L) (g := g) Flow.code_57 _ h57 h1
    (fun _ h => by cases h)
  by_cases hw : g / 32 = 0
  · simp only [hw, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hatv
    exact step_to (d' := ⟨.dealloc, c, vals⟩) (by simp [next, hw]) (run_rtg hv)
      (atD_of rfl (At.mono hatv (Flow.holds_factsFrom_mono hatv.2.2.2.2 (by table_decide))))
      (by inv_tac hi)
  · simp only [hw, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hatv
    exact step_to (d' := ⟨.exit, c, vals⟩) (by simp [next, hw]) (run_rtg hv)
      (atD_of rfl (At.mono hatv (Flow.holds_factsFrom_mono hatv.2.2.2.2 (by table_decide))))
      (by inv_tac hi)

omit hg in
theorem step_dealloc (h : (code L A B D g).AtD ⟨.dealloc, c, vals⟩ t)
    (hi : Inv g ⟨.dealloc, c, vals⟩) (hc : kernel.code[Site.dealloc.pc]? = some ins)
    (hf : Fires Site.dealloc.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.dealloc, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
  rw [tmpl_dealloc hpre hi.col (tc_reg h.2.2.2.2)] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl

end

end
end PTX.Kernels.TcGemm.Proof
