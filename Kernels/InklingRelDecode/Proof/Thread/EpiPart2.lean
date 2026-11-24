-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiWait

@[expose] public section

/-! # After the poll: the zero test, the zero pairs and the `num_iters` branch

After the always-executed poll of `o_final` (pc 2565, with its poll branch at pc 2566) the code
runs 33 local instructions to the branch on `%p173` (`num_iters < 1`) at pc 2600 (bridge part 2):

* `mov.b64 %rd531, {%r1299, %r1299}` (pc 2567): the zero pair;
* `setp.equ.f32 %p178, %r1454, 0f0` (pc 2568): the zero test of the row sum (`Prm.eq0`), which
  faults only where `Prm.setpOk` is false;
* the 31 copies `mov.b64 %rd532 ... %rd562, %rd531` (pcs 2569-2599) of the pair;
* `@%p173 bra 2674` (pc 2600): to the first store site of the `num_iters < 1` path (the stores
  of the zero pair), else on to the selection and reciprocal of pcs 2601-2602.

During the run `%rd531 ... %rd562` (the product registers, `valueOf` of the table) hold the zero
pair `zpair`, not a product: `valueP` is the table with those registers valued `zpair`, and
`facts2 pc d` the facts of that table. `p2_run` is the run of the whole part (under `Prm.setpOk`;
without it the thread is dead at `setp`). `valueP_sk` brings the run's table back to the
state's for `num_iters < 1` (`sk`: the products are the zero pair); at pc 2601 no product register
is live. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The zero pair `(0, 0)` that `mov.b64 %rd531, {%r1299, %r1299}` writes and the moves copy. -/
abbrev zpair : Value := .bits 64 (truncBits 32 0#64 ||| truncBits 32 0#64 <<< 32)

theorem zpair_eq : zpair = joinValue zero32 zero32 := rfl

/-- The table of the run: the product registers `%rd531 ... %rd562` hold the zero pair. -/
def valueP (d : D) (r : Nat) : Value := if 2479 ≤ r ∧ r < 2511 then zpair else valueOf d r

/-- The facts of the run at a pc: the registers live there, valued by `valueP`. -/
def facts2 (pc : Nat) (d : D) : List (Nat × Value) := Flow.factsFrom (Flow.live pc) (valueP d)

theorem valueP_of_not {d : D} {r : Nat} (h : ¬ (2479 ≤ r ∧ r < 2511)) :
    valueP d r = valueOf d r := by
  unfold valueP
  split_ifs
  rfl

theorem facts2_ne {pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ facts2 pc d, p.1 ≠ r := by
  intro p hp he
  simp only [facts2, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

/-- The value-table reduction used after evaluating a segment of the run. -/
macro "p2_values" : tactic =>
  `(tactic| simp only [valueP, valueOf, D.scalars, PTX.Flow.lookupLit, Option.getD_some,
    Option.getD_none, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, and_self, and_false,
    false_and, ↓reduceIte])

/-- Evaluate a segment of the run from `h` and close the facts of its end state. -/
syntax "p2_seg " term:max : tactic
macro_rules
  | `(tactic| p2_seg $h) =>
    `(tactic| (
      seg_fp $h using
        try p2_values
        all_goals seg_close [zpair_eq]
        all_goals rfl))

/-! ### The facts at the ends -/

theorem live2567_free : ∀ r ∈ Flow.live 2567, ¬ (2479 ≤ r ∧ r < 2511) := by decide +kernel

theorem live2567_sub : ∀ r ∈ Flow.live 2567, r ∈ Flow.live 2565 := by decide +kernel

/-- The facts of the state at the poll (pc 2565) give those of the run at pc 2567: no product
register is live there. -/
theorem facts2_of_wait (d : D) {R : Nat → Option Value} (h : Holds R (factsAt 2565 d)) :
    Holds R (facts2 2567 d) := by
  refine Flow.holds_of_pointwise fun r hr => ?_
  have h1 := reg_of h (live2567_sub r hr)
  rw [h1]
  rw [valueP_of_not (live2567_free r hr)]

/-- With `num_iters < 1` the products are the zero pair: the run's table is the state's. -/
theorem valueP_sk (d : D) (hsk : d.sk = true) : valueP d = valueOf d := by
  funext r
  unfold valueP
  split_ifs with h
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 32 ∧ r = 2479 + k := ⟨r - 2479, by omega, by omega⟩
    rw [valueOf_prod d hk]
    simp only [D.prod, hsk, ite_true]
    exact zpair_eq
  · rfl

/-! ### The run -/

theorem seg_p2_mov0 (d : D) : Seg kernel asms L g 1 2567 (facts2 2567 d) 2568 (facts2 2568 d) := by
  intro t h
  p2_seg h

theorem live_ne_setp : ∀ r ∈ Flow.live 2569, r = 178 ∨ (r ≠ 178 ∧ r ∈ Flow.live 2568) := by
  decide +kernel

theorem code_setp : kernel.code[2568]? = some ⟨none, .float
    { setpI (.unord .eq) false with dsts := [some 178], srcs := [.reg 1915, .f32imm 0] }⟩ :=
  Flow.code_2568

/-- **`setp.equ.f32 %p178, %r1454, 0f0`** (pc 2568), under the condition that it does not
fault. -/
theorem seg_p2_setp (d : D) :
    SegD kernel asms L g 1 2568 (facts2 2568 d) 2569 (facts2 2569 d) (d.pr.setpOk = true) := by
  have key : ∀ t, At t 2568 (facts2 2568 d) →
      execLocalA asms L g t (.float
        { setpI (.unord .eq) false with dsts := [some 178], srcs := [.reg 1915, .f32imm 0] }) =
      ((setpE (.unord .eq) false d.pr.l zero32).map Value.pred).map fun x =>
        PTX.next (setReg t 178 x) := by
    intro t h
    have hpc : 2563 ≤ t.pc := by have := h.1; omega
    have h1 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueP d)
      (show 1915 ∈ Flow.live 2568 by decide +kernel))
    have h1' : t.regs 1915 = some d.pr.l := by
      rw [h1]
      p2_values
    have e := exec_setpE (L := L) (g := g) (c := .unord .eq) (cmp := .eq) (fz := false) (p := 178)
      (idealAt (Or.inr rfl) hpc) (declineAt (Or.inr rfl) hpc) (Or.inr rfl) rfl rfl
      (OpndIs.reg h1') (OpndIs.imm (b := 0))
    rw [e]
    show (setpE (.unord .eq) false d.pr.l zero32).map _ = _
    cases setpE (.unord .eq) false d.pr.l zero32 <;> rfl
  refine SegD.iff (SegD.one (E := (setpE (.unord .eq) false d.pr.l zero32).map Value.pred)
    (d := 178) code_setp rfl key (fun x hx _ => ?_) live_ne_setp) ?_
  · show valueP d 178 = x
    have hv : valueP d 178 = .pred d.pr.eq0 := rfl
    rw [hv]
    cases hs : setpE (.unord .eq) false d.pr.l zero32 with
    | error f => rw [hs] at hx; cases hx
    | ok b =>
      rw [hs] at hx
      cases hx
      simp [Prm.eq0, hs]
  · simp only [Prm.setpOk]
    cases setpE (.unord .eq) false d.pr.l zero32 <;> simp [Except.toBool, Except.map]

theorem seg_p2_movs_a (d : D) :
    Seg kernel asms L g 10 2569 (facts2 2569 d) 2579 (facts2 2579 d) := by
  intro t h
  p2_seg h

theorem seg_p2_movs_b (d : D) :
    Seg kernel asms L g 10 2579 (facts2 2579 d) 2589 (facts2 2589 d) := by
  intro t h
  p2_seg h

theorem seg_p2_movs_c (d : D) :
    Seg kernel asms L g 11 2589 (facts2 2589 d) 2600 (facts2 2600 d) := by
  intro t h
  p2_seg h

/-- **The 31 copies of the zero pair** (pcs 2569-2599). -/
theorem seg_p2_movs (d : D) :
    Seg kernel asms L g 31 2569 (facts2 2569 d) 2600 (facts2 2600 d) :=
  ((seg_p2_movs_a d).comp (seg_p2_movs_b d)).comp (seg_p2_movs_c d)

/-- **The branch on `num_iters < 1`** (pc 2600). -/
theorem seg_p2_bra (d : D) :
    Seg kernel asms L g 1 2600 (facts2 2600 d) (if d.sk then 2674 else 2601) (facts2 2600 d) :=
  Seg.bra (p := 173) (pick := d.sk) Flow.code_2600
    (by
      have := Flow.mem_factsFrom (val := valueP d) (show 173 ∈ Flow.live 2600 by decide +kernel)
      exact this)
    (fun _ _ => asms_bra) (segFree (by omega))

/-- **Part 2 up to the branch** (pcs 2567-2599): 33 local steps, dead where the zero test
faults. -/
theorem p2_run (d : D) :
    SegD kernel asms L g 33 2567 (facts2 2567 d) 2600 (facts2 2600 d) (d.pr.setpOk = true) := by
  have s1 := SegD.seg_comp (seg_p2_mov0 (L := L) (g := g) d) (seg_p2_setp d)
  have s2 := SegD.comp_seg s1 (seg_p2_movs d)
  exact SegD.of_len s2 rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
