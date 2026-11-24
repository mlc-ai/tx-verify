-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiMul

@[expose] public section

/-! # The poll of `o_final` and the reciprocal of the row sum

After a successful poll of the `o_final` barrier (pc 2565) and the local code of pcs 2567-2600
(`EpiPart2`) the code selects `1.0` where the row sum is zero (`selp.f32`, pc 2601) and takes the
reciprocal (`rcp.approx.ftz.f32`, pc 2602). A failed poll polls again. The reciprocal faults on
an operand the assumption declines and the Core rule rejects; then the thread is dead
(`wait_ok_steps`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {t u : TState} {e : Event} {ins : Instr}

/-- A register live at `pc` has the table's value. -/
theorem reg_of {R : Nat → Option Value} {pc r : Nat} {d : D} (h : Holds R (factsAt pc d))
    (hl : r ∈ Flow.live pc) : R r = some (valueOf d r) :=
  holds_mem h (Flow.mem_factsFrom hl)

/-- A branch `@!p` on the fact `p = pick`: taken when `p` is false. -/
theorem run_nbra {t : TState} {pc target p : Nat} {F : List (Nat × Value)} {uni : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, true), .bra target uni⟩) (pick : Bool)
    (h : At t pc F) (hp : t.regs p = some (.pred pick))
    (hL : ∀ a ∈ asms, a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc asms pc) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (if pick then pc + 1 else target) F := by
  cases pick with
  | true =>
    refine ⟨skip t, ?_, by simp [skip, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩
    simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind,
      pure, Except.pure]
  | false =>
    refine ⟨{t with pc := target}, ?_, rfl, h.2⟩
    simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind, pure,
      Except.pure, hA.exec, execLocalRule_of_none hL, execLocal, Op.rule, execBranch, Op.isLocal]

theorem asms_bra {t : TState} {target : Nat} {uni : Bool} :
    ∀ a ∈ asms, a.localRule L g t (.bra target uni) = none :=
  asms_none (by simp) (by simp)

/-- An unconditional branch: one local step to its target, and the facts hold there. -/
theorem run_bra' {pc target : Nat} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .bra target true⟩) (h : At t pc F)
    (hA : Assumption.SegFreePc asms pc := by seg_free) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u target F := by
  refine ⟨{ t with pc := target }, ?_, rfl, h.2⟩
  simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, hA.exec,
    execLocalRule_of_none (asms_bra (t := t) (target := target) (uni := true)), execLocal,
    Op.rule, execBranch, Op.isLocal, pure, Except.pure]

/-- **The selection and the reciprocal after a successful poll** (pcs 2601-2602): `1762` is `1.0`
where `%p178` holds and `l` else, `1761` is the outcome of `rcp.approx.ftz.f32`; where that
faults the thread is dead. -/
theorem wait_ok_steps {u : TState} {F : List (Nat × Value)} (d : D) (hl4 : d.pr.l.bytes = 4)
    (h : At u 2601 F) (h179 : (178, .pred d.pr.eq0) ∈ F) (h1916 : (1915, d.pr.l) ∈ F)
    (hk1763 : ∀ q ∈ F, q.1 ≠ 1762) (hk1762 : ∀ q ∈ F, q.1 ≠ 1761) :
    (d.pr.rcpOk = true → ∃ t', run kernel asms L g 2 u = some t' ∧
      At t' 2603 ((1761, d.pr.inv) :: (1762, if d.pr.eq0 then one32 else d.pr.l) :: F)) ∧
    (d.pr.rcpOk = false → Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) := by
  have h179' : u.regs 178 = some (.pred d.pr.eq0) := holds_mem h.2.2.2.2 h179
  have h1916' : u.regs 1915 = some d.pr.l := holds_mem h.2.2.2.2 h1916
  set sv : Value := if d.pr.eq0 then one32 else d.pr.l with hsv
  have hex2 : execLocalA asms L g u (.int ⟨.selp, .float .f32, false, [some 1762],
      [.f32imm 1065353216, .reg 1915, .reg 178]⟩) = .ok (PTX.next (setReg u 1762 sv)) := by
    rw [(segFree (pc := u.pc) (by rw [h.1]; omega)).exec rfl,
      execLocalRule_of_none (asms_none (by simp) (by simp))]
    cases hc : d.pr.eq0
    · simp [execLocal_selp (i := ⟨.selp, .float .f32, false, [some 1762],
        [.f32imm 1065353216, .reg 1915, .reg 178]⟩) rfl, execMove, DType.width, readReg, h179',
        h1916', readValue, hl4, sv, hc, bind, Except.bind, pure, Except.pure]
    · simp [execLocal_selp (i := ⟨.selp, .float .f32, false, [some 1762],
        [.f32imm 1065353216, .reg 1915, .reg 178]⟩) rfl, execMove, DType.width, readReg, h179',
        readBits, readValue, Value.bytes, sv, hc, bind, Except.bind, pure, Except.pure, one32,
        b32]
  set w2 := PTX.next (setReg u 1762 sv) with hw2
  have o1 : out kernel asms L g u = .tau w2 :=
    tau_of_ok (by rw [h.1]; exact Flow.code_2601) rfl h.2.2.2.1 hex2
  have hpc2 : w2.pc = 2602 := by simp [w2, PTX.next, setReg, h.1]
  have hs2 : w2.regs 1762 = some sv := by simp [w2, PTX.next, setReg]
  have hex3 := exec_rcpE (L := L) (g := g) (t := w2) (approxAt_rcp (by omega)).1
    (approxAt_rcp (by omega)).2 (fz := true) (d := 1761) (OpndIs.reg hs2)
  have hre : d.pr.inv = okVal (b32 0) (rcpE true sv) := rfl
  constructor
  · intro hok
    have hok' : (rcpE true sv).toBool = true := hok
    obtain ⟨v, hv⟩ : ∃ v, rcpE true sv = .ok v := by
      cases hh : rcpE true sv with
      | error f => rw [hh] at hok'; simp [Except.toBool] at hok'
      | ok v => exact ⟨v, rfl⟩
    have o2 : out kernel asms L g w2 = .tau (PTX.next (setReg w2 1761 v)) :=
      tau_of_ok (by rw [hpc2]; exact Flow.code_2602) rfl h.2.2.2.1 (by rw [hex3, hv]; rfl)
    have hr23 : run kernel asms L g 2 u = some (PTX.next (setReg w2 1761 v)) := by
      simp only [run, tauStep, o1, o2, Option.bind_some]
    refine ⟨PTX.next (setReg w2 1761 v), hr23, ?_⟩
    have h2 : At w2 2602 ((1762, sv) :: F) := At.set h hk1763
    have hk : ∀ q ∈ (1762, sv) :: F, q.1 ≠ 1761 := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · show 1762 ≠ 1761; decide
      · exact hk1762 q hq
    have h3 := At.set (r := 1761) (v := v) h2 hk
    have hv' : d.pr.inv = v := by rw [hre, hv]; rfl
    rw [hv'] at *
    exact h3
  · intro hbad
    have hbad' : (rcpE true sv).toBool = false := hbad
    obtain ⟨f, hf⟩ : ∃ f, rcpE true sv = .error f := by
      cases hh : rcpE true sv with
      | error f => exact ⟨f, rfl⟩
      | ok v => rw [hh] at hbad'; simp [Except.toBool] at hbad'
    exact Machine.dead_of_tau o1
      (dead_of_error (f := f) (by rw [hpc2]; exact Flow.code_2602) rfl h.2.2.2.1
        (by rw [hex3, hf]; rfl))

/-! ### Guarded instructions that are skipped -/

/-- An instruction whose guard `@p` is false is skipped, whatever it is. -/
theorem seg_off {pc p : Nat} {op : Op} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨some (p, false), op⟩) (hp : (p, Value.pred false) ∈ F) :
    Seg kernel asms L g 1 pc F (pc + 1) F := by
  intro t h
  have hp' : t.regs p = some (.pred false) := holds_mem h.2.2.2.2 hp
  refine ⟨skip t, ?_, by simp [skip, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩
  simp [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, readReg, hp', bind, Except.bind, pure,
    Except.pure]

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
