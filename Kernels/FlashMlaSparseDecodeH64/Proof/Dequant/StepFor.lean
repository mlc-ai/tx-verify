-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.StepForBase
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part041
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part056
import Lemmas.Flow.CtlStepsU
import Lemmas.Flow.IssueNext
import Lemmas.Flow.RoleTemplates
import Lemmas.Flow.Step.Combinators
import Kernels.FlashMlaSparseDecodeH64.Gen.StepDequant

@[expose] public section

/-! # Warpgroup 2's strict steps at the sites without data

`stepAt_<site>S`: the exact step obligation (`Code.StepAt`, so strict for every event by
`StepAt.stepFor`) of the control machine at the sites `wq`, `wraw`, `wsv`, `fpx`, `arrD`, `bar`,
`exit`, the two length loads (`lenA`, `lenB`) and the last store of a row (`store r 7`), for a
state at element 0 (the other elements have a false invariant). The control segments are exact
(`seg_sym`, no `SegU`): the registers the segments write are control registers.
`stepAt_arrFS` cuts the ring's advance at pc 3603 (`ringSegS`); the set-up's `smr` is in
`StepForSmr.lean`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem stepAt_fpxS (d : D) (hs : d.site = .fpx) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  dq_state d
  simp only at hs he
  subst he hs
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_3595, rfl, trivial⟩)
    (Code.step_issue (C := code P L g w)
      (dn := ⟨.arrD, 0, ac, l0, l1, cnt, sb, pb⟩) Flow.code_3595
      (fun hf => Option.some.inj (fires_fence_proxy hf).2) (fun _ => rfl) rfl rfl
      ⟨fun _ => ?_, rfl, rfl, fun _ => Nat.one_pos⟩)
  dsimp only [code, facts, Site.pc, rowBase]
  seg_sym using dq_segS

theorem stepAt_wrawS (d : D) (hs : d.site = .wraw) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  dq_state d
  simp only at hs he
  subst he
  dq_sites s

theorem stepAt_arrDS (d : D) (hs : d.site = .arrD) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  dq_state d
  simp only at hs he
  subst he hs
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_3597, rfl, trivial⟩)
    (Code.step_issue (C := code P L g w)
      (dn := ⟨.arrF, 0, ac, l0, l1, cnt, sb, pb⟩) Flow.code_3597
      (fun hf => Code.fires_arrive_next hf) (fun _ => rfl) rfl rfl
      ⟨fun _ => ?_, rfl, rfl, fun _ => Nat.one_pos⟩)
  dsimp only [code, facts, Site.pc, rowBase]
  seg_sym using dq_segS

theorem stepAt_barS (d : D) (hs : d.site = .bar) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  dq_state d
  simp only at hs he
  subst he hs
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_3610, rfl, trivial⟩)
    (Code.step_issue (C := code P L g w)
      (dn := ⟨.exit, 0, ac, l0, l1, cnt, sb, pb⟩) Flow.code_3610
      (fun hf => fires_barSyncN_next hf) (fun _ => rfl) rfl rfl
      ⟨fun _ => ?_, rfl, rfl, fun _ => Nat.one_pos⟩)
  dsimp only [code, facts, Site.pc, rowBase]
  seg_sym using dq_segS

theorem stepAt_wsvS (d : D) (hs : d.site = .wsv) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  dq_state d
  simp only at hs he
  subst he
  dq_sites s

theorem stepAt_wqS (d : D) (hs : d.site = .wq) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  dq_state d
  simp only at hs he
  subst he
  dq_sites s

theorem ringSegS (ac : List Value) (l0 l1 cnt : BitVec 64) (sb pb : Bool) :
    ∃ n, Seg kernel Assumptions.all L g n 3600
      (factsFrom (ctlLive 3599) (valueOf P L g ⟨.arrF, 0, ac, l0, l1, cnt, sb, pb⟩))
      3607 (factsFrom (ctlLive 3607)
        (valueOf P L g ⟨.bar, 0, ac, l0, l1, addi cnt 1, !sb, pb != sb⟩)) := by
  refine Seg.comp_ex (q := 3603) (H := (136, .pred (pb != sb)) ::
    factsFrom ((ctlLive 3603).erase 136) (valueOf P L g ⟨.arrF, 0, ac, l0, l1, cnt, sb, pb⟩)) ?_ ?_
  · cases sb <;> cases pb <;> seg_sym using dq_segS
  · generalize (pb != sb) = c
    cases c <;> cases sb <;> seg_sym using dq_segS


set_option hygiene false in
local macro "arr_step " S:term:max : tactic => `(tactic| (
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_3599, rfl, trivial⟩)
    (Code.step_issue (C := code P L g w)
      (dn := ⟨$S, 0, ac, l0, l1, addi cnt 1, !sb, pb != sb⟩) Flow.code_3599
      (fun hf => Code.fires_arrive_next hf)
      (fun _ => by simp only [code, succ, advance, hz, Bool.false_eq_true, ↓reduceIte])
      rfl rfl ⟨fun _ => ?_, rfl, rfl, fun _ => Nat.one_pos⟩)
  dsimp only [code, facts, Site.pc, rowBase]
  refine Seg.comp_ex (q := 3607) (H := factsFrom (ctlLive 3607)
    (valueOf P L g ⟨.bar, 0, ac, l0, l1, addi cnt 1, !sb, pb != sb⟩))
    (ringSegS ac l0 l1 cnt sb pb) ?_
  refine Seg.pred_ex (p := 137) (c := scmpi .ne .b (addi cnt 1) 0) (c' := _)
    (mem_factsFrom_eq (show 137 ∈ ctlLive 3607 by decide +kernel) rfl) hz ?_
  seg_sym using dq_segS))

theorem stepAt_arrFS (d : D) (hs : d.site = .arrF) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  dq_state d
  simp only at hs he
  subst he hs
  cases hz : scmpi .ne .b (addi cnt 1) 0
  · arr_step .bar
  · arr_step .wraw


theorem stepAt_store7S (r : Fin 4) (d : D) (hs : d.site = .store r 7) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  dq_state d
  simp only at hs he
  subst he
  fin_cases r <;> dq_sites s

theorem stepAt_exitS (d : D) (hs : d.site = .exit) : (code P L g w).StepAt d := by
  have hp : (code P L g w).pc d = 3611 := by show d.site.pc = 3611; rw [hs]; rfl
  refine ⟨fun _ => ⟨⟨none, .ret⟩, by rw [hp]; exact Flow.code_3611, rfl, trivial⟩,
    fun ins _ _ hc hf => ?_⟩
  rw [hp, Flow.code_3611] at hc
  obtain rfl := Option.some.inj hc
  simp [eventTmpl, Fires] at hf

theorem stepAt_lenAS (d : D) (hs : d.site = .lenA) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  dq_state d
  simp only at hs he
  subst he
  dq_sites s

theorem stepAt_lenBS (d : D) (hs : d.site = .lenB) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  dq_state d
  simp only at hs he
  subst he
  dq_sites s

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
