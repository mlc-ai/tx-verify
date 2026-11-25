-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Shapes

@[expose] public section

/-! # One step of the Producer phase: event, successor and ledger together

`Good P L g pos w p x e` says that a position is good for the event `e` fired at it: the
thread machine has a successor state for `e` (it neither stops following the thread nor declares
it dead), and that state is a successor of the position (`Succ`) with the ledger advanced by the
ledger of `e` (`ledEv`). This file proves it for every position that is not a tensor load
(`good_entry`, `good_poll0` … `good_tail2`) and gives the two forms the generated case analysis
of the 210 load sites uses (`good_issue` for a load followed by a load of the same body,
`good_plain` with `ledEv_issue` for the last load of a body).

The ledger of an event in closed form: `ledEv_bar`, `ledEv_poll` (a successful poll of the
"empty" mbarrier of a stage counts for that stage only: the eleven mbarriers of a block are
distinct), `ledEv_fail`, `ledEv_arrive`, `ledEv_issue`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup (cu ft)
open PTX.Kernels.FlashKdaFwd.Protocol (Bar)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-- **A position is good for an event**: the event is the closed-form event of the position,
the machine has a successor state, and it is a successor of the position with the ledger
advanced by the event. -/
def Good (P : Params) (L : Launch) (g : Nat) (pos : Pos) (w : Nat → BitVec 64)
    (p : Nat → Bool) (x : Nat → Value) (e : Event) : Prop :=
  Ev P L g pos e ∧ ∃ d', Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some d') ∧
    Succ P g pos (ledEv L (g / L.block) e) d'

theorem good_plain {pos : Pos} {δ : Led} {aft : D} (hev : Ev P L g pos e)
    (hnx : Thread.next L g ⟨pos.site, w, p, x⟩ e = some (some aft)) (h : Succ P g pos δ aft)
    (hδ : ledEv L (g / L.block) e = δ) : Good P L g pos w p x e :=
  ⟨hev, aft, hnx, hδ ▸ h⟩

/-! ### The ledger of an event -/

theorem emptyLoc_inj {c : Nat} {s s' : Fin 3} : emptyLoc L c s = emptyLoc L c s' ↔ s = s' :=
  ⟨fun h => by cases (Bar.loc_inj h).1; rfl, fun h => h ▸ rfl⟩

theorem fullLoc_inj {c : Nat} {s s' : Fin 3} : fullLoc L c s = fullLoc L c s' ↔ s = s' :=
  ⟨fun h => by cases (Bar.loc_inj h).1; rfl, fun h => h ▸ rfl⟩

theorem empty_ne_full {c : Nat} {s s' : Fin 3} : emptyLoc L c s ≠ fullLoc L c s' := fun h => by
  cases (Bar.loc_inj h).1

theorem stage_eq (tt : Nat) (k : Fin 3) : stage tt = k ↔ tt % 3 = k.val := by
  simp only [stage, Fin.ext_iff]

theorem ledEv_bar (pc : Nat) : ledEv L (g / L.block) ⟨pc, .bar 0 none .sync⟩ = dBar := rfl

theorem ledEv_fail (pc q : Nat) (m : Loc) (acq : Bool) (sc : MbarScope) :
    ledEv L (g / L.block) ⟨pc, .wait m q false acq sc⟩ = dNone := rfl

theorem ledEv_poll (pc q tt : Nat) (acq : Bool) (sc : MbarScope) :
    ledEv L (g / L.block) ⟨pc, .wait (emptyLoc L (g / L.block) (stage tt)) q true acq sc⟩ =
      dPoll (tt % 3) := by
  simp only [ledEv, dPoll, Execution.isBarId, Startup.isInit, Startup.isArr, Startup.isIssue,
    Startup.isOkPoll, okPoll, sourceWaitSuccess, arrivesOn, sourceArrive, issuesTo,
    decide_eq_true_eq, emptyLoc_inj, stage_eq, Bool.false_eq_true, ↓reduceIte, Led.mk.injEq,
    true_and, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> rfl

theorem ledEv_arrive (pc tx n tt : Nat) (rel : Bool) (sc : MbarScope) :
    ledEv L (g / L.block) ⟨pc, .arrive (fullLoc L (g / L.block) (stage tt)) tx n rel sc⟩ =
      dArr (tt % 3) := by
  simp only [ledEv, dArr, Execution.isBarId, Startup.isInit, Startup.isArr, Startup.isIssue,
    Startup.isOkPoll, okPoll, sourceWaitSuccess, arrivesOn, sourceArrive, issuesTo,
    decide_eq_true_eq, fullLoc_inj, stage_eq, Bool.false_eq_true, ↓reduceIte, Led.mk.injEq,
    true_and, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> rfl

theorem ledEv_issue (hpre : Pre P L mem0) {c : Fin 3} {u : Nat} {i : Fin 70}
    (hev : Ev P L g (.load c u i) e) : ledEv L (g / L.block) e = dIss (tile c u % 3) := by
  rw [show e = _ from hev]
  simp only [ledEv, dIss, Execution.isBarId, Startup.isInit, Startup.isArr, Startup.isIssue,
    Startup.isOkPoll, okPoll, sourceWaitSuccess, arrivesOn, sourceArrive, issuesTo, tileLoad,
    loadSpec_mbar, fullLoc_eq hpre, decide_eq_true_eq, fullLoc_inj, stage_eq,
    Bool.false_eq_true, ↓reduceIte, Led.mk.injEq, true_and, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- **A tensor load followed by another load of the same body.** -/
theorem good_issue (hpre : Pre P L mem0) {c : Fin 3} {u : Nat} {i : Fin 70}
    (hi : i.val + 1 < 70) {aft : D} (hev : Ev P L g (.load c u i) e)
    (hnx : Thread.next L g ⟨(Pos.load c u i).site, w, p, x⟩ e = some (some aft))
    (hst : RefAt P g (.load c u ⟨i.val + 1, hi⟩) aft) : Good P L g (.load c u i) w p x e :=
  good_plain hev hnx (.inl ⟨_, hst, led_load c u i hi⟩) (ledEv_issue hpre hev)

/-! ### The positions that are no tensor loads -/

theorem good_entry (hpre : Pre P L mem0) (hg : g < L.threads) (hw : warp g = 4)
    (h : RefAt P g .entry ⟨.bar 5, w, p, x⟩) (hc : kernel.code[(Site.bar 5).pc]? = some ins)
    (hf : Fires (Site.bar 5).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Good P L g .entry w p x e := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have hev : e = ⟨1402, .bar 0 none .sync⟩ :=
    shape_barSync (P := fun e => e = ⟨_, .bar 0 none .sync⟩) hf (by decide) rfl
  subst hev
  exact good_plain rfl (next_bar_5 w p x _) (st_entry hpre hg hw h) (ledEv_bar _)

/-- A poll: a failed one stays, a successful one is the step `hok`. -/
theorem good_wait {pos : Pos} {pc q tt : Nat} {aft : Bool → D}
    (hev : ∃ ok, e = ⟨pc, .wait (emptyLoc L (g / L.block) (stage tt)) q ok true .cta⟩)
    (hpos : (∃ ok, e = ⟨pc, .wait (emptyLoc L (g / L.block) (stage tt)) q ok true .cta⟩) →
      Ev P L g pos e)
    (hnx : ∀ ok, Thread.next L g ⟨pos.site, w, p, x⟩
      ⟨pc, .wait (emptyLoc L (g / L.block) (stage tt)) q ok true .cta⟩ = some (some (aft ok)))
    (hno : Succ P g pos dNone (aft false)) (hok : Succ P g pos (dPoll (tt % 3)) (aft true)) :
    Good P L g pos w p x e := by
  have hE := hpos hev
  obtain ⟨ok, rfl⟩ := hev
  cases ok
  · exact good_plain hE (hnx false) hno (ledEv_fail _ _ _ _ _)
  · exact good_plain hE (hnx true) hok (ledEv_poll _ _ _ _ _)

theorem good_poll0 (hpre : Pre P L mem0) {u : Nat}
    (h : RefAt P g (.poll 0 u) ⟨.mbarWait 1, w, p, x⟩)
    (hat : (code L g).AtD ⟨.mbarWait 1, w, p, x⟩ t)
    (hc : kernel.code[(Site.mbarWait 1).pc]? = some ins)
    (hf : Fires (Site.mbarWait 1).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Good P L g (.poll 0 u) w p x e := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 670) (by lit_mem) (n := 32) rfl
  have r2 := reg_w hat (r := 2104) (by lit_mem) (n := 32) rfl
  have hh := h.pos
  simp only [AtPos, finVal, Lead, Loop] at hh
  simp only [hh] at r1 r2
  exact good_wait (ev_poll hpre hf r1 r2) id (fun ok => next_mbarWait_1 w p x _)
    (st_poll_no 0 u h) (st_poll0 hpre h)

theorem good_poll1 (hpre : Pre P L mem0) {u : Nat}
    (h : RefAt P g (.poll 1 u) ⟨.mbarWait 2, w, p, x⟩)
    (hat : (code L g).AtD ⟨.mbarWait 2, w, p, x⟩ t)
    (hc : kernel.code[(Site.mbarWait 2).pc]? = some ins)
    (hf : Fires (Site.mbarWait 2).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Good P L g (.poll 1 u) w p x e := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 785) (by lit_mem) (n := 32) rfl
  have r2 := reg_w hat (r := 786) (by lit_mem) (n := 32) rfl
  have hh := h.pos
  simp only [AtPos, finVal, Lead, Loop] at hh
  simp only [hh] at r1 r2
  exact good_wait (ev_poll hpre hf r1 r2) id (fun ok => next_mbarWait_2 w p x _)
    (st_poll_no 1 u h) (st_poll1 hpre h)

theorem good_poll2 (hpre : Pre P L mem0) {u : Nat}
    (h : RefAt P g (.poll 2 u) ⟨.mbarWait 3, w, p, x⟩)
    (hat : (code L g).AtD ⟨.mbarWait 3, w, p, x⟩ t)
    (hc : kernel.code[(Site.mbarWait 3).pc]? = some ins)
    (hf : Fires (Site.mbarWait 3).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Good P L g (.poll 2 u) w p x e := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 923) (by lit_mem) (n := 32) rfl
  have r2 := reg_w hat (r := 2104) (by lit_mem) (n := 32) rfl
  have hh := h.pos
  simp only [AtPos, finVal, Lead, Rem] at hh
  simp only [hh] at r1 r2
  exact good_wait (ev_poll hpre hf r1 r2) id (fun ok => next_mbarWait_3 w p x _)
    (st_poll_no 2 u h) (st_poll2 hpre h)

theorem good_arrive0 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.arrive 0 u) ⟨.mbarArrive 1, w, p, x⟩)
    (hat : (code L g).AtD ⟨.mbarArrive 1, w, p, x⟩ t)
    (hc : kernel.code[(Site.mbarArrive 1).pc]? = some ins)
    (hf : Fires (Site.mbarArrive 1).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Good P L g (.arrive 0 u) w p x e := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 676) (by lit_mem) (n := 32) rfl
  have r2 := reg_w hat (r := 675) (by lit_mem) (n := 32) rfl
  have hh := h.pos
  simp only [AtPos, finVal, Lead, Loop] at hh
  simp only [hh] at r1 r2
  obtain rfl := ev_arrive hpre hf r1 r2
  exact good_plain rfl (next_mbarArrive_1 w p x _) (st_arrive0 hpre hg h) (ledEv_arrive _ _ _ _ _ _)

theorem good_arrive1 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.arrive 1 u) ⟨.mbarArrive 2, w, p, x⟩)
    (hat : (code L g).AtD ⟨.mbarArrive 2, w, p, x⟩ t)
    (hc : kernel.code[(Site.mbarArrive 2).pc]? = some ins)
    (hf : Fires (Site.mbarArrive 2).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Good P L g (.arrive 1 u) w p x e := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 800) (by lit_mem) (n := 32) rfl
  have r2 := reg_w hat (r := 799) (by lit_mem) (n := 32) rfl
  have hh := h.pos
  simp only [AtPos, finVal, Lead, Loop] at hh
  simp only [hh] at r1 r2
  obtain rfl := ev_arrive hpre hf r1 r2
  exact good_plain rfl (next_mbarArrive_2 w p x _) (st_arrive1 hpre hg h) (ledEv_arrive _ _ _ _ _ _)

theorem good_arrive2 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.arrive 2 u) ⟨.mbarArrive 3, w, p, x⟩)
    (hat : (code L g).AtD ⟨.mbarArrive 3, w, p, x⟩ t)
    (hc : kernel.code[(Site.mbarArrive 3).pc]? = some ins)
    (hf : Fires (Site.mbarArrive 3).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Good P L g (.arrive 2 u) w p x e := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 929) (by lit_mem) (n := 32) rfl
  have r2 := reg_w hat (r := 928) (by lit_mem) (n := 32) rfl
  have hh := h.pos
  simp only [AtPos, finVal, Lead, Rem] at hh
  simp only [hh] at r1 r2
  obtain rfl := ev_arrive hpre hf r1 r2
  exact good_plain rfl (next_mbarArrive_3 w p x _) (st_arrive2 hpre hg h) (ledEv_arrive _ _ _ _ _ _)

theorem good_tail0 (hpre : Pre P L mem0) (h : RefAt P g (.tail 0) ⟨.mbarWait 4, w, p, x⟩)
    (hat : (code L g).AtD ⟨.mbarWait 4, w, p, x⟩ t)
    (hc : kernel.code[(Site.mbarWait 4).pc]? = some ins)
    (hf : Fires (Site.mbarWait 4).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Good P L g (.tail 0) w p x e := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 1047) (by lit_mem) (n := 32) rfl
  have r2 := reg_w hat (r := 2104) (by lit_mem) (n := 32) rfl
  have hh := h.pos
  simp only [AtPos, finVal] at hh
  simp only [hh] at r1 r2
  exact good_wait (tt := tilesOf P g + 0) (ev_poll hpre hf r1 r2) id
    (fun ok => next_mbarWait_4 w p x _) (st_tail_no 0 h) (st_tail0 hpre h)

theorem good_tail1 (hpre : Pre P L mem0) (h : RefAt P g (.tail 1) ⟨.mbarWait 5, w, p, x⟩)
    (hat : (code L g).AtD ⟨.mbarWait 5, w, p, x⟩ t)
    (hc : kernel.code[(Site.mbarWait 5).pc]? = some ins)
    (hf : Fires (Site.mbarWait 5).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Good P L g (.tail 1) w p x e := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 1049) (by lit_mem) (n := 32) rfl
  have r2 := reg_w hat (r := 1050) (by lit_mem) (n := 32) rfl
  have hh := h.pos
  simp only [AtPos, finVal] at hh
  simp only [hh] at r1 r2
  exact good_wait (ev_poll hpre hf r1 r2) id (fun ok => next_mbarWait_5 w p x _)
    (st_tail_no 1 h) (st_tail1 hpre h)

theorem good_tail2 (hpre : Pre P L mem0) (h : RefAt P g (.tail 2) ⟨.mbarWait 6, w, p, x⟩)
    (hat : (code L g).AtD ⟨.mbarWait 6, w, p, x⟩ t)
    (hc : kernel.code[(Site.mbarWait 6).pc]? = some ins)
    (hf : Fires (Site.mbarWait 6).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Good P L g (.tail 2) w p x e := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 1051) (by lit_mem) (n := 32) rfl
  have r2 := reg_w hat (r := 1052) (by lit_mem) (n := 32) rfl
  have hh := h.pos
  simp only [AtPos, finVal] at hh
  simp only [hh] at r1 r2
  exact good_wait (ev_poll hpre hf r1 r2) id (fun ok => next_mbarWait_6 w p x _)
    (st_tail_no 2 h) (st_tail2 hpre h)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
