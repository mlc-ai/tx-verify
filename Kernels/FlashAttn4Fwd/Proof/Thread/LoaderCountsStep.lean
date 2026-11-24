-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderCountsRounds

@[expose] public section

/-! # The loader's counts along its run

`counts_step`: every event fired at a loader state keeps `Counts`, the role's part of
`Code.run_inv` (with `Counts.init` at the role's start). The event has its site's shape
(`site_event`); the ledger moves by what that shape counts (`ledger_step`: per site, one case per
outcome of `next`, closed by arithmetic on the count formulas, `ledger_by`), the elections
likewise (`elects_step`); the rounds move at their own poll positions (`rounds_step`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {i tt s ph qp : Nat} {d' : D}
  {pre : List Event} {e : Event}

/-- The outcome of the last event of `es ++ [e]`, when every election of the trace returned the
thread's lane: an election `e` returned it. -/
local macro "elect_outcome " hl:ident : tactic => `(tactic| (
  have hlane := (electLead_append.mp $hl).2
  simp [ElectLead] at hlane))

set_option hygiene false in
/-- The obligations of `counts_of` at one site and outcome: the ring registers and the counts by
arithmetic (with the outcome of the step's election, if it is one), an arrival's barrier and
bytes, the copy fact of a copy site. -/
local macro "ledger_close" : tactic => `(tactic| (
  refine counts_of hJ (by cnt_arith [uB_succ])
    (fun s' => by cnt_arith [okPoll, sourceWaitSuccess, uB_succ])
    (fun st => by cnt_arith [okPoll, sourceWaitSuccess])
    (fun hl s' => by
      elect_outcome hl
      cnt_arith [arrivesOn, sourceArrive, uB_succ])
    (fun hl st => by
      elect_outcome hl
      cnt_arith [arrivesOn, sourceArrive])
    (fun m tx c rel sc hk => by
      cases hk <;> first
        | exact .inl ⟨by rfl, ⟨_, hs6⟩, by kv_loc⟩
        | exact .inl ⟨by rfl, ⟨_, hsn⟩, by kv_loc⟩
        | exact .inr ⟨by rfl, 0, by kv_loc⟩
        | exact .inr ⟨by rfl, 1, by kv_loc⟩)
    (fun hl s' => by
      elect_outcome hl
      (try simp only [issuesTo, hmb])
      cnt_arith [issuesTo, uB_succ, CopyId.bar, CopyId.use])
    (fun hl st => by
      elect_outcome hl
      (try simp only [issuesTo, hmb])
      cnt_arith [issuesTo, CopyId.bar])
    (fun hn' m => by
      first
        | exact absurd hn'.of_snoc ‹¬ ElectNonLead L g pre›
        | exact absurd hn'.of_snoc (hEl (by simp))
        | exact ⟨by rfl, by rfl⟩)
    (fun hs hnl => by
      first
        | (simp at hs; done)
        | (have hn2 := (electNonLead_append.mp hnl).2
           simp [ElectNonLead] at hn2))
    (fun hs => by simp at hs)
    (by first | exact ‹CopyFact L g pre _› | exact fun a sp hk => by cases hk)))

set_option hygiene false in
/-- **The ledger after one step at the sites `xs` split into**: the facts the arithmetic uses
(the ring registers of the state's use, the launch, the state's bounds, the last event's
election outcome), then one case per site and outcome of `next` (`shape_cases`), each closed by
`ledger_close`. -/
local macro "ledger_by" xs:(ppSpace colGt ident)* : tactic => `(tactic| (
  have hsh := shape hpre
  have hR := hJ.ring
  have hEl := hJ.elect
  have hs6 : s < 6 := hi.s
  have hsn := snext_lt hs6
  have hit := hi.item
  have htr := hi.trip
  have hld := hi.lead
  have hev2 := uB_even L i
  have hevT := uB_even L (T L g)
  have hu0 := uB_zero L
  have hTu : T L g = i + 1 → uB L (T L g) = uB L i + 2 * n L := fun h => by rw [h, uB_succ]
  have hTz : T L g = 0 → uB L (T L g) = 0 := fun h => by rw [h, hu0]
  obtain ⟨epc, ek⟩ := e
  shape_cases $xs* at hev hn unfolding [Ev, PollIs, ArriveIs]
    trans [next, afterCopy, afterUse, afterUse.itemEndOf, UseK.copies, Fin.isValue, Fin.val_zero,
      Fin.val_one, ↓reduceIte, ↓reduceDIte]
  all_goals simp only [Site.inItem, Site.inTrip, Site.leadOnly, kvB, qB, true_implies,
    Bool.false_eq_true, false_implies, Site.arrive.injEq, Site.copy.injEq, exists_eq',
    exists_const, reduceCtorEq, exists_false, or_false, false_or, or_true, true_or,
    and_self] at hit htr hld hR hEl ⊢
  all_goals (try have hmb := (hev hR.1).mbar)
  all_goals (try have hN1 := ring_next hR.1 hR.2.1)
  all_goals (try have hN2 := ring_after hR.1 hR.2.1 2)
  all_goals (try have hNk := ring_after hR.1 hR.2.1 ‹Fin 6›)
  all_goals ledger_close))

variable (hpre : Pre P L mem0)
include hpre

set_option maxHeartbeats 4000000

omit hpre in
theorem uB_zero (L : Launch) : uB L 0 = 0 := by simp [uB]

theorem ledger_setMaxReg (hJ : Ledger L g ⟨.setMaxReg, i, tt, s, ph, qp⟩ pre)
    (hi : Inv L g ⟨.setMaxReg, i, tt, s, ph, qp⟩) (hev : Ev L g ⟨.setMaxReg, i, tt, s, ph, qp⟩ e)
    (hn : next L g ⟨.setMaxReg, i, tt, s, ph, qp⟩ e = some (some d')) :
    Ledger L g d' (pre ++ [e]) := by
  obtain ⟨hi0, -, hs0, hph0, hqp0⟩ := hJ.start rfl
  have hiu : uB L i = 0 := by simp only at hi0; rw [hi0, uB_zero]
  ledger_by

theorem ledger_head (hJ : Ledger L g ⟨.head, i, tt, s, ph, qp⟩ pre)
    (hi : Inv L g ⟨.head, i, tt, s, ph, qp⟩) (hev : Ev L g ⟨.head, i, tt, s, ph, qp⟩ e)
    (hn : next L g ⟨.head, i, tt, s, ph, qp⟩ e = some (some d')) :
    Ledger L g d' (pre ++ [e]) := by ledger_by

theorem ledger_wait {u : UseK} (hJ : Ledger L g ⟨.wait u, i, tt, s, ph, qp⟩ pre)
    (hi : Inv L g ⟨.wait u, i, tt, s, ph, qp⟩) (hev : Ev L g ⟨.wait u, i, tt, s, ph, qp⟩ e)
    (hn : next L g ⟨.wait u, i, tt, s, ph, qp⟩ e = some (some d')) :
    Ledger L g d' (pre ++ [e]) := by ledger_by u

theorem ledger_elA {u : UseK} (hJ : Ledger L g ⟨.elA u, i, tt, s, ph, qp⟩ pre)
    (hi : Inv L g ⟨.elA u, i, tt, s, ph, qp⟩) (hev : Ev L g ⟨.elA u, i, tt, s, ph, qp⟩ e)
    (hn : next L g ⟨.elA u, i, tt, s, ph, qp⟩ e = some (some d')) :
    Ledger L g d' (pre ++ [e]) := by ledger_by u

theorem ledger_arrive {u : UseK} (hJ : Ledger L g ⟨.arrive u, i, tt, s, ph, qp⟩ pre)
    (hi : Inv L g ⟨.arrive u, i, tt, s, ph, qp⟩) (hev : Ev L g ⟨.arrive u, i, tt, s, ph, qp⟩ e)
    (hn : next L g ⟨.arrive u, i, tt, s, ph, qp⟩ e = some (some d')) :
    Ledger L g d' (pre ++ [e]) := by ledger_by u

theorem ledger_elC {u : UseK} {j : Fin 2} (hJ : Ledger L g ⟨.elC u j, i, tt, s, ph, qp⟩ pre)
    (hi : Inv L g ⟨.elC u j, i, tt, s, ph, qp⟩) (hev : Ev L g ⟨.elC u j, i, tt, s, ph, qp⟩ e)
    (hn : next L g ⟨.elC u j, i, tt, s, ph, qp⟩ e = some (some d')) :
    Ledger L g d' (pre ++ [e]) := by
  have hone := hi.one u j (.inl rfl)
  ledger_by u j

theorem ledger_copy {u : UseK} {j : Fin 2} (hJ : Ledger L g ⟨.copy u j, i, tt, s, ph, qp⟩ pre)
    (hi : Inv L g ⟨.copy u j, i, tt, s, ph, qp⟩) (hev : Ev L g ⟨.copy u j, i, tt, s, ph, qp⟩ e)
    (hn : next L g ⟨.copy u j, i, tt, s, ph, qp⟩ e = some (some d')) :
    Ledger L g d' (pre ++ [e]) := by
  have hone := hi.one u j (.inr rfl)
  have hcf := (copy_fact hJ hi hev rfl).fact
  ledger_by u j

theorem ledger_drain {k : Fin 6} (hJ : Ledger L g ⟨.drain k, i, tt, s, ph, qp⟩ pre)
    (hi : Inv L g ⟨.drain k, i, tt, s, ph, qp⟩) (hev : Ev L g ⟨.drain k, i, tt, s, ph, qp⟩ e)
    (hn : next L g ⟨.drain k, i, tt, s, ph, qp⟩ e = some (some d')) :
    Ledger L g d' (pre ++ [e]) := by ledger_by

theorem ledger_drainQ (hJ : Ledger L g ⟨.drainQ, i, tt, s, ph, qp⟩ pre)
    (hi : Inv L g ⟨.drainQ, i, tt, s, ph, qp⟩) (hev : Ev L g ⟨.drainQ, i, tt, s, ph, qp⟩ e)
    (hn : next L g ⟨.drainQ, i, tt, s, ph, qp⟩ e = some (some d')) :
    Ledger L g d' (pre ++ [e]) := by ledger_by

theorem ledger_elTail (hJ : Ledger L g ⟨.elTail, i, tt, s, ph, qp⟩ pre)
    (hi : Inv L g ⟨.elTail, i, tt, s, ph, qp⟩) (hev : Ev L g ⟨.elTail, i, tt, s, ph, qp⟩ e)
    (hn : next L g ⟨.elTail, i, tt, s, ph, qp⟩ e = some (some d')) :
    Ledger L g d' (pre ++ [e]) := by ledger_by

theorem ledger_arriveTail (hJ : Ledger L g ⟨.arriveTail, i, tt, s, ph, qp⟩ pre)
    (hi : Inv L g ⟨.arriveTail, i, tt, s, ph, qp⟩)
    (hev : Ev L g ⟨.arriveTail, i, tt, s, ph, qp⟩ e)
    (hn : next L g ⟨.arriveTail, i, tt, s, ph, qp⟩ e = some (some d')) :
    Ledger L g d' (pre ++ [e]) := by ledger_by

/-- **Every event fired at a loader state keeps the ledger.** -/
theorem ledger_step {d : D} (hJ : Ledger L g d pre) (hi : Inv L g d) (hev : Ev L g d e)
    (hn : next L g d e = some (some d')) : Ledger L g d' (pre ++ [e]) := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  cases site with
  | setMaxReg => exact ledger_setMaxReg hpre hJ hi hev hn
  | head => exact ledger_head hpre hJ hi hev hn
  | wait u => exact ledger_wait hpre hJ hi hev hn
  | elA u => exact ledger_elA hpre hJ hi hev hn
  | arrive u => exact ledger_arrive hpre hJ hi hev hn
  | elC u j => exact ledger_elC hpre hJ hi hev hn
  | copy u j => exact ledger_copy hpre hJ hi hev hn
  | drain k => exact ledger_drain hpre hJ hi hev hn
  | drainQ => exact ledger_drainQ hpre hJ hi hev hn
  | elTail => exact ledger_elTail hpre hJ hi hev hn
  | arriveTail => exact ledger_arriveTail hpre hJ hi hev hn
  | exit => simp [next] at hn

omit hpre in
/-- Every event fired at a loader state keeps `Counts`. -/
theorem counts_step (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t : TState}
    {ins : Instr} {o : Option TState} (hJ : Counts L g d pre) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) (hn : next L g d e = some (some d')) :
    Counts L g d' (pre ++ [e]) :=
  have hev := site_event hpre hg h hi hc hf
  ⟨ledger_step hpre hJ.toLedger hi hev hn, rounds_step hJ.rounds hi hc hf hn,
    elects_step hJ.elects hi hev hn⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
