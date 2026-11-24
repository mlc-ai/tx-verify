-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueSteps
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Warp 0's elections and barrier initializations

Each of warp 0's fourteen elections continues on the elected lane to the first initialization
of its group and on the other lanes to the site after the group (`electNext`); each
initialization continues to the next of its group or to the site after the group (`initNext`).
The warp is known (`Inv`), so every warp test of these segments is evaluated; the two segments
through the computation of the leader's rank are evaluated in the two cases of the rank. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}
  {ins : Instr}

/-- The predicate register election `e` writes. -/
def electPred (e : Fin 14) : Nat :=
  [6, 9, 12, 15, 17, 20, 26, 29, 31, 34, 36, 39, 41, 44].getD e.val 0

/-- Where election `e` leads: the leader to its group, the other lanes past it. -/
def electNext (e : Fin 14) (b : Bool) : Site := if b then .init (groupStart e) else afterGroup e

/-- The local instructions after election `e` (leader or not). -/
def electLen (e : Fin 14) (b : Bool) : Nat :=
  if b then 3 else [5, 4, 5, 2, 5, 12, 5, 2, 4, 2, 6, 2, 5, 2].getD e.val 0

/-- The local instructions after initialization `j`. -/
def initLen (j : Fin 36) : Nat :=
  [0, 3, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 10, 0, 3, 0, 0, 0, 2, 0, 0, 0, 4,
    0, 0, 0, 3, 0, 0].getD j.val 0

theorem code_elect (e : Fin 14) : ∃ dst, kernel.code[(Site.elect e).pc]? =
    some ⟨none, .warp ⟨.elect, none, [some dst, some (electPred e)], [], some (.imm (-1))⟩⟩ ∧
    dst ∉ Flow.live (Site.elect e).pc ∧ electPred e ∉ Flow.live (Site.elect e).pc := by
  fin_cases e
  all_goals first
    | exact ⟨_, Flow.code_elect_1, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_2, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_3, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_4, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_5, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_6, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_7, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_8, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_9, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_10, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_11, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_12, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_13, by table_decide, by table_decide⟩
    | exact ⟨_, Flow.code_elect_14, by table_decide, by table_decide⟩

/-- Each initialization site is an unguarded `mbarrier.init` (decided on the code). -/
theorem init_ops : ∀ j : Fin 36, (kernel.code[(Site.init j).pc]?).map
    (fun ins => decide (ins.guard = none) &&
      (match ins.op with | .mbarInit .. => true | _ => false))
      = some true := by
  decide +kernel

theorem code_init (j : Fin 36) :
    ∃ ins, kernel.code[(Site.init j).pc]? = some ins ∧ ins.guard = none ∧ AdvancesOp ins.op := by
  have h := init_ops j
  cases hc : kernel.code[(Site.init j).pc]? with
  | none => rw [hc] at h; cases h
  | some ins =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨ins, rfl, h.1, ?_⟩
    obtain ⟨_, h2⟩ := h
    revert h2
    cases ins.op <;> simp [AdvancesOp]

theorem rank_cases' (hpre : Pre P L mem0) (g : Nat) : rankOf L g = 0 ∨ rankOf L g = 1 := by
  rw [rankOf_eq hpre]
  omega

set_option maxHeartbeats 20000000 in
/-- The local code after election `e`. -/
theorem elect_seg (hpre : Pre P L mem0) (e : Fin 14) (b : Bool) {u : TState}
    (h1 : At u ((Site.elect e).pc + 1)
      ((electPred e, .pred b) :: factsAt L g 0 (rankOf L g) (Site.elect e).pc)) :
    ∃ t', run kernel asms L g (electLen e b) u = some t' ∧
      At t' (electNext e b).pc (factsAt L g 0 (rankOf L g) (electNext e b).pc) := by
  fin_cases e <;> cases b
  all_goals first
    | pro_seg h1 hpre [rankOf, ctaOf, Launch.oneDim_rankOfCta hpre.oneDimLaunch.1, hpre.cluster]
    | (rcases rank_cases' hpre g with hr | hr <;> (rw [hr] at h1 ⊢; pro_seg h1 hpre))

set_option maxHeartbeats 20000000 in
/-- The local code after initialization `j`. -/
theorem init_seg (hpre : Pre P L mem0) (j : Fin 36) {u : TState}
    (h1 : At u ((Site.init j).pc + 1) (factsAt L g 0 (rankOf L g) (Site.init j).pc)) :
    ∃ t', run kernel asms L g (initLen j) u = some t' ∧
      At t' (initNext j).pc (factsAt L g 0 (rankOf L g) (initNext j).pc) := by
  fin_cases j
  all_goals first
    | pro_seg h1 hpre [rankOf, ctaOf, Launch.oneDim_rankOfCta hpre.oneDimLaunch.1, hpre.cluster]
    | (rcases rank_cases' hpre g with hr | hr <;> (rw [hr] at h1 ⊢; pro_seg h1 hpre))

theorem electNext_ne (e : Fin 14) (b : Bool) :
    electNext e b ≠ .elect12 ∧ electNext e b ≠ .init320 := by
  unfold electNext afterGroup
  split_ifs <;> simp

theorem initNext_ne (j : Fin 36) : initNext j ≠ .elect12 ∧ initNext j ≠ .init320 := by
  unfold initNext afterGroup
  split_ifs <;> simp

/-- Warp 0's election `e`. -/
theorem step_elect (hpre : Pre P L mem0) (k : Fin 14) (hs : d.site = .elect k) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  have hw := hi.warp0 (.inl ⟨k, rfl⟩)
  obtain ⟨dst, hc', hd, hp⟩ := code_elect k
  rw [hc] at hc'
  cases hc'
  obtain ⟨mk, inst, ld, rfl, hu⟩ := fires_elect hf
  right
  have h1 : At u ((Site.elect k).pc + 1)
      ((electPred k, .pred (laneOf L g == ld)) :: factsAt L g 0 (rankOf L g) (Site.elect k).pc) :=
    hu ▸ hw ▸ at_elect h hd hp
  obtain ⟨t2, hr2, h2⟩ := elect_seg hpre k _ h1
  rw [← hw] at h2
  have hn : next L g ⟨.elect k⟩ ⟨(Site.elect k).pc, .elect mk inst ld⟩ =
      some (some (.inl ⟨electNext k (laneOf L g == ld)⟩)) := by
    simp only [next, electNext]
    by_cases hl : laneOf L g = ld <;> simp [hl]
  exact ⟨.inl ⟨electNext k (laneOf L g == ld)⟩, t2, hn, run_rtg hr2,
    good_inl h2 ⟨fun _ => hw, fun h => by
      rcases h with h | h
      · exact absurd h (electNext_ne k _).1
      · exact absurd h (electNext_ne k _).2⟩⟩

/-- Warp 0's initialization `j`. -/
theorem step_init (hpre : Pre P L mem0) (j : Fin 36) (hs : d.site = .init j) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  have hw := hi.warp0 (.inr ⟨j, rfl⟩)
  obtain ⟨ins', hc', -, hadv⟩ := code_init j
  rw [hc] at hc'
  cases hc'
  obtain rfl := fires_next hadv hf
  right
  have h1 : At (PTX.next t) ((Site.init j).pc + 1) (factsAt L g 0 (rankOf L g) (Site.init j).pc) :=
    hw ▸ At.next h
  obtain ⟨t2, hr2, h2⟩ := init_seg hpre j h1
  rw [← hw] at h2
  exact ⟨.inl ⟨initNext j⟩, t2, by simp [next], run_rtg hr2,
    good_inl h2 ⟨fun _ => hw, fun h => by
      rcases h with h | h
      · exact absurd h (initNext_ne j).1
      · exact absurd h (initNext_ne j).2⟩⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
