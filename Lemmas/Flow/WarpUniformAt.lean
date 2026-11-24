-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PollSynced

@[expose] public section

/-! # Warp-divergent executions, split by position

`not_warpDivergent_polls` and `not_warpDivergent_synced` (`Lemmas/Flow/WarpUniform.lean`,
`PollSynced.lean`) take `Kernel.pollGuardsOk`: every instruction that compares a guard or an index
between lanes (`Instr.laneCompared`) is a poll branch. A kernel may also have guarded uniform
instructions whose guards are warp-uniform for another reason (for example a guard computed from
the warp index). `WarpDivergentAt U` is `WarpDivergent` restricted to the positions `U` selects.
`not_warpDivergent_polls'` and `not_warpDivergent_synced'` split `WarpDivergent` into the poll
branches, which the poll arguments cover, and the positions of `U`, for which the kernel shows
`¬ WarpDivergentAt U` by its own argument. -/

namespace PTX

open PTX.Proof

noncomputable section

/-- `WarpDivergent` (ERR-NONUNIFORM-GUARD) with the compared records at a position that `U`
selects. -/
def WarpDivergentAt (U : Nat → Prop) (L : Launch) (K : Kernel) (A : List Assumption)
    (X : Execution) : Prop :=
  ∃ g h, g < L.threads ∧ h < L.threads ∧ g ≠ h ∧
    ∃ eg eh vg vh, eg <+: X.tr g ∧ eh <+: X.tr h ∧ Walk K A L g {} eg vg ∧
      Walk K A L h {} eh vh ∧
      ∃ i j pc vi vj, U pc ∧ vg[i]? = some vi ∧ vh[j]? = some vj ∧ vi.pc = pc ∧ vj.pc = pc ∧
        SameUniformGroup L (K.uniformScopeAt pc) g h ∧ vi.Disagree vj ∧
        ¬ VisitBefore L K X g vg i h vh j ∧ ¬ VisitBefore L K X h vh j g vg i ∧
        ¬ PollAgreeExempt K A pc vg vh i j

/-- A property of states that every step of a thread keeps (a local step or an event with a next
state) holds at the state of every record of a walk from a state that has it. -/
theorem Walk.inv {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {I : TState → Prop} (hI : ∀ s ev s', I s → WStep K A L g s ev s' → I s') {t : TState}
    {es : List Event} {vs : List Visit} (h : Walk K A L g t es vs) (ht : I t) {r : Nat}
    {v : Visit} (hv : vs[r]? = some v) : ∃ s ev, I s ∧ v = visit K L g s ev := by
  induction h generalizing r with
  | stop => simp at hv
  | @tau t t' es vs hst hw ih =>
    cases r with
    | zero => exact ⟨t, none, ht, by simpa using hv.symm⟩
    | succ r => exact ih (hI _ _ _ ht (.inl ⟨rfl, hst⟩)) (by simpa using hv)
  | @ev t t' e es vs hst hw ih =>
    cases r with
    | zero => exact ⟨t, some e, ht, by simpa using hv.symm⟩
    | succ r => exact ih (hI _ _ _ ht (.inr ⟨e, rfl, hst⟩)) (by simpa using hv)
  | @last t e hst =>
    cases r with
    | zero => exact ⟨t, some e, ht, by simpa using hv.symm⟩
    | succ r => simp at hv

/-- A `WarpDivergent` execution whose compared position is not a poll branch is one of
`WarpDivergentAt U` when every lane-comparing instruction is a poll branch or selected by `U`; a
divergent pair at a poll branch is returned with its data. -/
theorem warpDivergent_split {U : Nat → Prop} {L : Launch} {K : Kernel} {A : List Assumption}
    {X : Execution}
    (hK : ∀ pc ins, K.code[pc]? = some ins → ins.laneCompared = true →
      K.pollBranch pc = true ∨ U pc)
    (hU : ¬ WarpDivergentAt U L K A X) (hd : WarpDivergent L K A X) :
    ∃ g h, g < L.threads ∧ h < L.threads ∧ g ≠ h ∧
      ∃ eg eh vg vh, eg <+: X.tr g ∧ eh <+: X.tr h ∧ Walk K A L g {} eg vg ∧
        Walk K A L h {} eh vh ∧
        ∃ i j pc vi vj, K.pollBranch pc = true ∧ vg[i]? = some vi ∧ vh[j]? = some vj ∧
          vi.pc = pc ∧ vj.pc = pc ∧ SameUniformGroup L (K.uniformScopeAt pc) g h ∧
          vi.Disagree vj ∧ ¬ VisitBefore L K X g vg i h vh j ∧
          ¬ VisitBefore L K X h vh j g vg i ∧ ¬ PollAgreeExempt K A pc vg vh i j := by
  obtain ⟨g, h, hg, hh, hgh, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, pc, vi, vj, hvi, hvj,
    hpi, hpj, hgrp, hdis, hng, hnh, hnot⟩ := hd
  obtain ⟨s, ev, rfl⟩ := hwg.state hvi
  obtain ⟨ins, hins, hl⟩ : ∃ ins, K.code[s.pc]? = some ins ∧ ins.laneCompared = true := by
    rcases hdis with ⟨b, -, hb, -, -⟩ | ⟨x, -, hx, -, -⟩
    · exact visit_compared_guard hb
    · exact visit_compared_index hx
  simp only [visit_pc] at hpi
  subst hpi
  rcases hK _ _ hins hl with hpb | hu
  · exact ⟨g, h, hg, hh, hgh, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, s.pc, _, vj, hpb, hvi,
      hvj, rfl, hpj, hgrp, hdis, hng, hnh, hnot⟩
  · exact absurd ⟨g, h, hg, hh, hgh, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, s.pc, _, vj, hu,
      hvi, hvj, rfl, hpj, hgrp, hdis, hng, hnh, hnot⟩ hU

/-- **No warp-divergent execution** for a kernel whose guarded uniform instructions are the
branches of its wait loops or at positions `U` selects, when no execution diverges at the
positions of `U`, its polls use warp-uniform objects and polls at the branches no assumption
selects with `uniPoll` are ordered (`not_warpDivergent_polls` with the positions of `U` split
off). -/
theorem not_warpDivergent_polls' {U : Nat → Prop} {L : Launch} {K : Kernel}
    {A : List Assumption} {X : Execution}
    (hK : ∀ pc ins, K.code[pc]? = some ins → ins.laneCompared = true →
      K.pollBranch pc = true ∨ U pc)
    (hU : ¬ WarpDivergentAt U L K A X)
    (hloc : ∀ g t op t', execLocalA A L g t op = .ok t' → LocalFrame op t t')
    (hobj : PollObjUniform L X) (hord : PollOrdered L K A X) : ¬ WarpDivergent L K A X := by
  intro hd
  obtain ⟨g, h, hg, hh, hgh, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, pc, vi, vj, hpb, hvi, hvj,
    hpi, hpj, hgrp, hdis, hng, hnh, hnot⟩ := warpDivergent_split hK hU hd
  obtain ⟨h0, -, dst, neg, tgt, base, off, par, acq, sc, hcb, hcw⟩ := pollBranch_spec hpb
  have hw : SameWarp L g h := by
    simpa [Kernel.uniformScopeAt, hcb, Op.uniformScope, SameUniformGroup] using hgrp
  have hpb1 : K.pollBranch vi.pc = true := by rw [hpi]; exact hpb
  obtain ⟨hi, ug, mg, pg, okg, acqg, scg, hug, hugev⟩ := hwg.poll_before (hloc g) hvi hpb1
  have hpb' : K.pollBranch vj.pc = true := by rw [hpj]; exact hpb
  obtain ⟨hj, uh, mh, ph, okh, acqh, sch, huh, huhev⟩ := hwh.poll_before (hloc h) hvj hpb'
  rw [hpj] at huhev
  rw [hpi] at hugev
  obtain ⟨hxg, -⟩ := hwg.event_get hpg hug hugev
  obtain ⟨hxh, -⟩ := hwh.event_get hph huh huhev
  have hm : mg = mh := hobj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hw hxg hxh
  subst hm
  have hig : Visit.events vg i = Visit.events vg (i - 1) + 1 := by
    have := Visit.events_succ hug hugev
    rwa [Nat.sub_add_cancel hi] at this
  have hjh : Visit.events vh j = Visit.events vh (j - 1) + 1 := by
    have := Visit.events_succ huh huhev
    rwa [Nat.sub_add_cancel hj] at this
  cases hs : A.any (·.uniPoll pc) with
  | true =>
    exact hnot ⟨hs, ⟨dst, neg, tgt, _, base, off, par, acq, sc, hcb, hcw, rfl⟩, ug, uh, mg, pg,
      ph, okg, okh, acqg, acqh, scg, sch, hug, huh, hi, hj, hugev, huhev⟩
  | false =>
    have hs' : A.any (·.uniPoll (pc - 1 + 1)) = false := by rwa [Nat.sub_add_cancel h0]
    rcases hord _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hgh hw hxg hxh hs' with
      ⟨a, ha, hab⟩ | ⟨a, ha, hab⟩
    · exact hng ⟨a, _, by unfold Visit.events at hig ⊢; omega,
        by unfold Visit.events at hjh ⊢; omega, hab⟩
    · exact hnh ⟨a, _, by unfold Visit.events at hjh ⊢; omega,
        by unfold Visit.events at hig ⊢; omega, hab⟩

/-- **No warp-divergent execution** for a kernel whose guarded uniform instructions are the
branches of its wait loops or at positions `U` selects, when no execution diverges at the
positions of `U`, its local steps land at the next position or off the poll branches, and polls of
one position are ordered unless an assumption exempts them (`not_warpDivergent_synced` with the
positions of `U` split off). -/
theorem not_warpDivergent_synced' {U : Nat → Prop} {L : Launch} {K : Kernel}
    {A : List Assumption} {X : Execution}
    (hK : ∀ pc ins, K.code[pc]? = some ins → ins.laneCompared = true →
      K.pollBranch pc = true ∨ U pc)
    (hU : ¬ WarpDivergentAt U L K A X) (hloc : LocalLands K A L)
    (hsync : PollSynced L K A X) : ¬ WarpDivergent L K A X := by
  intro hd
  obtain ⟨g, h, hg, hh, hgh, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, pc, vi, vj, hpb, hvi, hvj,
    hpi, hpj, hgrp, hdis, hng, hnh, hnot⟩ := warpDivergent_split hK hU hd
  obtain ⟨h0, -, dst, neg, tgt, base, off, par, acq, sc, hcb, hcw⟩ := pollBranch_spec hpb
  have hw : SameWarp L g h := by
    simpa [Kernel.uniformScopeAt, hcb, Op.uniformScope, SameUniformGroup] using hgrp
  have hpb1 : K.pollBranch vi.pc = true := by rw [hpi]; exact hpb
  obtain ⟨hi, ug, mg, pg, okg, acqg, scg, hug, hugev⟩ := hwg.poll_before_lands hloc hvi hpb1
  have hpb' : K.pollBranch vj.pc = true := by rw [hpj]; exact hpb
  obtain ⟨hj, uh, mh, ph, okh, acqh, sch, huh, huhev⟩ := hwh.poll_before_lands hloc hvj hpb'
  rw [hpj] at huhev
  rw [hpi] at hugev
  obtain ⟨hxg, -⟩ := hwg.event_get hpg hug hugev
  obtain ⟨hxh, -⟩ := hwh.event_get hph huh huhev
  have hig : Visit.events vg i = Visit.events vg (i - 1) + 1 := by
    have := Visit.events_succ hug hugev
    rwa [Nat.sub_add_cancel hi] at this
  have hjh : Visit.events vh j = Visit.events vh (j - 1) + 1 := by
    have := Visit.events_succ huh huhev
    rwa [Nat.sub_add_cancel hj] at this
  by_cases hs : mg = mh ∧ A.any (·.uniPoll pc) = true
  · obtain ⟨rfl, hs⟩ := hs
    exact hnot ⟨hs, ⟨dst, neg, tgt, _, base, off, par, acq, sc, hcb, hcw, rfl⟩, ug, uh, mg, pg,
      ph, okg, okh, acqg, acqh, scg, sch, hug, huh, hi, hj, hugev, huhev⟩
  · have hd : mg ≠ mh ∨ A.any (·.uniPoll (pc - 1 + 1)) = false := by
      rw [Nat.sub_add_cancel h0]
      by_cases hm : mg = mh
      · exact .inr (by simpa [hm] using hs)
      · exact .inl hm
    have hpb2 : K.pollBranch (pc - 1 + 1) = true := by rw [Nat.sub_add_cancel h0]; exact hpb
    rcases hsync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hgh hw hxg hxh hpb2 hd with
      ⟨a, ha, hab⟩ | ⟨a, ha, hab⟩
    · exact hng ⟨a, _, by unfold Visit.events at hig ⊢; omega,
        by unfold Visit.events at hjh ⊢; omega, hab⟩
    · exact hnh ⟨a, _, by unfold Visit.events at hjh ⊢; omega,
        by unfold Visit.events at hig ⊢; omega, hab⟩

end

end PTX
