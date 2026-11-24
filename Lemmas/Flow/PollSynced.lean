-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PollLands

@[expose] public section

/-! # Polls of one position that disagree are ordered

ERR-NONUNIFORM-GUARD compares two lanes' evaluations of a poll branch unless the
execution-dependency order (`DepBefore`, EXT-DEPENDENCY-ORDER) orders them, or a kernel assumption
selects the branch with `uniPoll` and the polls right before are of one mbarrier
(`PollAgreeExempt`, ASM-POLL-AGREE). A kernel whose ring polls compute their slot from the
iteration polls different objects at one position in different iterations, so `PollObjUniform`
(one object per position) does not hold for it. What the rule needs is weaker (`PollSynced`): two
distinct lanes of a warp polling at one position followed by a poll branch, different objects or
at a branch no assumption selects, are ordered (`PollBefore`: an event one lane performs after
its poll precedes the other lane's poll in `DepBefore`). With the code facts it suffices
(`not_warpDivergent_synced`). -/

namespace PTX

noncomputable section

/-- The poll `e` is ordered before the poll `f`: an event `e`'s thread performs after `e`
precedes `f` in the execution-dependency order. -/
def PollBefore (L : Launch) (K : Kernel) (X : Execution) (e f : EvId) : Prop :=
  ∃ a, e.2 < a ∧ DepBefore L K X (e.1, a) f

/-- Two distinct lanes of a warp polling at one position whose next instruction is a poll branch
(`Kernel.pollBranch`: a guarded `bra.uni` on the poll's predicate; ERR-NONUNIFORM-GUARD constrains
no other branch after a poll), different objects or at a branch that no assumption selects with
`uniPoll`, are ordered. -/
def PollSynced (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ g h k k' pc m m' p p' ok ok' acq acq' sc sc', g < L.threads → h < L.threads → g ≠ h →
    SameWarp L g h → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
    X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ → K.pollBranch (pc + 1) = true →
    (m ≠ m' ∨ A.any (·.uniPoll (pc + 1)) = false) →
    PollBefore L K X (g, k) (h, k') ∨ PollBefore L K X (h, k') (g, k)

/-- **No warp-divergent execution** for a kernel whose guarded uniform instructions are the
branches of its wait loops, when its local steps land at the next position or off the poll
branches and polls of one position are ordered unless an assumption exempts them. -/
theorem not_warpDivergent_synced {L : Launch} {K : Kernel} {A : List Assumption}
    {X : Execution} (hK : K.pollGuardsOk = true) (hloc : LocalLands K A L)
    (hsync : PollSynced L K A X) : ¬ WarpDivergent L K A X := by
  rintro ⟨g, h, hg, hh, hgh, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, pc, vi, vj, hvi, hvj,
    hpi, hpj, hgrp, hdis, hng, hnh, hnot⟩
  obtain ⟨s, ev, rfl⟩ := hwg.state hvi
  obtain ⟨ins, hins, hl⟩ : ∃ ins, K.code[s.pc]? = some ins ∧ ins.laneCompared = true := by
    rcases hdis with ⟨b, -, hb, -, -⟩ | ⟨x, -, hx, -, -⟩
    · exact visit_compared_guard hb
    · exact visit_compared_index hx
  have hpb := pollGuardsOk_lane hK hins hl
  simp only [visit_pc] at hpi
  subst hpi
  obtain ⟨h0, -, dst, neg, tgt, base, off, par, acq, sc, hcb, hcw⟩ := pollBranch_spec hpb
  have hw : SameWarp L g h := by
    simpa [Kernel.uniformScopeAt, hcb, Op.uniformScope, SameUniformGroup] using hgrp
  obtain ⟨hi, ug, mg, pg, okg, acqg, scg, hug, hugev⟩ := hwg.poll_before_lands hloc hvi hpb
  have hpb' : K.pollBranch vj.pc = true := by rw [hpj]; exact hpb
  obtain ⟨hj, uh, mh, ph, okh, acqh, sch, huh, huhev⟩ := hwh.poll_before_lands hloc hvj hpb'
  rw [hpj] at huhev
  simp only [visit_pc] at hugev
  obtain ⟨hxg, -⟩ := hwg.event_get hpg hug hugev
  obtain ⟨hxh, -⟩ := hwh.event_get hph huh huhev
  have hig : Visit.events vg i = Visit.events vg (i - 1) + 1 := by
    have := Visit.events_succ hug hugev
    rwa [Nat.sub_add_cancel hi] at this
  have hjh : Visit.events vh j = Visit.events vh (j - 1) + 1 := by
    have := Visit.events_succ huh huhev
    rwa [Nat.sub_add_cancel hj] at this
  by_cases hs : mg = mh ∧ A.any (·.uniPoll s.pc) = true
  · obtain ⟨rfl, hs⟩ := hs
    exact hnot ⟨hs, ⟨dst, neg, tgt, _, base, off, par, acq, sc, hcb, hcw, rfl⟩, ug, uh, mg, pg,
      ph, okg, okh, acqg, acqh, scg, sch, hug, huh, hi, hj, hugev, huhev⟩
  · have hd : mg ≠ mh ∨ A.any (·.uniPoll (s.pc - 1 + 1)) = false := by
      rw [Nat.sub_add_cancel h0]
      by_cases hm : mg = mh
      · exact .inr (by simpa [hm] using hs)
      · exact .inl hm
    have hpb1 : K.pollBranch (s.pc - 1 + 1) = true := by rw [Nat.sub_add_cancel h0]; exact hpb
    rcases hsync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hgh hw hxg hxh hpb1 hd with
      ⟨a, ha, hab⟩ | ⟨a, ha, hab⟩
    · exact hng ⟨a, _, by unfold Visit.events at hig ⊢; omega,
        by unfold Visit.events at hjh ⊢; omega, hab⟩
    · exact hnh ⟨a, _, by unfold Visit.events at hjh ⊢; omega,
        by unfold Visit.events at hig ⊢; omega, hab⟩

end

end PTX
