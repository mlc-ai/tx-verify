-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Guard
public import Lemmas.Flow.PollSynced
public import Lemmas.Flow.PollRounds

@[expose] public section

/-! # Uniform poll branches when a loop polls a different object each pass

A proof tool, generic over the kernel (Inkling request L-o). `not_warpDivergent_pollAgree` asks
that each poll position polls one object across a warp (`PollObjUniform`). A poll inside a loop
whose object is a function of the iteration (a ring slot `i % depth`, a buffer `i % 2`) polls a
different object at one position in different passes, so `PollObjUniform` is false for it.

Here the polls carry a key (`key : EvId → Nat`, the kernel's choice: the pass of the loop, read
off the thread's machine state or counted on the trace). Two premises replace `PollObjUniform`:

* `PollObjAt key`: two polls at one position by lanes of one warp with equal keys name one object
  (the object is a function of the pass);
* `PollKeyOrdered key`: two polls at one position followed by a poll branch, by two lanes of one
  warp with different keys and different objects, are ordered (`PollBefore`), the order the
  kernel's hand-off gives between passes. With the round of a poll (`pollRound`, its successful
  polls at the position) as key it is `PollRoundsMet` (`PollKeyOrdered.of_roundsMet`), which
  `PollRoundsMet.of_collectives` derives from per-round warp collectives.

With them, a disagreeing pair at a poll branch selected by the `pollAgree` assumption is either of
one object (exempt, ASM-POLL-AGREE) or ordered (`not_warpDivergent_pollAgree_key`). -/

namespace PTX

open PTX.Proof

noncomputable section

variable {U : Nat → Prop} {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}

/-- Two polls at one position by lanes of one warp whose keys are equal name one object. -/
def PollObjAt (L : Launch) (X : Execution) (key : EvId → Nat) : Prop :=
  ∀ g h k k' pc m m' p p' ok ok' acq acq' sc sc', g < L.threads → h < L.threads →
    SameWarp L g h → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
    X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ → key (g, k) = key (h, k') → m = m'

/-- Two polls at one position followed by a poll branch, by two lanes of one warp with different
keys and different objects, are ordered. -/
def PollKeyOrdered (L : Launch) (K : Kernel) (X : Execution) (key : EvId → Nat) : Prop :=
  ∀ g h k k' pc m m' p p' ok ok' acq acq' sc sc', g < L.threads → h < L.threads → g ≠ h →
    SameWarp L g h → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
    X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ → K.pollBranch (pc + 1) = true →
    key (g, k) ≠ key (h, k') → m ≠ m' →
    PollBefore L K X (g, k) (h, k') ∨ PollBefore L K X (h, k') (g, k)

/-- **The round of a poll as its key**: lanes in different rounds met (`PollRoundsMet`) are
ordered. -/
theorem PollKeyOrdered.of_roundsMet {A : List Assumption} (key : EvId → Nat)
    (hkey : ∀ g k pc m p ok acq sc, X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      key (g, k) = pollRound pc ((X.tr g).take k))
    (h : PollRoundsMet L K A X) : PollKeyOrdered L K X key := by
  intro g h' k k' pc m m' p p' ok ok' acq acq' sc sc' hg hh hgh hw hx hx' hpb hk hm
  rw [hkey _ _ _ _ _ _ _ _ hx, hkey _ _ _ _ _ _ _ _ hx'] at hk
  rcases Nat.lt_or_gt_of_ne hk with hlt | hlt
  · exact .inl (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hgh hw hx hx' hpb (.inl hm) hlt)
  · exact .inr (h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh hg (Ne.symm hgh) hw.symm hx' hx hpb
      (.inl (Ne.symm hm)) hlt)

/-- One object at every position is the case of a constant key. -/
theorem PollObjAt.of_uniform (h : PollObjUniform L X) (key : EvId → Nat) : PollObjAt L X key :=
  fun g h' k k' pc m m' p p' ok ok' acq acq' sc sc' hg hh hw hx hx' _ =>
    h g h' k k' pc m m' p p' ok ok' acq acq' sc sc' hg hh hw hx hx'

/-- **No warp-divergent execution under a `pollAgree` assumption, with keyed polls**: as
`not_warpDivergent_pollAgree`, where polls of equal keys name one object and polls of different
keys and objects are ordered. -/
theorem not_warpDivergent_pollAgree_key (key : EvId → Nat)
    (hK : ∀ pc ins, K.code[pc]? = some ins → ins.laneCompared = true →
      K.pollBranch pc = true ∨ U pc)
    (hU : ¬ WarpDivergentAt U L K A X)
    (hloc : ∀ g t op t', execLocalA A L g t op = .ok t' → LocalFrame op t t')
    (hobj : PollObjAt L X key) (hord : PollKeyOrdered L K X key)
    (hsel : ∀ pc, K.pollBranch pc = true → A.any (·.uniPoll pc) = true) :
    ¬ WarpDivergent L K A X := by
  intro hd
  obtain ⟨g, h, hg, hh, hgh, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, pc, vi, vj, hpb, hvi, hvj,
    hpi, hpj, hgrp, -, hng, hnh, hnot⟩ := warpDivergent_split hK hU hd
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
  by_cases hm : mg = mh
  · subst hm
    exact hnot ⟨hsel pc hpb, ⟨dst, neg, tgt, _, base, off, par, acq, sc, hcb, hcw, rfl⟩, ug, uh,
      mg, pg, ph, okg, okh, acqg, acqh, scg, sch, hug, huh, hi, hj, hugev, huhev⟩
  · have hk := fun he => hm (hobj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hw hxg hxh he)
    have hig : Visit.events vg i = Visit.events vg (i - 1) + 1 := by
      have := Visit.events_succ hug hugev
      rwa [Nat.sub_add_cancel hi] at this
    have hjh : Visit.events vh j = Visit.events vh (j - 1) + 1 := by
      have := Visit.events_succ huh huhev
      rwa [Nat.sub_add_cancel hj] at this
    have hpb0 : K.pollBranch (pc - 1 + 1) = true := by rwa [Nat.sub_add_cancel h0]
    rcases hord _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hgh hw hxg hxh hpb0 hk hm with
      ⟨a, ha, hab⟩ | ⟨a, ha, hab⟩
    · exact hng ⟨a, _, by unfold Visit.events at hig ⊢; simp only at ha; omega,
        by unfold Visit.events at hjh ⊢; omega, hab⟩
    · exact hnh ⟨a, _, by unfold Visit.events at hjh ⊢; simp only at ha; omega,
        by unfold Visit.events at hig ⊢; omega, hab⟩

end

end PTX
