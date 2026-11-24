-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.ScoreSFull
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ScoreBlocked
public import Kernels.FlashAttn4Fwd.Proof.Interface.Init
public import Lemmas.Protocol.UnitNotify
public import Lemmas.Flow.ElectActor

@[expose] public section

/-! # The attribution of the S-full objects

Stage `st`'s S-full object of a CTA (count 1) is completed by the notifications of commits only
(`SFullFacts`: no thread arrives, no copy completes on it; `TmemFacts`: no bulk copy,
cancellation request or invalidation), and its history starts with its only initialization
(`SFullInit`). With the commit premise (`FullCommit`: a commit notifying it names the stage's
object of its own CTA, and the commits notifying one pair's objects of a stage are one thread's)
it is a commit object (`MbarRing.Notify.Obj`, offset 0) of that thread (`fullObj`, shared with
the O-full objects). The commit premise holds of a family whose commits are each the elected
lane's of warp 12 of the pair leader, naming the stage's object of its own CTA
(`fullCommit_of`): the elected lanes of one warp are one thread (`selected_elect_thread_unique`).
For the S-full objects that is `SFullFacts.s_commit` (`sFullCommit`).

**SFullUnits** (`sFullUnits`): each softmax thread's polls of its stage's S-full object read as
the object's units (`MbarRing.Notify.Obj.units`): the observation of a phase and every unit of
it, a phase holding a unit, later polls observing later phases come from the object's history;
the units are commit notifications of the pair's thread (`InitFacts.commit_cluster`) whose
counter is `sCommits`. The enabling paths of the object's reuse (the commit of tile `t` is
enabled by every softmax poll for a tile before `t`, through the P-ready object) are the
premise `SFullReach`, shared with `PReadyReach`'s joint induction. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

namespace Score

variable {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel} {A : List Assumption}

/-- **The commit premise** of a family `bar c st` of objects completed by commits (the S-full
and O-full objects): a commit notifying stage `st`'s object of a CTA names the stage's object of
its own CTA, and the commits notifying stage `st`'s objects of one pair are one thread's. -/
def FullCommit (L : Launch) (X : Execution) (bar : Nat → Nat → Loc) : Prop :=
  ∀ {y y' : EvId} {s s' : TcCommit.Spec} {r r' : Fin 16} {c c' st : Nat}, st < 2 →
    X.Commit y s → X.Commit y' s' → TcCommit.target s r = some (bar c st) →
    TcCommit.target s' r' = some (bar c' st) → leadCta c = leadCta c' →
      s.mbar = bar (ctaOf L y.1) st ∧ y'.1 = y.1

/-- **The commit premise from the committing lanes**: when every commit notifying stage `st`'s
object of a CTA `c` is a thread's of warp 12 of `c`'s pair leader, after a full-mask election
that returned its lane, and names the stage's object of its own CTA, the commits notifying one
pair's objects of a stage are one thread's. -/
theorem fullCommit_of (hX : Consistent L K A mem0 X) {bar : Nat → Nat → Loc}
    (hcom : ∀ {g k pc c st : Nat} {sp : TcCommit.Spec} {r : Fin 16}, g < L.threads → st < 2 →
      X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some (bar c st) →
        warpOf L g = 12 ∧ leadCta c = ctaOf L g ∧ LeadAt L X g k ∧
          sp.mbar = bar (ctaOf L g) st) :
    FullCommit L X bar := by
  intro y y' s s' r r' c c' st hst ⟨pc, hy⟩ ⟨pc', hy'⟩ ht ht' hc
  have hg := event_thread_lt hX hy
  have hg' := event_thread_lt hX hy'
  obtain ⟨hw, hl, ⟨j, -, pj, ij, hj⟩, hm⟩ := hcom hg hst hy ht
  obtain ⟨hw', hl', ⟨j', -, pj', ij', hj'⟩, -⟩ := hcom hg' hst hy' ht'
  refine ⟨hm, (selected_elect_thread_unique hX.elect hj hj' ?_ rfl rfl).symm⟩
  refine ⟨⟨hg, hg', ?_⟩, ?_⟩
  · show ctaOf L y.1 = ctaOf L y'.1
    rw [← hl, ← hl', hc]
  · show warpOf L y.1 = warpOf L y'.1
    rw [hw, hw']

/-- **The commit premise of the S-full objects.** -/
theorem sFullCommit (hX : Consistent L K A mem0 X) (hs : SFullFacts L X) :
    FullCommit L X (sFullBar L) :=
  fullCommit_of hX hs.s_commit

/-- **The reuse premise** of the S-full objects: each softmax thread's polls of its stage's
S-full object for the uses before `t` enable the recorded notification of a commit with `t`
earlier commits to the object. -/
def SFullReach (L : Launch) (K : Kernel) (X : Execution) : Prop :=
  ∀ h, h < L.threads → warpOf L h < 8 → ∀ (y : EvId) (rank : Fin 16),
    (∃ r ∈ X.objects (sFullBar L (ctaOf L h) (warpOf L h / 4)),
      r.id = .async y (.tcNotify rank) ∧ r.fault = none) →
    ∀ j < sCommits L X y.1 (warpOf L h / 4) y.2,
      Relation.TransGen (DepStep L K X)
        (.thread (h, MbarRing.Poll.nth X (sFullBar L (ctaOf L h) (warpOf L h / 4)) h j), true)
        (.async y (.tcNotify rank), false)

/-- **An object of the family completed by commits alone is a commit object** of the thread
that commits to it. -/
theorem fullObj (hX : Consistent L K A mem0 X) (htm : TmemFacts L X) {bar : Nat → Nat → Loc}
    (hcom : FullCommit L X bar) {c st : Nat} (hst : st < 2)
    (hinit : PairTmaRing.InitFirst X (bar c st) 1)
    (harr : ∀ {g i pc tx cnt : Nat} {rel : Bool} {sc : MbarScope},
      X.get (g, i) ≠ some ⟨pc, .arrive (bar c st) tx cnt rel sc⟩)
    (hten : ∀ {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec},
      X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ bar c st)
    (hpar : ∀ {h k pc p : Nat} {acq : Bool} {sc : MbarScope},
      X.get (h, k) = some ⟨pc, .wait (bar c st) p true acq sc⟩ →
        p % 2 = okPolls (bar c st) ((X.tr h).take k) % 2) :
    ∃ g, MbarRing.Notify.Obj X (bar c st) g (bar (ctaOf L g) st) 0 := by
  have hg : ∃ g, ∀ {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {r : Fin 16},
      X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some (bar c st) →
        i.1 = g ∧ sp.mbar = bar (ctaOf L g) st := by
    by_cases hex : ∃ (i : EvId) (pc : Nat) (sp : TcCommit.Spec) (r : Fin 16),
        X.get i = some ⟨pc, .tc (.commit sp)⟩ ∧ TcCommit.target sp r = some (bar c st)
    · obtain ⟨i, pc, sp, r, he, ht⟩ := hex
      refine ⟨i.1, fun {i'} {pc'} {sp'} {r'} he' ht' => ?_⟩
      have h1 := (hcom hst ⟨pc, he⟩ ⟨pc', he'⟩ ht ht' rfl).2
      have h2 := (hcom hst ⟨pc', he'⟩ ⟨pc', he'⟩ ht' ht' rfl).1
      rw [h1] at h2
      exact ⟨h1, h2⟩
    · exact ⟨0, fun he ht => (hex ⟨_, _, _, _, he, ht⟩).elim⟩
  obtain ⟨g, hg⟩ := hg
  exact ⟨g, MbarRing.Notify.Obj.of_commits hX hinit harr hten (fun he => (htm.no_bulk he).elim)
    (fun he => (htm.no_arriveOn he).elim) htm.no_clc htm.no_inval hg
    (fun he => by simpa using hpar he) (Nat.zero_le _)⟩

/-- **SFullUnits** from the reuse of the S-full objects. -/
theorem sFullUnits (hX : Consistent L K A mem0 X) (hs : SFullFacts L X) (htm : TmemFacts L X)
    (hi : InitFacts L X) (hinit : SFullInit L X) (hcom : FullCommit L X (sFullBar L))
    (hR : SFullReach L K X) : SFullUnits L K A X := by
  intro h hh hw
  have hst : warpOf L h / 4 < 2 := by omega
  obtain ⟨g, O⟩ := fullObj hX htm hcom hst (hinit _ _ hst) (hs.s_arrive hst) (hs.s_tensor hst)
    (fun he => (hs.s_poll (event_thread_lt hX he) hst he).2.2.2.1)
  have hRe := MbarRing.Notify.Reach.of_records (A := A) O (h := h)
    (fun i rank hrec j hj => hR h hh hw (g, i) rank hrec j hj)
  refine ⟨O.units hX h hRe, fun j => rfl, fun k t => rfl, fun x hx => ?_⟩
  obtain ⟨-, pc, sp, hget, -, ht, hc⟩ := O.S_rec hx
  refine ⟨_, sp, _, rfl, ⟨pc, hget⟩, ?_, (hcom hst ⟨pc, hget⟩ ⟨pc, hget⟩ ht ht rfl).1, hc, ht⟩
  have hcl := hi.commit_cluster hget ht
  simp only [sFullBar] at hcl
  show leadCta (ctaOf L g) = _
  unfold leadCta
  omega

/-- **SFullUnits** from the reuse of the S-full objects, with the commit premise from
`SFullFacts.s_commit`. -/
theorem sFullUnits_of_facts (hX : Consistent L K A mem0 X) (hs : SFullFacts L X)
    (htm : TmemFacts L X) (hi : InitFacts L X) (hinit : SFullInit L X)
    (hR : SFullReach L K X) : SFullUnits L K A X :=
  sFullUnits hX hs htm hi hinit (sFullCommit hX hs) hR

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
