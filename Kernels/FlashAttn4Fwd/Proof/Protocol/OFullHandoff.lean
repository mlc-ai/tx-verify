-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.OAccReady
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ScoreSFullUnits

@[expose] public section

/-! # The O-full handoff

Stage `st`'s O-full object of a CTA (count 1) is completed by the notifications of the MMA
thread's commits, multicast over the pair, and polled by the CTA's correction threads. Like the
S-full objects it is a commit object of the pair's committing thread (`Score.fullObj`: `OFullFacts`,
`TmemFacts`, its initialization `OFullInit`, the commit premise `FullCommit`).

**OFullHandoff** (`oFullHandoff`): a correction poll of the object with `u` earlier successful
polls observes the notification of the commit with `u` earlier commits
(`MbarRing.Notify.Obj.observes`), by an acquire poll at cluster scope of a thread of the
committing thread's pair (`OFullFacts.o_poll`). The enabling paths of the object's reuse (the
commit of an item is enabled by the correction's polls for the earlier items) are the premise
`OFullReach`. The commit premise is `OFullFacts.o_commit` (`oFullCommit`,
`oFullHandoff_of_facts`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

namespace OAcc
open Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **The reuse premise** of the O-full objects: each correction thread's polls of stage `st`'s
O-full object for the uses before `t` enable the recorded notification of a commit with `t`
earlier commits to the object. -/
def OFullReach (L : Launch) (K : Kernel) (X : Execution) : Prop :=
  ∀ h st, h < L.threads → 8 ≤ warpOf L h → warpOf L h < 12 → st < 2 →
    ∀ (y : EvId) (rank : Fin 16), (∃ r ∈ X.objects (oFullBar L (ctaOf L h) st),
      r.id = .async y (.tcNotify rank) ∧ r.fault = none) →
    ∀ j < oCommits L X y.1 st y.2,
      Relation.TransGen (DepStep L K X)
        (.thread (h, MbarRing.Poll.nth X (oFullBar L (ctaOf L h) st) h j), true)
        (.async y (.tcNotify rank), false)

/-- **OFullHandoff** from the reuse of the O-full objects. -/
theorem oFullHandoff (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X)
    (ho : OFullFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (hinit : OFullInit L X)
    (hcom : FullCommit L X (oFullBar L)) (hR : OFullReach L K X) : OFullHandoff L X := by
  intro h j pc p st acq sc hh h8 h12 hst hget
  obtain ⟨-, -, -, -, hok⟩ := ho.o_poll hh hst hget
  obtain ⟨rfl, rfl⟩ := hok rfl
  obtain ⟨g, O⟩ := fullObj hX htm hcom hst (hinit _ _ hst) (ho.o_arrive hst) (ho.o_tensor hst)
    (fun he => (ho.o_poll (event_thread_lt hX he) hst he).2.2.2.1)
  have hRe := MbarRing.Notify.Reach.of_records (A := A) O (h := h)
    (fun i rank hrec j hj => hR h st hh h8 h12 hst (g, i) rank hrec j hj)
  obtain ⟨i, pc', sp, rank, hgi, -, ht, hc, hrank, hwo⟩ := O.observes hX hRe hget rfl
  have hcta : leadCta (ctaOf L g) = leadCta (ctaOf L h) := by
    have hcl := hi.commit_cluster hgi ht
    simp only [oFullBar] at hcl
    unfold leadCta
    omega
  have hgl := event_thread_lt hX hgi
  refine ⟨(g, i), sp, rank, .cluster, ⟨pc', hgi⟩, hcta,
    (hcom hst ⟨pc', hgi⟩ ⟨pc', hgi⟩ ht ht rfl).1, hc, ht, hrank, hwo, ?_⟩
  exact ⟨sameCluster_of_pair hpre hgl hh hcta, sameCluster_of_pair hpre hh hgl hcta.symm⟩

/-- **The commit premise of the O-full objects.** -/
theorem oFullCommit (hX : Consistent L K A mem0 X) (ho : OFullFacts L X) :
    FullCommit L X (oFullBar L) :=
  fullCommit_of hX ho.o_commit

/-- **OFullHandoff** from the reuse of the O-full objects, with the commit premise from
`OFullFacts.o_commit`. -/
theorem oFullHandoff_of_facts (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X)
    (ho : OFullFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (hinit : OFullInit L X)
    (hR : OFullReach L K X) : OFullHandoff L X :=
  oFullHandoff hpre hX ho htm hi hinit (oFullCommit hX ho) hR

end OAcc

end
end PTX.Kernels.FlashAttn4Fwd.Proof
