-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.ScoreHandoff
public import Kernels.FlashAttn4Fwd.Proof.Protocol.PReadyObj

@[expose] public section

/-! # The S-full handoff from the object's attribution

Stage `st`'s S-full object of a CTA (count 1) is completed by the notifications of the MMA
thread's commits, multicast over the pair, and polled by the CTA's softmax threads of the stage.
**SFull** (`Score.SFullHandoff`): the softmax poll with `u` earlier successful polls observes the
notification of the commit with `u` earlier commits.

It follows (`sFullHandoff`) from the attribution of the object's phases as each softmax thread
polls it (`SFullUnits`, a `MbarRing.Multi.Units` with one kind: unit `t` is the notification on
the thread's S-full object of the commit with `t` earlier commits; its consumer's poll for use `j`
is its successful poll with `j` earlier ones): the poll for use `u` observes unit `u`
(`Units.observes`), an observation that is the object's (`Observed.waitObserves_tcNotify`), by an
acquire poll at cluster scope of a thread of the committing thread's pair (`SFullFacts.s_poll`).

`SFullUnits` holds the object's history facts (each poll observes a completed phase and every
notification in it, a phase holds a notification, later polls observe later phases: the count-1
commit object's `UnitItems`) and the reuse paths (the commit of tile `t` is enabled by every
softmax poll for a tile before `t`, through the P-ready object), which it shares with
`PReadyReach`; it is the premise. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **The attribution premise of the S-full objects**: each softmax thread's polls of its stage's
S-full object, read as units of one kind whose unit `t` is the notification on that object of the
commit with `t` earlier commits to the stage's object of its CTA, by a thread of the pair. -/
def SFullUnits (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ h, h < L.threads → warpOf L h < 8 → ∃ U : MbarRing.Multi.Units L K A X (Fin 1),
    (∀ j, U.w j = (h, MbarRing.Poll.nth X (sFullBar L (ctaOf L h) (warpOf L h / 4)) h j)) ∧
    (∀ k t, U.use k t = t) ∧
    ∀ x ∈ U.S, ∃ y s rank, U.it x.1 x.2 = .async y (.tcNotify rank) ∧ X.Commit y s ∧
      leadCta (ctaOf L y.1) = leadCta (ctaOf L h) ∧
      s.mbar = sFullBar L (ctaOf L y.1) (warpOf L h / 4) ∧
      sCommits L X y.1 (warpOf L h / 4) y.2 = x.2 ∧
      TcCommit.target s rank = some (sFullBar L (ctaOf L h) (warpOf L h / 4))

/-- **SFull** from the attribution of the S-full objects. -/
theorem sFullHandoff (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (hs : SFullFacts L X)
    (hU : SFullUnits L K A X) : SFullHandoff L X := by
  intro h j pc p acq sc hh hw hget
  set m := sFullBar L (ctaOf L h) (warpOf L h / 4)
  have hst : warpOf L h / 4 < 2 := by omega
  obtain ⟨-, -, -, -, hok⟩ := hs.s_poll hh hst hget
  obtain ⟨rfl, rfl⟩ := hok rfl
  obtain ⟨U, hUw, hUu, hUit⟩ := hU h hh hw
  have hjn : MbarRing.Poll.nth X m h (sPolls L X h (warpOf L h / 4) j) = j :=
    MbarRing.Poll.nth_eq hget
  have hpw : X.RefPresent (.thread (U.w (sPolls L X h (warpOf L h / 4) j))) := by
    rw [hUw, hjn]
    exact ⟨_, hget⟩
  obtain ⟨t, hS, ht, hobs⟩ := U.observes (DepStepAcyclic.of_dependency hX.dependency) hpw 0
  rw [hUu] at ht
  subst ht
  obtain ⟨y, s, rank, hit, hcom, hcta, hmbar, hcnt, htgt⟩ := hUit _ hS
  rw [hit, hUw, hjn] at hobs
  obtain ⟨hrank, hwo⟩ := hobs.waitObserves_tcNotify hget
  obtain ⟨pcy, hy⟩ := hcom
  have hyl := event_thread_lt hX hy
  refine ⟨y, s, rank, .cluster, ⟨pcy, hy⟩, hcta, hmbar, hcnt, htgt, hrank, hwo, ?_⟩
  exact ⟨sameCluster_of_pair hpre hyl hh hcta, sameCluster_of_pair hpre hh hyl hcta.symm⟩

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
