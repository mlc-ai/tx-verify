-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc

@[expose] public section

/-! # The commit branch of `Unsafe`

A commit is the MMA warp's of a leader CTA, to a table barrier `b` of its CTA (S-full, KV-empty,
Q-empty or O-full), over the pair from its CTA with mask 3 (`TcFacts.commit_spec`). So:

* **The issue** (`commit_issue_safe`): it resolves as issued, since the pair is the issuer's
  cluster (`L.clusterSize = 2`), and the CTA group of two lies in the cluster.
* **A target** (`commit_target_published`, the commit case of `MbarUninit`): the target of rank
  `r < 2` is `b` in CTA `c + r` of the pair, whose initialization is published to the commit
  (`PairInit`).

`PairInit` is the cluster start's export: an event after the start follows the start cluster
barrier, whose wait observed every arrival of the cluster, so each thread of warp 0 of each CTA of
the pair reached its arrival; its thread 0, or the lane an election before it returned,
initialized every barrier but the handshake barrier before it (`TcFacts.init_done`), and the
start barrier publishes every initialization to every later event of the cluster
(`ClusterStart.init_published`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof TcCommit

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **PairInit**: every barrier but the handshake barrier of each CTA of the pair of an event
after the start has an initialization published to the event. -/
def PairInit (L : Launch) (X : Execution) : Prop :=
  ∀ {g j cta : Nat} {ev : Event} {b : FBar}, X.get (g, j) = some ev → ¬ PreKind ev.kind →
    (∀ f, ev.kind ≠ .ub f) → b ≠ .dealloc → ctaOf L g / 2 = cta / 2 →
      ∃ e n, X.MbInit e (b.loc L cta) n ∧ InitPublished L X e (g, j) (b.loc L cta)

/-- **A commit's issue is safe.** -/
theorem commit_issue_safe (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : TcFacts L X) {i : EvId} {s : Spec} (hc : X.Commit i s) : TcCommitIssueSafe L i s := by
  obtain ⟨pc, he⟩ := hc
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, hev, b, -, rfl⟩ := ht.commit_spec hg he
  have hone := hpre.oneDimLaunch.1
  have hblock := hpre.block
  have hcl := hpre.cluster
  have hgrid := hpre.grid
  have hcta := cta_lt hg
  unfold ctaOf at hev hcta
  refine ⟨hg, ?_, ?_⟩
  · unfold TcCommit.resolve
    split_ifs with hc'
    · simp only [Launch.oneDim_clusterStart hone, Launch.oneDim_clusterOfCta hone,
        Launch.oneDim_clusterSizeOf hone, hcl, ctaOf, Option.some.injEq, Spec.mk.injEq,
        true_and, and_true]
      omega
    · exfalso
      refine hc' ⟨Launch.oneDimLaunch_clusterGridValid hpre.oneDimLaunch, hcta, rfl, hcta, rfl,
        ?_⟩
      simp only [Launch.oneDim_clusterSizeOf hone, hcl]
      decide
  · rw [Launch.ctaGroup_ne_none_iff L _ _ hcta (fun r hr => by
      simp only [Launch.oneDim_clusterSizeOf hone, Launch.oneDim_clusterStart hone,
        Launch.oneDim_clusterOfCta hone, hcl] at hr ⊢
      omega)]
    simp only [Launch.oneDim_rankOfCta hone, Launch.oneDim_clusterSizeOf hone, hcl,
      CtaGroup.size]
    omega

/-- **A commit's targets are initialized and published to it**: the target of rank `r < 2` is
barrier `b` of CTA `c + r` of the pair, whose initialization is published to the commit
(`PairInit`). This is the commit case of `MbarUninit`. -/
theorem commit_target_published (hX : Consistent L kernel asms mem0 X) (ht : TcFacts L X)
    (hpi : PairInit L X) {i : EvId} {s : Spec} {rank : Fin 16} {m : Loc} (hc : X.Commit i s)
    (htg : target s rank = some m) : ∃ e n, X.MbInit e m n ∧ InitPublished L X e i m := by
  obtain ⟨pc, he⟩ := hc
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, hev, b, hb, rfl⟩ := ht.commit_spec hg he
  unfold TcCommit.target at htg
  split_ifs at htg with hr
  cases htg
  have hr2 : rank.val < 2 := hr.1
  have hm : (⟨.shared, ctaOf L i.1 + rank.val, (b.loc L (ctaOf L i.1)).addr⟩ : Loc) =
      b.loc L (ctaOf L i.1 + rank.val) := rfl
  rw [hm]
  exact hpi (g := i.1) (j := i.2) he (by simp [PreKind]) (by simp) hb
    (cta := ctaOf L i.1 + rank.val) (by omega)

/-- **No commit is unsafe**: every commit's issue is safe. -/
theorem no_commit_unsafe (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : TcFacts L X) : ¬ TcCommitUnsafe L X := by
  rintro ⟨i, s, hc, hn⟩
  exact hn (commit_issue_safe hpre hX ht hc)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
