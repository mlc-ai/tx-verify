-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TcWrites
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Cluster.ClusterBarrierExecution
public import Lemmas.Kernel.SharedLifetime

@[expose] public section

/-! # The commit branch of `Unsafe`, from the interface

A commit is the MMA thread's, on a leader CTA (`ThreadFacts.commit_spec`): a slot's commit to
its input empty barrier, or the accumulator commit to its buffer's full barrier, both with the
pair's mask, so they resolve as issued and target that barrier in both CTAs of the pair.

* The issue (`commit_issue_safe`): it resolves as issued, in a CTA group within the cluster.
  Its targets' initialization is the mbarrier branch's (`no_mbarUninit`).
* The CTA group's shared memory (`commit_group_lifetime`): each CTA of the pair started before the
  commit, as its thread 0's initialization of the barrier is published to the commit
  (`ThreadFacts.ring_initialized`, `started_of_published`), and if it exited, the commit happened
  before its exit, as the commit comes before the MMA thread's exit arrival (`ExitOrder`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX TcCommit

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An initialization published to an event by base causality: the initializer's completion
precedes the event's issue. -/
theorem started_of_published {init user : EvId} (hi : ∃ ev, X.get init = some ev)
    (hp : baseCausality L X init user) :
    ∃ start ev, start.1 / L.block = init.1 / L.block ∧ X.get start = some ev ∧
      LifetimeOrder L kernel Prod X (.thread start, true) (.thread user, false) := by
  obtain ⟨ev, he⟩ := hi
  exact ⟨init, ev, rfl, he, LifetimeOrder.of_baseCausality hp⟩

/-- A commit of the kernel: the MMA thread's, on a leader CTA, of one of its two specifications. -/
theorem commit_source (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {i : EvId}
    {s : Spec} (hc : X.Commit i s) :
    i.1 < L.threads ∧ i.1 / L.block % 2 = 0 ∧ (∃ ev, X.get i = some ev) ∧
      ∃ m : Mma.D, Frame.stateAt (code L) X i.1 i.2 = some (some (.inr (.mma m))) ∧
      ((∃ sl : Fin 4, m.site = .commit sl ∧
          s = ⟨.two, ⟨.shared, i.1 / L.block, L.sharedBase + 40 + 8 * sl.val⟩, 3,
            i.1 / L.block / 2 * 2, 2⟩) ∨
        (m.site = .accCommit ∧ s = ⟨.two, ⟨.shared, i.1 / L.block,
          L.sharedBase + 8 * (i.1 % L.block / 32 % 2) + 72⟩, 3, i.1 / L.block / 2 * 2, 2⟩)) := by
  obtain ⟨pc, he⟩ := hc
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨m, rfl, hlead, hsp⟩ := ht.commit_spec hg he hσ rfl
  exact ⟨hg, hlead, ⟨_, he⟩, m, hσ, hsp⟩

/-- The barrier a commit of the kernel notifies, by its specification: in every CTA, the table's
barrier at the specification's offset. -/
theorem commit_bar (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {i : EvId}
    {s : Spec} (hc : X.Commit i s) :
    ∃ b : Bar, b.Valid ∧ s.mbar = Bar.loc L (i.1 / L.block) b ∧ s.group = .two ∧ s.mask = 3 ∧
      s.clusterBase = i.1 / L.block / 2 * 2 ∧ s.clusterSize = 2 := by
  obtain ⟨-, -, -, m, -, ⟨sl, -, rfl⟩ | ⟨-, rfl⟩⟩ := commit_source hX ht hc
  · exact ⟨⟨.input, sl.val, false⟩, sl.isLt, by simp [Bar.loc, Bar.off, Nat.add_assoc], rfl, rfl,
      rfl, rfl⟩
  · refine ⟨⟨.acc, i.1 % L.block / 32 % 2, true⟩, Nat.mod_lt _ (by decide), ?_, rfl, rfl, rfl, rfl⟩
    simp only [Bar.loc, Bar.off]
    congr 1
    omega

/-- **A commit's issue is safe.** -/
theorem commit_issue_safe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {i : EvId} {s : Spec} (hc : X.Commit i s) :
    TcCommitIssueSafe L i s := by
  obtain ⟨hg, -, -, -, -, -⟩ := commit_source hX ht hc
  obtain ⟨b, hb, hmb, hgrp, hmask, hcb, hcs⟩ := commit_bar hX ht hc
  have hblock := hpre.block
  have hcl := hpre.cluster
  have hgrid := hpre.grid
  have hcta : i.1 / L.block < L.grid := by
    simp only [Launch.threads] at hg
    rw [hblock] at hg ⊢
    omega
  refine ⟨hg, ?_, ?_⟩
  · obtain ⟨grp, mb, mk, cb, cs⟩ := s
    simp only at hmb hgrp hmask hcb hcs
    subst hmb hgrp hmask hcb hcs
    unfold TcCommit.resolve
    split_ifs with hc'
    · simp only [clusterStart_eq hpre, clusterOfCta_eq hpre, clusterSizeOf_eq hpre]
    · exact absurd ⟨Launch.oneDimLaunch_clusterGridValid hpre.oneDimLaunch, hcta, rfl, hcta, rfl,
        by rw [clusterSizeOf_eq hpre]; show (3 : BitVec 16).toNat < 2 ^ 2; decide⟩ hc'
  · rw [hgrp, Launch.ctaGroup_two, rankOfCta_eq hpre, peerCta_eq hpre hcta (by omega),
      peerCta_eq hpre hcta (by omega)]
    simp

/-- **A commit's use of its CTA group's shared memory is safe**: each CTA of the group started
before the commit, and if it exited, the commit finished before one of its exits. -/
theorem commit_group_lifetime (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hex : ExitOrder L X) {i : EvId} {s : Spec} (hc : X.Commit i s)
    {peer : Nat} (hpeer : SameCtaGroup L s.group (i.1 / L.block) peer) :
    PeerSharedStarted L kernel Prod X (.thread i) peer ∧
      (CtaExited L X peer → SharedFinished L kernel Prod X (.thread i) peer) := by
  obtain ⟨hg, -, -, m, hσ, hsp⟩ := commit_source hX ht hc
  obtain ⟨pc0, he⟩ := id hc
  obtain ⟨b, hb, -, -, -, -, -⟩ := commit_bar hX ht hc
  have hblock := hpre.block
  obtain ⟨⟨-, hpg, hpc⟩, -⟩ := hpeer
  obtain ⟨pci, hinit, hpub⟩ := ht.ring_initialized hg he hσ hb hpg hpc.symm
  obtain ⟨start, sev, hsc, hse, hsw⟩ := started_of_published ⟨_, hinit⟩ hpub
  have hpb : peer * L.block / L.block = peer := by
    rw [Nat.mul_div_cancel _ (by rw [hblock]; decide)]
  refine ⟨⟨start, sev, Frame.lt_of_get hX hse, by rw [hsc, hpb], hse, hsw⟩, fun hexit => ?_⟩
  have hgp : peer * L.block < L.threads := by
    simp only [Launch.threads]
    rw [hblock] at hpb ⊢
    nlinarith
  obtain ⟨fpc, hlast⟩ := hexit (peer * L.block) hgp hpb
  rw [List.getLast?_eq_getElem?] at hlast
  change X.get (peer * L.block, (X.tr (peer * L.block)).length - 1) = _ at hlast
  have hph : ThreadD.clPhase (.inr (.mma m)) ≤ 1 := by
    rcases hsp with ⟨sl, hs, -⟩ | ⟨hs, -⟩ <;> simp [ThreadD.clPhase, hs]
  have hhb := hex i (peer * L.block, (X.tr (peer * L.block)).length - 1) _ _ fpc he hσ hph
    (fun rel al h => by cases h) hlast ⟨hg, hgp, by rw [hpb]; exact hpc⟩
  exact ⟨⟨_, he⟩, _, fpc, hgp, hpb, hlast, CompletedBefore.of_baseCausality hhb⟩

/-- **No commit is unsafe.** -/
theorem no_commit_unsafe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : ¬ TcCommitUnsafe L X := by
  rintro ⟨i, s, hc, hn⟩
  exact hn (commit_issue_safe hpre hX ht hc)

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
