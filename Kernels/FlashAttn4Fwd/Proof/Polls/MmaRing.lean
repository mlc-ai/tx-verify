-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.Waits
public import Kernels.FlashAttn4Fwd.Proof.Progress.Collective
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressAsync
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.MmaRing
public import Kernels.FlashAttn4Fwd.Proof.Protocol.MmaRingBlocked
public import Lemmas.Protocol.ElectCount

@[expose] public section

/-! # The MMA warp's Q-full and KV-full polls have a blocker

A lane `g` of the leader CTA's MMA warp at a `qWait` or `kvWait` site polls the full barrier `b`
of its CTA `2 c` (`MmaRingPollFacts.poll`), which has a final state (`MmaRing.full_state`, after
its first `bar.sync`). Let `n` be its successful polls of `b`. The elected MMA lane is a lane of
its warp; all elections name the full mask, so it has made no more elections than `g`
(`electCount_le`), and its commits to the partner empty barrier are at most `n`
(`MmaRingPollFacts.commits`). When the phase of `b` has the parity of `n`, the protocol
(`MmaRing.mmaRingBlocked`) gives a short use: the leader CTA's elected loader lane made at most
`n` arrivals, or an elected loader lane of the pair issued fewer than `n + 1` uses' copies (each
then lags `g`, `MmaRingPollFacts.arrive`, `copies`, and is a blocker, `Sched.blk_of_lags`), or a
tensor copy is open. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Flow MBarrier Rings

noncomputable section

/-- An MMA state at a Q-full or KV-full poll site has a positive time. -/
theorem one_le_mmaWait {L : Launch} {g : Nat} {d : Mma.D}
    (hsite : (∃ k, d.site = .qWait k) ∨ ∃ k, d.site = .kvWait k) :
    1 ≤ stateTime L g (.inr (.mma d)) := by
  obtain ⟨site, i, t, base, pro⟩ := d
  rcases hsite with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp only at hk <;> subst hk <;>
    simp only [stateTime, Time.mma, Time.mmaAt, Time.slotTime, Time.base] <;> split_ifs <;> omega

/-- **The MMA warp's Q-full and KV-full polls have a blocker.** -/
theorem mmaRing_pollBlocked {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hmax : Maximal L kernel asms mem0 X) (hI : AsyncInputs P L X) (_hW : WaitInputs L X)
    (hF : MmaRingPollFacts L X) {g : Nat} (hp : Frame.Pending L X g)
    (_hrel : Step.Released L X g) {d : Mma.D}
    (hσ : St L X g (X.tr g).length = some (some (.inr (.mma d))))
    (hsite : (∃ k, d.site = .qWait k) ∨ ∃ k, d.site = .kvWait k) :
    Sched.PollBlocked (timed L) X g := by
  have hX := hmax.1
  have hg := hp.1
  obtain ⟨hev, hw12, ⟨j, pc, hbar⟩, hpoll⟩ := hF.poll hg hσ hsite
  obtain ⟨b, hbq, hfull⟩ : ∃ b, Mma.pollBar L d = some b ∧ b.isFull := by
    rcases hsite with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp [Mma.pollBar, hk, FBar.isFull]
  have hne : X.tr g ≠ [] := by
    intro h
    have h' : (X.tr g)[j]? = some _ := hbar
    simp [h] at h'
  set c := ctaOf L g / 2 with hc
  have hcg : ctaOf L g = 2 * c := by omega
  have hP := hpoll b hbq
  rw [hcg] at hP
  obtain ⟨before, hst⟩ := MmaRing.full_state hpre hX hI.cluster hI.init hI.tmem hI.rings hfull
    hbar (by simp [PreKind]) (by simp) hc.symm
  refine Sched.pollBlocked_of hP hst (fun hpar => ?_)
  have h2c : 2 * c < L.grid := hcg ▸ cta_lt hg
  have h2c1 : 2 * c + 1 < L.grid := by
    have := hpre.grid
    omega
  have h1 := one_le_mmaWait (L := L) (g := g) hsite
  have hcl : ∀ y, ctaOf L y / 2 = c →
      L.clusterOfCta (y / L.block) = L.clusterOfCta (g / L.block) := by
    intro y hy
    change clusterOf L y = clusterOf L g
    rw [clusterOf_eq hpre, clusterOf_eq hpre]
    omega
  -- The elected MMA lane's commits are at most `n`.
  have hy := MmaRing.leadOf_lt (X := X) hpre h2c (by decide : 12 < 16)
  obtain ⟨hyc, hyw⟩ := leadOf_place (X := X) (cta := 2 * c) (w := 12) hpre (by decide)
  have hsw : SameWarp L g (leadOf L X (2 * c) 12) := by
    refine ⟨⟨hg, hy, ?_⟩, ?_⟩
    · change ctaOf L g = ctaOf L _
      rw [hyc, hcg]
    · change warpOf L g = warpOf L _
      rw [hyw, hw12]
  have hE := electCount_le hX (fun he => elect_full hX he) (sameWarp_symm hsw)
  have hC := hF.commits hg hsw hσ hsite hbq
    (MmaRing.leadOf_selfElected hpre hX (by decide)) hE
  rw [hcg] at hC
  have hinit : RingInit L X := InitFirst.ringInit hpre hX hI.cluster hI.tmem hI.init hI.rings
  rcases MmaRing.mmaRingBlocked hpre hX hI.rings hI.tmem hinit c b hfull hst hC
      (by simpa using hpar) with harr | ⟨a, hcp⟩ | hobl
  · -- The leader CTA's loader lane has made at most `n` arrivals.
    have hy0 := MmaRing.leadOf_lt (X := X) hpre h2c (by decide : 14 < 16)
    obtain ⟨hy0c, hy0w⟩ := leadOf_place (X := X) (cta := 2 * c) (w := 14) hpre (by decide)
    refine Sched.blk_of_lags hX (Sched.safe_noUb (hs.2 X hX)) hg hne hσ hy0 (hcl _ (by omega))
      (hF.arrive hg hy0 hσ hsite hbq (by rw [hy0c, hcg]) hy0w
        (MmaRing.leadOf_selfElected hpre hX (by decide)) ?_)
    rw [hcg]
    exact harr
  · -- A loader lane of the pair has issued fewer than `n + 1` uses' copies.
    have hca : 2 * c + a.val < L.grid := by
      rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with ha | ha <;> subst ha
      · exact h2c
      · exact h2c1
    have hya := MmaRing.leadOf_lt (X := X) hpre hca (by decide : 14 < 16)
    obtain ⟨hyac, hyaw⟩ := leadOf_place (X := X) (cta := 2 * c + a.val) (w := 14) hpre
      (by decide)
    have ha2 := a.isLt
    refine Sched.blk_of_lags hX (Sched.safe_noUb (hs.2 X hX)) hg hne hσ hya (hcl _ (by omega))
      (hF.copies hg hya hσ hsite hbq (by omega) hyaw
        (MmaRing.leadOf_selfElected hpre hX (by decide)) ?_)
    rw [hcg]
    exact hcp
  · exact .inl ⟨.tensor, by simp, hobl⟩

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
