-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Vote
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VotePeers

public section

/-! # Progress at the softmax reference vote -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem peer_at_vote_or_earlier {g h : Nat} {d z : Wg0.D}
    (hBlocks : Wg0.blocksOf P L h = Wg0.blocksOf P L g)
    (hi : Wg0.Inv P L g d) (hz : Wg0.Inv P L h z)
    (hSite : d.site = .rescaleVote) (hCount : Wg0VoteCount.ordinal z = d.block) :
    z.site = .rescaleVote ∨ priority P L h (.wg0 z) < priority P L g (.wg0 d) := by
  by_cases hEq : z.site = .rescaleVote
  · exact .inl hEq
  right
  have hSub : z.sub < 4 := hz.subLt.trans_le (by cases z.site <;> decide +revert)
  have hBlock := hi.blockLt
  have hEpi : z.site.inEpilogue = false := by
    cases he : z.site.inEpilogue
    · rfl
    · have hLast := hz.epilogueLast he
      have hVote : Wg0VoteCount.ordinal z = z.block + 1 := by
        cases hp : z.site <;> simp_all [Wg0.Site.inEpilogue, Wg0VoteCount.ordinal,
          Wg0VoteCount.afterVote]
      omega
  cases hZ : z.site
  all_goals first
    | exact (hEq hZ).elim
    | solve | simp [Wg0.Site.inEpilogue, hZ] at hEpi
    | (try (rename_i j; have := j.isLt))
      simp only [Wg0VoteCount.ordinal, Wg0VoteCount.afterVote, hZ,
        Bool.toNat_true, Bool.toNat_false, Nat.add_zero] at hCount
      simp only [priority, softmaxTime, blockTime, hSite, hZ, wg0Ordinal]
      omega

/-- If the reference vote cannot issue in a maximal followed execution, another lane in
its warp is pending at a strictly earlier site. -/
theorem pending_softmax_vote_earlier {g : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : PendingState P L X g (.wg0 d))
    (hSite : d.site = .rescaleVote) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g (.wg0 d) := by
  have hX := hmax.1
  have hPeers := softmax_vote_peers hpre hX hs ht hub hp.1 hp.2 hSite
  obtain ⟨v, hRun⟩ := Frame.run_some hX hub hp.1
  obtain ⟨_, _, _, _, hi, _, _⟩ := Frame.end_at hs hp.1.1 hRun hp.2
  change Wg0.Inv P L g d at hi
  by_contra hNoEarlier
  have all (h : Nat) (hw : SameWarp L g h) :
      ∃ z, Frame.Pending L X h ∧ PTX.Step.Released L X h ∧
        Frame.stateAt (Machine.code P L) X h (X.tr h).length = some (some (.wg0 z)) ∧
        z.site = .rescaleVote := by
    obtain ⟨hPend, hCount⟩ := hPeers h hw
    obtain ⟨q, hQ⟩ := pending_followed hpre hX hs ht hPend
    have hCta : ctaOf L h = ctaOf L g := hw.1.2.2.symm
    have hBlocks : Wg0.blocksOf P L h = Wg0.blocksOf P L g := by
      simp only [Wg0.blocksOf, Wg0.eOf, ctaidY, hCta]
    have hWarp : warpOf L h = warpOf L g := by
      simpa only [warpOf, tidOf_eq hpre, hpre.block] using hw.2.symm
    have hGroup : wgOf L h = 0 := by
      have hLt := hi.warpLt
      unfold wgOf
      rw [← Nat.div_div_eq_div_mul _ 32 4]
      change warpOf L h / 4 = 0
      omega
    have sound := (hs h hPend.1).machine
    rcases Wg0.state_of_wg hGroup (sound.produces (hX.thr h hPend.1)) hQ with
      ⟨s, rfl⟩ | ⟨z, rfl⟩ | rfl
    · apply (hNoEarlier ⟨h, .prologue s, ⟨hPend, hQ⟩, ?_⟩).elim
      simp only [priority, softmaxTime, blockTime, hSite, wg0Ordinal]
      omega
    · obtain ⟨t, hRun⟩ := Frame.run_some hX hub hPend
      obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.end_at hs hPend.1 hRun hQ
      have hOrd := Wg0VoteCount.count_of_prefix hX sound hPend.1 hQ
      rw [List.take_length, hCount] at hOrd
      rcases peer_at_vote_or_earlier hBlocks hi hInv hSite hOrd.symm with hV | hEarlier
      · exact ⟨z, hPend, softmax_vote_released hQ hV, hQ, hV⟩
      · exact (hNoEarlier ⟨h, .wg0 z, ⟨hPend, hQ⟩, hEarlier⟩).elim
    · obtain ⟨j, _, tag, hClose⟩ :=
        ClosingOrder.arrival_before_state hpre hX sound hPend.1 hQ trivial
      have hAt := softmax_vote_count_at_closing hpre hX hs ht hGroup hClose
      have hMono := (List.take_sublist j (X.tr h)).countP_le (p := Wg0VoteCount.countsVote)
      rw [hAt, hBlocks, hCount] at hMono
      exact (Nat.not_le_of_lt hi.blockLt hMono).elim
  exact hmax.not_grows (softmax_rescale_vote_extension hpre hs hX hp.1.1 hub all)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
