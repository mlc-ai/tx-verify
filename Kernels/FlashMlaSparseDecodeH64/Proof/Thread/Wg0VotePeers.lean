-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteCount
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Election
import Lemmas.Clc.ClcExecution
import Lemmas.Step.WarpVote

public section

/-! # Actual live peers and vote counts for the softmax rendezvous -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Step

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The closing softmax warp has already executed all its references votes. -/
theorem softmax_vote_count_at_closing {h j tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hWg : wgOf L h = 0) (he : X.get (h, j) = some ⟨tag, .bar 12 none .sync⟩) :
    ((X.tr h).take j).countP Wg0VoteCount.countsVote = Wg0.blocksOf P L h := by
  have hh := Frame.lt_of_get hX he
  have hSound := (hs h hh).machine
  obtain ⟨q, hQ, hSite, _, _⟩ := ScoreClosingGate.closing_at hpre hX hs ht he
  rcases Wg0.state_of_wg hWg (hSound.produces (hX.thr h hh)) hQ with h | ⟨d, rfl⟩ | rfl
  · obtain ⟨s, rfl⟩ := h
    exact hSite.elim
  · have hd : d.site = .everyone := hSite
    obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX hSound he hQ
    have hi : Wg0.Inv P L h d := hFire.choose_spec.1.2
    have ht := hi.epilogueLast (by rw [hd]; decide)
    have hCount := Wg0VoteCount.count_at_wg0 hX hSound he hQ
    simpa only [Wg0VoteCount.ordinal, Wg0VoteCount.afterVote, hd, Bool.toNat_true, ht] using hCount
  · exact hSite.elim

/-- A pending reference vote has a live warp with identical numbers of completed votes. -/
theorem softmax_vote_peers {g : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g)
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hSite : d.site = .rescaleVote) :
    ∀ h, SameWarp L g h → Frame.Pending L X h ∧
      (X.tr h).countP Wg0VoteCount.countsVote = d.block := by
  have hSound := (hs g hp.1).machine
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, _, _, _, hi, _, _⟩ := Frame.end_at hs hp.1 hRun hd
  change Wg0.Inv P L g d at hi
  let mask := 2 ^ 32 - 1
  have hCount : PTX.Step.maskCount voteClass X g mask = d.block := by
    have hc := Wg0VoteCount.count_of_prefix hX hSound hp.1 hd
    rw [List.take_length] at hc
    change (X.tr g).countP Wg0VoteCount.countsVote = d.block
    simpa only [Wg0VoteCount.ordinal, Wg0VoteCount.afterVote, hSite,
      Bool.toNat_false, Nat.add_zero] using hc
  have hUpper (h : Nat) (hh : SameWarp L g h) :
      PTX.Step.maskCount voteClass X h mask ≤ d.block := by
    by_contra! hLt
    obtain ⟨i, hVote⟩ := PTX.Step.exists_maskK (c := voteClass) (g := h)
      (show d.block + 1 ≤ PTX.Step.maskCount voteClass X h mask by omega)
    rcases vote_lane_of_ready hX hVote (sameWarp_symm hh) (full_member L g).2 with
      ⟨j, hJ⟩ | ⟨j, pc, he⟩
    · have h := PTX.Step.MaskK.lt_count hJ
      rw [hCount] at h
      omega
    · exact hRun.no_exit he
  have hNoClose (h : Nat) (hw : SameWarp L g h) {j tag : Nat}
      (he : X.get (h, j) = some ⟨tag, .bar 12 none .sync⟩) : False := by
    have hCta : ctaOf L h = ctaOf L g := hw.1.2.2.symm
    have hBlock : Wg0.blocksOf P L h = Wg0.blocksOf P L g := by
      simp only [Wg0.blocksOf, Wg0.eOf, ctaidY, hCta]
    have hWarp : warpOf L h = warpOf L g := by
      simpa only [warpOf, tidOf_eq hpre, hpre.block] using hw.2.symm
    have hW : wgOf L h = 0 := by
      have hWg := hi.warpLt
      unfold wgOf
      rw [← Nat.div_div_eq_div_mul _ 32 4]
      change warpOf L h / 4 = 0
      omega
    have hBefore := softmax_vote_count_at_closing hpre hX hs ht hW he
    have hMono := (List.take_sublist j (X.tr h)).countP_le (p := Wg0VoteCount.countsVote)
    rw [hBefore, hBlock] at hMono
    have hN := hi.blockLt
    have hLe := hUpper h hw
    change (X.tr h).countP Wg0VoteCount.countsVote ≤ d.block at hLe
    omega
  have hNoExit (h : Nat) (hw : SameWarp L g h) (j pc : Nat) :
      X.get (h, j) ≠ some ⟨pc, .exit⟩ := by
    intro he
    obtain ⟨k, _, tag, hk⟩ := ClosingOrder.arrival_before_exit hpre hX hs ht he
    exact hNoClose h hw hk
  intro h hw
  refine ⟨⟨hw.1.2.1, ?_, ?_⟩, ?_⟩
  · rintro ⟨_, _, hCancel⟩
    obtain ⟨i, s, tg, _, hi, _⟩ := hX.clc.canceled_has_issue hCancel
    exact GlobalWrites.no_clc (i := i) (s := s) (tg := tg) hX hi
  · intro pc hLast
    rw [List.getLast?_eq_getElem?] at hLast
    exact hNoExit h hw _ _ hLast
  · have he := (vote_count_eq hX hw hNoExit (fun h _ => (full_member L h).2)).symm
    rw [hCount] at he
    exact he

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
