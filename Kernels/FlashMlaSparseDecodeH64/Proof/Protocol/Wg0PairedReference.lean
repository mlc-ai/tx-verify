-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0MaxReadback
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Probability
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ReferenceHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0TcVotes
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
import Lemmas.Flow.NthEv

@[expose] public section

/-! # Paired softmax warps reduce the same reference-change predicates -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PairedReference

open PTX PTX.Proof PTX.Flow PTX.Assumption Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem sub_reference_eq {d q : D} {m : WithBot ℝ}
    (hm : d.blockMax = peakVal m) (hq : q.blockMax = peakVal m)
    (hr : reference d = reference q) :
    subE true d.blockMax (miVal d) = subE true q.blockMax (miVal q) := by
  rw [hm, hq]
  cases m with
  | bot =>
    have hNeg : readEReal .f32 negInf = some (.ok (⊥ : EReal)) := rfl
    simp only [subE, idealSub, show peakVal ⊥ = negInf from rfl, hNeg,
      readEReal_of_valFloat (valFloat_miVal d), readEReal_of_valFloat (valFloat_miVal q),
      hr, bindRead, addEReal, pure, Except.pure]
    rfl
  | coe x =>
    change subE true (fl x) (miVal d) = subE true (fl x) (miVal q)
    rw [subE_fin (valFloat_fl x) (valFloat_miVal d),
      subE_fin (valFloat_fl x) (valFloat_miVal q), hr]

/-- Equal maxima and old references produce equal contributions at actual votes. -/
theorem equal_vote_inputs {g h i j : Nat} {d q : D} {m : WithBot ℝ}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hg : g < L.threads) (hh : h < L.threads)
    (hi : i ≤ (X.tr g).length) (hj : j ≤ (X.tr h).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hq : Frame.stateAt (Machine.code P L) X h j = some (some (.wg0 q)))
    (hD : d.site = .rescaleVote) (hQ : q.site = .rescaleVote)
    (hm : d.blockMax = peakVal m) (hm' : q.blockMax = peakVal m)
    (hr : reference d = reference q) :
    d.voteTest = q.voteTest := by
  obtain ⟨gd, hdGap, hdPred⟩ :=
    Wg0ReferenceHistory.comparison_at_vote hX hs hg hi hd hD
  obtain ⟨gq, hqGap, hqPred⟩ :=
    Wg0ReferenceHistory.comparison_at_vote hX hs hh hj hq hQ
  rw [sub_reference_eq hm hm' hr, hqGap] at hdGap
  obtain rfl := Except.ok.inj hdGap
  exact Except.ok.inj (hdPred.symm.trans hqPred)

/-- The same old reference, block maximum and collective result yield the same new reference. -/
theorem equal_reference_after_vote {d q d' q' : D} {m : WithBot ℝ} {take : Bool}
    (hd : d.blockMax = peakVal m) (hq : q.blockMax = peakVal m)
    (href : reference d = reference q)
    (hD : afterReferenceVote d take = some d') (hQ : afterReferenceVote q take = some q') :
    reference d' = reference q' := by
  obtain ⟨dNext, hDNext, hDRef, _⟩ := Result.afterReferenceVote_ratio m hd take
  obtain ⟨qNext, hQNext, hQRef, _⟩ := Result.afterReferenceVote_ratio m hq take
  rw [hD] at hDNext
  rw [hQ] at hQNext
  obtain rfl := Option.some.inj hDNext
  obtain rfl := Option.some.inj hQNext
  rw [hDRef, hQRef, href]

private theorem warp_lane_address {l : Nat} (hpre : Pre P L mem0) (g : Nat) :
    warpLane L g l = ctaOf L g * 384 + 32 * warpOf L g + l := by
  unfold warpLane PTX.laneOf warpOf ctaOf
  rw [tidOf_eq hpre, hpre.block]
  omega

private theorem warp_lane_geometry {g l : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (hw : warpOf L g < 4) (hl : l < 32) :
    let t := warpLane L g l
    t < L.threads ∧ ctaOf L t = ctaOf L g ∧ warpOf L t = warpOf L g ∧
      laneOf L t = l ∧ wgOf L t = 0 := by
  let t := warpLane L g l
  have he : t = ctaOf L g * 384 + 32 * warpOf L g + l := warp_lane_address hpre g
  have ht : t = ctaOf L g * L.block + (32 * warpOf L g + l) := by
    rw [hpre.block, he, Nat.add_assoc]
  have hsmall : 32 * warpOf L g + l < L.block := by rw [hpre.block]; omega
  have hTid : tidOf L t = 32 * warpOf L g + l := by
    rw [tidOf_eq hpre, he]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change t < L.threads
    rw [ht]
    exact NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hsmall
  · change t / L.block = ctaOf L g
    rw [hpre.block, he]
    omega
  · change tidOf L t / 32 = _
    rw [hTid]
    omega
  · change tidOf L t % 32 = _
    rw [hTid]
    omega
  · change tidOf L t / 128 = _
    rw [hTid]
    omega

private theorem warp_lane_partner {g l : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (hw : warpOf L g < 4) (hl : l < 32) :
    warpLane L (Wg0PeerSources.partner L g) l = Wg0PeerSources.partner L (warpLane L g l) := by
  obtain ⟨_, hc, hwarp, hlane, _⟩ := warp_lane_geometry hpre hg hw hl
  obtain ⟨hMate, hWg, hTid⟩ := Wg0MaxReadback.partner_geometry hpre hg hw
  have hWm := Wg0.warpLt hpre hWg
  have hBound : tidOf L (Wg0PeerSources.partner L g) < 128 := by
    change tidOf L (Wg0PeerSources.partner L g) / 32 < 4 at hWm
    omega
  have hBound' : tidOf L g < 128 := by change tidOf L g / 32 < 4 at hw; omega
  rw [Nat.mod_eq_of_lt hBound, Nat.mod_eq_of_lt hBound'] at hTid
  have hSwap : ∀ n : Fin 128, (n.val ^^^ 64) / 32 = n.val / 32 ^^^ 2 := by decide
  have hWarpMate : warpOf L (Wg0PeerSources.partner L g) = warpOf L g ^^^ 2 := by
    change tidOf L (Wg0PeerSources.partner L g) / 32 = _
    rw [hTid]
    exact hSwap ⟨tidOf L g, hBound'⟩
  rw [warp_lane_address hpre]
  change _ = ctaOf L (warpLane L g l) * L.block +
    (32 * (warpOf L (warpLane L g l) ^^^ 2) + laneOf L (warpLane L g l))
  have hCta : ctaOf L (Wg0PeerSources.partner L g) = ctaOf L g := hMate.2.2
  rw [hCta, hWarpMate, hc, hwarp, hlane, hpre.block, Nat.add_assoc]

private theorem no_early_exit {g b : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hw : wgOf L g = 0)
    (hb : b < Wg0.blocksOf P L g) : ¬ MaskExited voteClass X g (2 ^ 32 - 1) b := by
  rintro ⟨i, tag, he, hmask⟩
  have hg := Frame.lt_of_get hX he
  have hdone := Wg0OutputVisits.doneAtExit hX (hs g hg).machine ht hw he rfl
  obtain ⟨j, hj, d, e, hd, hsite, hget, _⟩ :=
    Wg0OutputVisits.barrierBeforeDone hpre hX hg (hs g hg).machine hw hdone 0
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hget hd
  have hi : Wg0.Inv P L g d := hInv
  have hLast := hi.epilogueLast (by rw [hsite]; rfl)
  have hCount := Wg0VoteCount.count_at_wg0 hX (hs g hg).machine hget hd
  rw [Wg0VoteCount.ordinal, hsite] at hCount
  change ((X.tr g).take j).countP Wg0VoteCount.countsVote = d.block + 1 at hCount
  have hmono := countP_take_mono Wg0VoteCount.countsVote (X.tr g) hj.le
  change ((X.tr g).take i).countP Wg0VoteCount.countsVote ≤ b at hmask
  omega

private theorem vote_mask_k {g i tag : Nat} {d : D} {p take : Bool}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (he : X.get (g, i) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) p take⟩)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) :
    X.MaskK voteClass (g, i) (2 ^ 32 - 1) d.block := by
  have hcount := Wg0VoteCount.count_at_wg0 hX (hs g (Frame.lt_of_get hX he)).machine he hd
  rw [Wg0VoteCount.ordinal, hsite] at hcount
  refine ⟨⟨_, ⟨2 ^ 32 - 1, .any, p⟩, he, rfl, rfl⟩, ?_⟩
  exact hcount.trans (Nat.add_zero _)

private theorem actual_participant {g b l : Nat} {part : Nat → Option Bool}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hInstance : MaskInstance L voteClass X g (2 ^ 32 - 1) b .any part) (hl : l < 32)
    (hNoExit : ¬ MaskExited voteClass X (warpLane L g l) (2 ^ 32 - 1) b) :
    let t := warpLane L g l
    ∃ j q tag take, X.get (t, j) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) q.voteTest take⟩ ∧
      Frame.stateAt (Machine.code P L) X t j = some (some (.wg0 q)) ∧
      q.site = .rescaleVote ∧ q.block = b ∧ part l = some q.voteTest := by
  have hbit : (2 ^ 32 - 1 : Nat).testBit l = true :=
    Nat.testBit_two_pow_sub_one 32 _ ▸ decide_eq_true hl
  rcases (hInstance l hl).1 hbit with ⟨j, tag, kind, pred, he, hkind, hk, hPart⟩ | ⟨he, _⟩
  · have hclass : voteClass kind ≠ none := by rw [hkind]; simp
    obtain ⟨q, hst⟩ := Frame.event_state hs hX ht he (by
      intro u f h
      have hKind := congrArg Event.kind h
      change kind = .ub f at hKind
      rw [hKind] at hclass
      exact hclass rfl)
    have htm := Frame.lt_of_get hX he
    obtain ⟨o, hf⟩ := (Frame.trace hs hX htm).fired_at he hst
    obtain ⟨d, r, rfl, hsite, hVote⟩ := Wg0VoteSites.of_fired hf hclass
    have hVote : kind = .voteMode .any (2 ^ 32 - 1) d.voteTest r := hVote
    have hcount := Wg0VoteCount.count_at_wg0 hX (hs _ htm).machine he hst
    rw [Wg0VoteCount.ordinal, hsite] at hcount
    have hmatch : b = d.block := hk.2.symm.trans (hcount.trans (Nat.add_zero _))
    rw [hVote] at he hkind
    have hEq : d.voteTest = pred := congrArg WarpPart.input (Option.some.inj hkind)
    exact ⟨j, d, tag, r, he, hst, hsite, hmatch.symm, hPart.trans (congrArg some hEq.symm)⟩
  · exact (hNoExit he).elim

/-- The actual votes of paired warps return the same predicate when corresponding
lanes have the same old reference and block maximum. All 32 lanes take part in each vote. -/
theorem paired_vote_result {g i j tag mateTag : Nat} {d q : D} {p p' take take' : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) p take⟩)
    (hf : X.get (Wg0PeerSources.partner L g, j) =
      some ⟨mateTag, .voteMode .any (2 ^ 32 - 1) p' take'⟩)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hq : Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) j =
      some (some (.wg0 q)))
    (hD : d.site = .rescaleVote) (hQ : q.site = .rescaleVote) (hBlock : q.block = d.block)
    (hInputs : ∀ {l j0 j1 : Nat} {v w : D} {e0 e1 : Event}, l < 32 →
      X.get (warpLane L g l, j0) = some e0 →
      X.get (Wg0PeerSources.partner L (warpLane L g l), j1) = some e1 →
      Frame.stateAt (Machine.code P L) X (warpLane L g l) j0 = some (some (.wg0 v)) →
      Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L (warpLane L g l)) j1 =
        some (some (.wg0 w)) →
      v.site = .rescaleVote → w.site = .rescaleVote → v.block = d.block → w.block = d.block →
      ∃ m : WithBot ℝ, v.blockMax = peakVal m ∧ w.blockMax = peakVal m ∧
        reference v = reference w) :
    take = take' := by
  let mate := Wg0PeerSources.partner L g
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hd
  have hInv' : Wg0.Inv P L g d := hInv
  have hWarp := hInv'.warpLt
  obtain ⟨hPair, hMateWg, _⟩ := Wg0MaxReadback.partner_geometry hpre hg hWarp
  have hMateWarp := Wg0.warpLt hpre hMateWg
  have hk := vote_mask_k hX hs he hd hD
  have hk' := vote_mask_k hX hs hf hq hQ
  rw [hBlock] at hk'
  obtain ⟨part, hPart⟩ := Wg0TcVotes.full_instance hX he hk
  obtain ⟨part', hPart'⟩ := Wg0TcVotes.full_instance hX hf hk'
  have hbound {t : Nat} (hc : ctaOf L t = ctaOf L g) : d.block < Wg0.blocksOf P L t := by
    have hSame : Wg0.blocksOf P L t = Wg0.blocksOf P L g := by
      simp only [Wg0.blocksOf, Wg0.eOf, ctaidY, hc]
    rw [hSame]
    exact hInv'.blockLt
  have hSamePart : MaskInstance L voteClass X mate (2 ^ 32 - 1) d.block .any part := by
    intro l hl
    obtain ⟨hg0, hCta0, _, _, hWG0⟩ := warp_lane_geometry hpre hg hWarp hl
    obtain ⟨hg1, hCta1, _, _, hWG1⟩ := warp_lane_geometry hpre hPair.1 hMateWarp hl
    have hCta : ctaOf L mate = ctaOf L g := hPair.2.2
    have hPartner := warp_lane_partner hpre hg hWarp hl
    obtain ⟨j0, v, _, _, hv, hvState, hvSite, hvBlock, harg⟩ :=
      actual_participant hX hs ht hPart hl (no_early_exit hpre hX hs ht hWG0 (hbound hCta0))
    obtain ⟨j1, w, _, _, hw, hwState, hwSite, hwBlock, harg'⟩ :=
      actual_participant hX hs ht hPart' hl
        (no_early_exit hpre hX hs ht hWG1 (hbound (hCta1.trans hCta)))
    have hwPartner := hwState
    have hwGet := hw
    rw [hPartner] at hwPartner hwGet
    obtain ⟨m, hMax, hMax', hRef⟩ :=
      hInputs hl hv hwGet hvState hwPartner hvSite hwSite hvBlock hwBlock
    have hEq := equal_vote_inputs hX hs hg0 hg1 (PTX.len_of_get hv).le
      (PTX.len_of_get hw).le hvState hwState hvSite hwSite hMax hMax' hRef
    have hp : part l = part' l := harg.trans (hEq ▸ harg'.symm)
    rw [hp]
    exact hPart' l hl
  exact (hX.warpValue.1 g i tag .any _ _ _ _ he hk part hPart).trans
    (hX.warpValue.1 mate j mateTag .any _ _ _ _ hf hk' part hSamePart).symm

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PairedReference
