-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualPvVotes
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PairedBlockMax
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ReferencePrefix
import Lemmas.Flow.NthEv

@[expose] public section

/-! # The reference shared by all actual softmax votes for a head and sparse block -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow Protocol Wg0

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A reference recorded by an actual vote at this head and sparse block. -/
def VoteReferenceCandidate (P : Params) (L : Launch) (X : Execution)
    (cta block head : Nat) (ref : ℝ) : Prop :=
  ∃ g j v mid tag take, ctaOf L g = cta ∧ Wg0.head L g = head ∧ v.block = block ∧
    X.get (g, j) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) v.voteTest take⟩ ∧
    Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 v)) ∧ v.site = .rescaleVote ∧
    afterReferenceVote v take = some mid ∧ reference mid = ref

/-- Use an actual reference update of this head and block when one has occurred. -/
def canonicalPvReference (P : Params) (L : Launch) (X : Execution) (cta block head : Nat) : ℝ :=
  by
    classical
    exact if h : ∃ ref, VoteReferenceCandidate P L X cta block head ref then
      Classical.choose h else negMaxReal

private theorem same_thread_of_geometry {g h : Nat} (hpre : Pre P L mem0)
    (hc : ctaOf L g = ctaOf L h) (ht : tidOf L g = tidOf L h) : g = h := by
  rw [tidOf_eq hpre, tidOf_eq hpre] at ht
  simp only [ctaOf, hpre.block] at hc
  omega

private theorem same_head_lanes {g h : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (hG : warpOf L g < 4) (hH : warpOf L h < 4)
    (hc : ctaOf L g = ctaOf L h) (hd : Wg0.head L g = Wg0.head L h) :
    h = g ∨ h = Wg0PeerSources.partner L g := by
  by_cases hTid : tidOf L h = tidOf L g
  · exact .inl (same_thread_of_geometry hpre hc.symm hTid)
  · apply Or.inr
    obtain ⟨hMate, hWg, hT⟩ := Wg0MaxReadback.partner_geometry hpre hg hG
    have hG' : tidOf L g < 128 := by change tidOf L g / 32 < 4 at hG; omega
    have hH' : tidOf L h < 128 := by change tidOf L h / 32 < 4 at hH; omega
    have hMateTid : tidOf L (Wg0PeerSources.partner L g) < 128 := by
      change tidOf L (Wg0PeerSources.partner L g) / 128 = 0 at hWg
      omega
    rw [Nat.mod_eq_of_lt hMateTid, Nat.mod_eq_of_lt hG'] at hT
    have hCtaMate : ctaOf L h = ctaOf L (Wg0PeerSources.partner L g) :=
      hc.symm.trans hMate.2.2.symm
    apply same_thread_of_geometry hpre hCtaMate
    rw [hT]
    change tidOf L g % 64 = tidOf L h % 64 at hd
    have hXor : ∀ t : Fin 128, t.val ^^^ 64 =
        if t.val < 64 then t.val + 64 else t.val - 64 := by decide
    have hx := hXor ⟨tidOf L g, hG'⟩
    change tidOf L g ^^^ 64 = (if tidOf L g < 64 then tidOf L g + 64 else tidOf L g - 64) at hx
    rw [hx]
    split_ifs <;> omega

private theorem counted_vote {e : Event} {mask : Nat} {p take : Bool}
    (hk : e.kind = .voteMode .any mask p take) :
    (voteClass e.kind).any (·.mask == mask) = true := by
  simp only [hk, voteClass, Option.any_some, beq_self_eq_true]

private theorem same_vote_reference {g i j tag tag' : Nat} {d q mid mid' : D}
    {take take' : Bool}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) d.voteTest take⟩)
    (hf : X.get (g, j) = some ⟨tag', .voteMode .any (2 ^ 32 - 1) q.voteTest take'⟩)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)))
    (hD : d.site = .rescaleVote) (hQ : q.site = .rescaleVote) (hb : d.block = q.block)
    (hRef : afterReferenceVote d take = some mid)
    (hRef' : afterReferenceVote q take' = some mid') :
    reference mid = reference mid' := by
  have hg := Frame.lt_of_get hX he
  have hCount := Wg0VoteCount.count_at_wg0 hX (hs g hg).machine he hd
  have hCount' := Wg0VoteCount.count_at_wg0 hX (hs g hg).machine hf hq
  rw [Wg0VoteCount.ordinal, hD, hb] at hCount
  rw [Wg0VoteCount.ordinal, hQ] at hCount'
  have hc : ((X.tr g).take i).countP Wg0VoteCount.countsVote =
      ((X.tr g).take j).countP Wg0VoteCount.countsVote := hCount.trans hCount'.symm
  have hEq := nthEv_unique (p := Wg0VoteCount.countsVote) he
    (counted_vote (mask := 2 ^ 32 - 1) rfl) hf (counted_vote (mask := 2 ^ 32 - 1) rfl) hc
  subst j
  rw [hd] at hq
  obtain rfl := Machine.ThreadD.wg0.inj (Option.some.inj (Option.some.inj hq))
  have hTake : take = take' := (Kind.voteMode.inj
    (congrArg Event.kind (Option.some.inj (he.symm.trans hf)))).2.2.2
  rw [← hTake, hRef] at hRef'
  exact congrArg reference (Option.some.inj hRef')

private theorem candidate_unique {cta block head : Nat} {a b : ℝ}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hMax : Wg0PairedReference.PairedBlockMax P L X)
    (ha : VoteReferenceCandidate P L X cta block head a)
    (hb : VoteReferenceCandidate P L X cta block head b) : a = b := by
  obtain ⟨g, i, d, mid, tag, take, hCta, hHead, hBlock, he, hd, hD, hRef, rfl⟩ := ha
  obtain ⟨h, j, q, mid', tag', take', hCta', hHead', hBlock', hf, hq, hQ, hRef', rfl⟩ := hb
  have hg := Frame.lt_of_get hX he
  have hh := Frame.lt_of_get hX hf
  have hWg : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  have hWh : wgOf L h = 0 := RingRoleGeometry.of_trace hX hh (hs h hh).machine hq
  rcases same_head_lanes hpre hg (Wg0.warpLt hpre hWg) (Wg0.warpLt hpre hWh)
      (hCta.trans hCta'.symm) (hHead.trans hHead'.symm) with rfl | rfl
  · exact same_vote_reference hX hs he hf hd hq hD hQ (hBlock.trans hBlock'.symm) hRef hRef'
  · exact (Wg0PairedReference.reference_after_vote hpre hX hs ht hMax he hf hd hq hD hQ
      (hBlock'.trans hBlock.symm) hRef hRef').2

private theorem exact_vote_event {g j : Nat} {v : D} {e : Event} {take : Bool}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 v)))
    (hk : ∃ mode mask arg, e.kind = .voteMode mode mask arg take) :
    ∃ tag, X.get (g, j) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) v.voteTest take⟩ := by
  obtain ⟨mode, mask, arg, hKind⟩ := hk
  have hclass : voteClass e.kind ≠ none := by simp [hKind, voteClass]
  obtain ⟨o, hf⟩ := (Frame.trace hs hX (Frame.lt_of_get hX he)).fired_at he hd
  obtain ⟨v', r, hV, _, hVote⟩ := Wg0VoteSites.of_fired hf hclass
  have hv : v = v' := Machine.ThreadD.wg0.inj hV
  subst v'
  have hR : take = r := (Kind.voteMode.inj (hKind.symm.trans hVote)).2.2.2
  subst r
  obtain ⟨tag, kind⟩ := e
  cases hVote
  exact ⟨tag, he⟩

/-- The chosen reference agrees with every actual vote candidate of this CTA, block and head. -/
theorem canonical_pv_vote_reference
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (cta block : Nat) :
    PvVoteReference P L X cta block (canonicalPvReference P L X cta block) := by
  intro g j v mid e take hCta he hKind hd hD hBlock hUpdate
  obtain ⟨tag, hGet⟩ := exact_vote_event hX hs he hd hKind
  let head := Wg0.head L g
  have hw : VoteReferenceCandidate P L X cta block head (reference mid) :=
    ⟨g, j, v, mid, tag, take, hCta, rfl, hBlock, hGet, hd, hD, hUpdate, rfl⟩
  have hp : ∃ s, VoteReferenceCandidate P L X cta block head s := ⟨_, hw⟩
  have hMax : Wg0PairedReference.PairedBlockMax P L X :=
    Wg0PairedReference.actual_paired_block_max hpre hX hs ht (qk_values hpre hX hs)
  change reference mid = canonicalPvReference P L X cta block head
  unfold canonicalPvReference
  rw [dite_eq_left hp]
  exact candidate_unique hpre hX hs ht hMax hw (Classical.choose_spec hp)

/-- The old reference at an actual vote is the initial finite reference in block zero
and otherwise the canonical updated reference of the preceding block at this head. -/
theorem canonical_reference_before_vote {g j cta : Nat} {v : D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hc : ctaOf L g = cta) (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 v)))
    (hsite : v.site = .rescaleVote) :
    reference v = if v.block = 0 then negMaxReal else
      canonicalPvReference P L X cta (v.block - 1) (Wg0.head L g) := by
  rcases Wg0ReferencePrefix.before_vote hX hs ht he hd hsite with ⟨hZero, hRef⟩ |
    ⟨i, d, tag, take, mid, _, hf, hState, hSite, hBlock, hUpdate, hRef⟩
  · rw [ite_eq_left hZero]
    exact hRef
  · have hn : v.block ≠ 0 := by omega
    have hb : d.block = v.block - 1 := by omega
    rw [ite_eq_right hn, hRef, ← hb]
    exact canonical_pv_vote_reference hpre hX hs ht cta d.block hc hf
      ⟨.any, 2 ^ 32 - 1, d.voteTest, rfl⟩ hState hSite rfl hUpdate

/-- The actual vote's gain is the ratio of the preceding and current canonical reference
scales, using the initial finite reference for the first block. -/
theorem canonical_vote_gain {g i cta : Nat} {d mid : D} {e : Event} {take : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hc : ctaOf L g = cta) (he : X.get (g, i) = some e)
    (hKind : ∃ mode mask arg, e.kind = .voteMode mode mask arg take)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) (hUpdate : afterReferenceVote d take = some mid) :
    let head := Wg0.head L g
    let before := if d.block = 0 then negMaxReal else
      canonicalPvReference P L X cta (d.block - 1) head
    valFloat .f32 mid.gainWord =
      .ok ((2 : ℝ) ^ (before - canonicalPvReference P L X cta d.block head)) := by
  have hOld := canonical_reference_before_vote hpre hX hs ht hc he hd hsite
  have hNew := canonical_pv_vote_reference hpre hX hs ht cta d.block hc he hKind hd hsite
    rfl hUpdate
  obtain ⟨⟨m, hm⟩, _⟩ := Wg0VoteSuccessor.inputs_of_vote hpre hX hs ht
    (qk_values hpre hX hs) (Frame.lt_of_get hX he) (PTX.len_of_get he).le hd hsite
  obtain ⟨q, hq, _, hGain⟩ := afterReferenceVote_ratio m hm take
  rw [hUpdate] at hq
  obtain rfl := Option.some.inj hq
  rw [hOld, hNew] at hGain
  exact hGain

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
