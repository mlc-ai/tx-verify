-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ReferenceHistory

@[expose] public section

/-! # A softmax lane's next vote uses its preceding vote's reference update -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ReferencePrefix

open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An ordinary role step preserves the reference, except for its initial input reads.
A vote step carries the reference update through the probability calculation. -/
theorem reference_step {g : Nat} {old d : D} {e : Event}
    (hn : Wg0.next P L g old e = some (some d)) :
    (old.site ≠ .rescaleVote ∧
      ((reference d = reference old ∧ d.voteTaken = old.voteTaken ∧
          d.gainWord = old.gainWord) ∨
        ((old.site = .sink ∨ old.site = .lenOrig ∨ old.site = .lenExtra) ∧
          reference d = negMaxReal))) ∨
    (old.site = .rescaleVote ∧ ∃ mode mask input take mid,
      e.kind = .voteMode mode mask input take ∧
      afterReferenceVote old take = some mid ∧ reference d = reference mid ∧
      d.voteTaken = take ∧ d.gainWord = mid.gainWord) := by
  cases hd : old.site <;> simp only [Wg0.next, nextSite, writeStep, waitStep, hd] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hMap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, hPeer, rfl⟩ := Option.map_eq_some_iff.mp hMap
        simp only [withPeerMax, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hPeer
        obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := hPeer
        exact .inl ⟨by simp, .inl ⟨rfl, rfl, rfl⟩⟩
      · cases hn
    · cases hn
  case scoreLoad a k =>
    split at hn
    · split at hn
      · cases hn
        exact .inl ⟨by simp, .inl (by unfold loadScores; split <;> exact ⟨rfl, rfl, rfl⟩)⟩
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · rename_i mode mask input take hKind
      obtain ⟨mid, hVote, hMap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, hProbability, rfl⟩ := Option.map_eq_some_iff.mp hMap
      simp only [probabilityUpdate, bind, Option.bind_eq_some_iff,
        pure, Option.some.injEq] at hProbability
      obtain ⟨_, _, _, _, rfl⟩ := hProbability
      exact .inr ⟨rfl, mode, mask, input, take, mid, hKind, hVote, rfl, rfl, rfl⟩
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals first
    | exact .inl ⟨by simp, .inl ⟨rfl, rfl, rfl⟩⟩
    | exact .inl ⟨by simp, .inr ⟨by simp, rfl⟩⟩

private theorem role_or_entry {g : Nat} {q : Machine.ThreadD} {e : Event} {d : D}
    (hn : Machine.next P L g q e = some (some (.wg0 d))) :
    d = Wg0.init P L g ∨ ∃ v, q = .wg0 v ∧ Wg0.next P L g v e = some (some d) := by
  cases q
  case prologue p =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          exact .inl rfl
        · cases hn
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  case wg0 v =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i s hNext
      cases hn
      exact .inr ⟨v, rfl, hNext⟩
    · split_ifs at hn <;> cases hn
    · cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

private theorem ordinal_at_entry (P : Params) (L : Launch) (g : Nat) :
    Wg0VoteCount.ordinal (Wg0.init P L g) = 0 := by
  unfold Wg0VoteCount.ordinal Wg0.init Wg0.firstSite Wg0.afterSink Wg0.afterLen
  dsimp only
  split_ifs <;> rfl

private theorem event_count_step {g i : Nat} {e : Event} (he : X.get (g, i) = some e) :
    ((X.tr g).take (i + 1)).countP Wg0VoteCount.countsVote =
      ((X.tr g).take i).countP Wg0VoteCount.countsVote + (Wg0VoteCount.countsVote e).toNat := by
  change (X.tr g)[i]? = some e at he
  rw [List.take_add_one, he, Option.toList_some, List.countP_append]
  cases hk : Wg0VoteCount.countsVote e <;> simp [hk]

private theorem no_vote_count {g : Nat} {q : D} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.wg0 q)) e o) (hQ : q.site ≠ .rescaleVote) :
    Wg0VoteCount.countsVote e = false := by
  have hk : voteClass e.kind = none := by
    by_contra hn
    obtain ⟨d, _, hEq, hs, _⟩ := Wg0VoteSites.of_fired hf hn
    exact hQ ((Machine.ThreadD.wg0.inj hEq) ▸ hs)
  simp only [Wg0VoteCount.countsVote, hk, Option.any_none]

private theorem vote_count_true {e : Event} {mask : Nat} {p take : Bool}
    (he : e.kind = .voteMode .any mask p take) :
    (voteClass e.kind).any (·.mask == mask) = true := by
  simp only [he, voteClass, Option.any_some, beq_self_eq_true]

private theorem origin {g i : Nat} {d : D} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) :
    (Wg0VoteCount.ordinal d = 0 ∧ reference d = negMaxReal) ∨
      ∃ j v tag take mid, j < i ∧
        X.get (g, j) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) v.voteTest take⟩ ∧
        Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 v)) ∧
        v.site = .rescaleVote ∧ v.block + 1 = Wg0VoteCount.ordinal d ∧
        afterReferenceVote v take = some mid ∧ reference d = reference mid ∧
        d.voteTaken = take ∧ d.gainWord = mid.gainWord := by
  have hg := Frame.lt_of_get hX he
  cases i with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ i =>
    have hLen : i < (X.tr g).length := by have := PTX.len_of_get he; simp only at this; omega
    obtain ⟨f, hf⟩ : ∃ f, X.get (g, i) = some f := ⟨_, List.getElem?_eq_getElem hLen⟩
    obtain ⟨q, hq⟩ := Frame.stateAt_live ht hg hd (Nat.le_succ i)
    have hn := Frame.stateAt_succ (C := Machine.code P L) hf
    rw [hd, hq] at hn
    rcases role_or_entry hn.symm with rfl | ⟨v, rfl, hStep⟩
    · exact .inl ⟨ordinal_at_entry P L g, rfl⟩
    obtain ⟨o, hFired⟩ := (Frame.trace hs hX hg).fired_at hf hq
    have hCountOld := Wg0VoteCount.count_at_wg0 hX (hs g hg).machine hf hq
    have hCountNew := Wg0VoteCount.count_at_wg0 hX (hs g hg).machine he hd
    have hCount := event_count_step hf
    rw [hCountOld, hCountNew] at hCount
    rcases reference_step hStep with ⟨hNot, ⟨hStable, hTake, hGain⟩ | ⟨hReset, hZeroRef⟩⟩ |
      ⟨hVote, mode, mask, input, take, mid, hKind, hv, hRef, hTake, hGain⟩
    · rw [no_vote_count hFired hNot] at hCount
      have hEq : Wg0VoteCount.ordinal d = Wg0VoteCount.ordinal v :=
        hCount.trans (Nat.add_zero _)
      rcases origin hX hs ht hf hq with ⟨hn, hRef⟩ |
        ⟨j, q', tag, r, after, hj, hGet, hState, hsite, hb, hAfter, hRef, hVote, hWord⟩
      · exact .inl ⟨hEq.trans hn, hStable.trans hRef⟩
      · exact .inr ⟨j, q', tag, r, after, by omega, hGet, hState, hsite,
          hb.trans hEq.symm, hAfter, hStable.trans hRef, hTake.trans hVote, hGain.trans hWord⟩
    · rw [no_vote_count hFired hNot] at hCount
      have hOrd : Wg0VoteCount.ordinal v = 0 := by
        rcases hReset with hd | hd | hd <;> rw [Wg0VoteCount.ordinal, hd]
      exact .inl ⟨by rw [hCount, hOrd]; rfl, hZeroRef⟩
    · have hClass : voteClass f.kind ≠ none := by simp [hKind, voteClass]
      obtain ⟨q, r, hQ, _, hActual⟩ := Wg0VoteSites.of_fired hFired hClass
      have hQ' : v = q := Machine.ThreadD.wg0.inj hQ
      subst q
      have hr : take = r := (Kind.voteMode.inj (hKind.symm.trans hActual)).2.2.2
      subst r
      have hYes : Wg0VoteCount.countsVote f = true := vote_count_true hActual
      have hOrd : Wg0VoteCount.ordinal v = v.block := by
        rw [Wg0VoteCount.ordinal, hVote]
        exact Nat.add_zero _
      rw [hYes, hOrd] at hCount
      change Wg0VoteCount.ordinal d = v.block + 1 at hCount
      have hGet : X.get (g, i) = some ⟨f.pc, .voteMode .any (2 ^ 32 - 1) v.voteTest take⟩ := by
        rw [hf]
        cases f
        cases hActual
        rfl
      exact .inr ⟨i, v, f.pc, take, mid, Nat.lt_succ_self i, hGet, hq, hVote,
        hCount.symm, hv, hRef, hTake, hGain⟩
termination_by i

variable {g i : Nat} {d : D} {e : Event} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
include hX hs ht he hd

/-- The first reference vote uses the fixed initial reference. Every later actual vote
uses the reference computed by the preceding block's actual vote in that lane. -/
theorem before_vote (hsite : d.site = .rescaleVote) :
    (d.block = 0 ∧ reference d = negMaxReal) ∨
      ∃ j v tag take mid, j < i ∧
        X.get (g, j) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) v.voteTest take⟩ ∧
        Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 v)) ∧
        v.site = .rescaleVote ∧ v.block + 1 = d.block ∧
        afterReferenceVote v take = some mid ∧ reference d = reference mid := by
  have h := origin hX hs ht he hd
  have hOrd : Wg0VoteCount.ordinal d = d.block := by
    rw [Wg0VoteCount.ordinal, hsite]
    exact Nat.add_zero _
  rw [hOrd] at h
  rcases h with h | ⟨j, v, tag, take, mid, hj, hGet, hState, hSite, hb, hAfter, hRef, _, _⟩
  · exact .inl h
  · exact .inr ⟨j, v, tag, take, mid, hj, hGet, hState, hSite, hb, hAfter, hRef⟩

/-- A reached state after its block's vote retains the actual decision and gain. -/
theorem after_vote (hOrd : Wg0VoteCount.ordinal d = d.block + 1) :
    ∃ j v tag take mid, j < i ∧
      X.get (g, j) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) v.voteTest take⟩ ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 v)) ∧
      v.site = .rescaleVote ∧ v.block = d.block ∧
      afterReferenceVote v take = some mid ∧ reference d = reference mid ∧
      d.voteTaken = take ∧ d.gainWord = mid.gainWord := by
  rcases origin hX hs ht he hd with ⟨hZero, _⟩ |
    ⟨j, v, tag, take, mid, hj, hGet, hState, hSite, hb, hAfter, hRef, hTake, hGain⟩
  · omega
  · exact ⟨j, v, tag, take, mid, hj, hGet, hState, hSite, by omega, hAfter, hRef, hTake, hGain⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ReferencePrefix
