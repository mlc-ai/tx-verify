-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerContinuation
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # Score-load values carried through the WG0 peer exchange -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The peer exchange carries both score-load lists unchanged. -/
def ScoreExchangeSite : Site → Prop
  | .exchStore _ | .pairBar | .peerRead _ | .rowMax => True
  | _ => False

set_option maxHeartbeats 1500000 in
private theorem score_exchange_prev {d q : D} {e : Event}
    (hn : Wg0.next P L g q e = some (some d)) (hsite : ScoreExchangeSite d.site) :
    ((q.site = .maskRead ∧ ∃ a bs, e.kind = .rd a bs ∧
        rebuild 3 bs = .ok (.bits 32 d.maskWord)) ∨
      (ScoreExchangeSite q.site ∧ d.maskWord = q.maskWord)) ∧
      d.block = q.block ∧ d.ownScores = q.ownScores ∧ d.peerScores = q.peerScores := by
  cases hq : q.site <;>
    simp only [Wg0.next, nextSite, writeStep, waitStep, hq] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        exact hsite.elim
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      exact hsite.elim
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [ScoreExchangeSite, afterScoreSite, afterLen, afterSink, epiAfterBar,
    loadScores, init]
  all_goals
    split_ifs at hsite <;> exact hsite.elim

private theorem composed_score_exchange_prev {d : D} {e : Event} {s : Machine.ThreadD}
    (hn : Machine.next P L g s e = some (some (.wg0 d))) (hsite : ScoreExchangeSite d.site) :
    ∃ q : D, s = .wg0 q ∧ ((q.site = .maskRead ∧ ∃ a bs, e.kind = .rd a bs ∧
        rebuild 3 bs = .ok (.bits 32 d.maskWord)) ∨
      (ScoreExchangeSite q.site ∧ d.maskWord = q.maskWord)) ∧
      d.block = q.block ∧ d.ownScores = q.ownScores ∧ d.peerScores = q.peerScores := by
  cases s with
  | wg0 q =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i r hr
      cases hn
      exact ⟨q, rfl, score_exchange_prev hr hsite⟩
    · split_ifs at hn <;> cases hn
    · cases hn
  | prologue s =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          unfold init firstSite afterSink afterLen at hsite
          split_ifs at hsite <;> exact hsite.elim
        · cases hn
      · cases hn
    · cases hn
  | head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  | _ =>
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

/-- The exchange retains the score lists and the actual word returned at its block's mask load. -/
theorem mask_event_before_exchange {i : Nat} {d : D}
    (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : ScoreExchangeSite d.site) :
    ∃ j q e a bs, j < i ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      X.get (g, j) = some e ∧ q.site = .maskRead ∧ d.block = q.block ∧
      d.ownScores = q.ownScores ∧ d.peerScores = q.peerScores ∧ e.kind = .rd a bs ∧
      rebuild 3 bs = .ok (.bits 32 d.maskWord) := by
  induction i generalizing d with
  | zero =>
    rw [Frame.stateAt_zero] at hd
    cases hd
  | succ k ih =>
    have hk : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    rw [Frame.stateAt_succ he] at hd
    cases hr : Frame.stateAt (Machine.code P L) X g k with
    | none =>
      simp [hr] at hd
    | some state =>
      rw [hr, Option.bind_some] at hd
      cases state with
      | none =>
        change (some none : Option (Option Machine.ThreadD)) = some (some (.wg0 d)) at hd
        cases hd
      | some s =>
        change Machine.next P L g s e = some (some (.wg0 d)) at hd
        obtain ⟨q, rfl, hprev, hb, ho, hp⟩ := composed_score_exchange_prev hd hsite
        rcases hprev with ⟨hmask, a, bs, hKind, hWord⟩ | ⟨hqsite, hMask⟩
        · exact ⟨k, q, e, a, bs, Nat.lt_succ_self k, hr, he, hmask, hb, ho, hp, hKind, hWord⟩
        · obtain ⟨j, r, f, a, bs, hj, hstate, hget, hmask, hblock, hown, hpeer, hKind, hWord⟩ :=
            ih (Nat.le_of_lt hk) hr hqsite
          rw [← hMask] at hWord
          exact ⟨j, r, f, a, bs, Nat.lt_trans hj (Nat.lt_succ_self k), hstate, hget, hmask,
            hb.trans hblock, ho.trans hown, hp.trans hpeer, hKind, hWord⟩

/-- The two score-load lists at the exchange belong to the earlier mask state of that block. -/
theorem mask_words_before_exchange {i : Nat} {d : D}
    (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : ScoreExchangeSite d.site) :
    ∃ j q, j < i ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      q.site = .maskRead ∧ d.block = q.block ∧
      d.ownScores = q.ownScores ∧ d.peerScores = q.peerScores := by
  obtain ⟨j, q, _, _, _, hj, hq, _, hmask, hb, hown, hpeer, _, _⟩ :=
    mask_event_before_exchange hlen hd hsite
  exact ⟨j, q, hj, hq, hmask, hb, hown, hpeer⟩

/-- To identify the real score words of an exchange state, it suffices to identify the words at
its actual earlier mask event. This also handles a thread paused at its next exchange state. -/
theorem real_scores_from_mask {i : Nat} {d : D}
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : ScoreExchangeSite d.site)
    (hmask : ∀ j q e, X.get (g, j) = some e →
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) →
      q.site = .maskRead → RealScores q.ownScores ∧ RealScores q.peerScores) :
    RealScores d.ownScores ∧ RealScores d.peerScores := by
  let k := min i (X.tr g).length
  have hlen : k ≤ (X.tr g).length := Nat.min_le_right _ _
  have hk : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)) := by
    by_cases h : i ≤ (X.tr g).length
    · simpa only [k, Nat.min_eq_left h] using hd
    · have hle : (X.tr g).length ≤ i := by omega
      rw [Frame.stateAt_of_le hle] at hd
      rw [show k = (X.tr g).length from Nat.min_eq_right hle]
      exact hd
  obtain ⟨j, q, hj, hq, hmaskSite, _, hown, hpeer⟩ := mask_words_before_exchange hlen hk hsite
  have hjlt : j < (X.tr g).length := by omega
  obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e := ⟨_, List.getElem?_eq_getElem hjlt⟩
  rw [hown, hpeer]
  exact hmask j q e he hq hmaskSite

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
