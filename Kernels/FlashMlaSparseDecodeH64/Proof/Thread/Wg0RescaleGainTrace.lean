-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Rescale
import Lemmas.Flow.Final

@[expose] public section

/-! # The gain retained from the same-block reference vote -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0RescaleGainTrace

open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {X : Execution} {g : Nat}

/-- The probability stores and rescale tiles all retain the gain from their common vote. -/
def GainSite : Wg0.Site → Prop
  | .pStore _ | .rescaleFence | .rescaleLoad _ | .rescaleWait _
  | .rescaleStore _ | .rescaleWaitSt _ | .rescaleFenceB => True
  | _ => False

set_option maxHeartbeats 1500000 in
private theorem role_previous {q d : D} {e : Event}
    (hn : Wg0.next P L g q e = some (some d)) (hd : GainSite d.site) :
    (q.site = .rescaleVote ∨ (GainSite q.site ∧ d.gainWord = q.gainWord)) ∧
      (d.site.inRescale = true → 0 < d.block ∨
        q.site.inRescale = true ∧ d.block = q.block) ∧
      (∀ k, d.site = .rescaleWait k → q.site = .rescaleLoad k ∧ d.block = q.block) := by
  cases hq : q.site <;>
    simp only [Wg0.next, nextSite, writeStep, waitStep, hq] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        cases hd
      · cases hn
    · cases hn
  case rescaleVote =>
    refine ⟨.inl rfl, ?_⟩
    split at hn
    · obtain ⟨_, _, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hm
      simp [Wg0.Site.inRescale]
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [GainSite, afterScoreSite, afterLen, afterSink, epiAfterBar, loadScores, init,
    Wg0.Site.inRescale]
  all_goals try (split_ifs at hd)
  all_goals try contradiction
  all_goals simp_all [wantsRescale]
  all_goals omega

private theorem composed_previous {q : Machine.ThreadD} {d : D} {e : Event}
    (hn : Machine.next P L g q e = some (some (.wg0 d))) (hd : GainSite d.site) :
    ∃ s : D, q = .wg0 s ∧
      (s.site = .rescaleVote ∨ (GainSite s.site ∧ d.gainWord = s.gainWord)) ∧
      (d.site.inRescale = true → 0 < d.block ∨
        s.site.inRescale = true ∧ d.block = s.block) ∧
      (∀ k, d.site = .rescaleWait k → s.site = .rescaleLoad k ∧ d.block = s.block) := by
  cases q with
  | wg0 q =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i _ hr
      cases hn
      exact ⟨q, rfl, role_previous hr hd⟩
    · split_ifs at hn <;> cases hn
    · cases hn
  | prologue q =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          unfold init firstSite afterSink afterLen at hd
          split_ifs at hd <;> cases hd
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

/-- The gain at a reached rescale site is the gain of the actual vote successor. -/
theorem gain_from_vote {i : Nat} {d : D}
    (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : GainSite d.site) :
    ∃ j e q u, j < i ∧ X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧ q.site = .rescaleVote ∧
      Machine.next P L g (.wg0 q) e = some (some (.wg0 u)) ∧ d.gainWord = u.gainWord := by
  cases i with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ j =>
    have hj : j < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨q, hq⟩ := FollowedPrefix.state_at hd (Nat.le_succ j)
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, hq] at hn
    obtain ⟨s, rfl, hstep, _, _⟩ := composed_previous hn.symm hsite
    rcases hstep with hVote | ⟨hGain, hEq⟩
    · exact ⟨j, e, s, d, by omega, he, hq, hVote, hn.symm, rfl⟩
    · obtain ⟨k, ev, q, u, hk, he, hq, hVote, hnext, heq⟩ :=
        gain_from_vote hj.le hq hGain
      exact ⟨k, ev, q, u, by omega, he, hq, hVote, hnext, hEq.trans heq⟩
termination_by i

/-- The first-block test prevents a reached rescale state in block zero. -/
theorem rescale_block_pos {i : Nat} {d : D}
    (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site.inRescale = true) : 0 < d.block := by
  cases i with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ j =>
    have hj : j < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨q, hq⟩ := FollowedPrefix.state_at hd (Nat.le_succ j)
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, hq] at hn
    have hGain : GainSite d.site := by
      cases hs : d.site <;> simp_all [GainSite, Wg0.Site.inRescale]
    obtain ⟨s, rfl, _, hNext, _⟩ := composed_previous hn.symm hGain
    rcases hNext hsite with h | ⟨hs, heq⟩
    · exact h
    · rw [heq]
      exact rescale_block_pos hj.le hq hs
termination_by i

/-- A reached rescale load wait follows its actual tile load and retains all its words. -/
theorem load_before_wait {mem0 : Mem0} {i : Nat} {d : D} {tile : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleWait tile) :
    ∃ j q, j + 1 = i ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      q.site = .rescaleLoad tile ∧ q.block = d.block ∧
      X.TLd (g, j) (64 * tile.val) d.rescaleWords .s32x32b ∧ d.rescaleWords.length = 64 := by
  cases i with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ j =>
    have hj : j < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨r, hr⟩ := FollowedPrefix.state_at hd (Nat.le_succ j)
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, hr] at hn
    have hGain : GainSite d.site := by rw [hsite]; trivial
    obtain ⟨q, rfl, _, _, hBefore⟩ := composed_previous hn.symm hGain
    obtain ⟨hqs, hb⟩ := hBefore tile hsite
    change some (some (.wg0 d)) = Machine.next P L g (.wg0 q) e at hn
    obtain ⟨_, _, o, hat, _, hc, hf⟩ := Frame.fired_site hs hX he hr
    cases o with
    | none =>
      have hkind := fires_none_ends hf
      rcases hkind with ⟨f, hKind⟩ | hKind
      · simp [Machine.next, Wg0.next, nextSite, hqs, hKind] at hn
      · simp [Machine.next, Wg0.next, nextSite, hqs, hKind] at hn
    | some u =>
      obtain ⟨words, hw, hk, _⟩ := fires_rescaleLoad hpre hqs hat hc hf
      simp only [Machine.next, Wg0.next, nextSite, hqs, hk, Option.some.injEq,
        Machine.ThreadD.wg0.injEq] at hn
      have hdWords := congrArg D.rescaleWords hn
      change d.rescaleWords = words at hdWords
      refine ⟨j, q, rfl, hr, hqs, hb.symm, ?_, hdWords.symm ▸ hw⟩
      rw [hdWords]
      cases e
      exact ⟨_, he.trans (congrArg some (congrArg (Event.mk _) hk))⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0RescaleGainTrace
