-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0MassHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerContinuation
public import Lemmas.Kernel.Frame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0StateFields

@[expose] public section

/-! # The running maximum in the actual softmax trace -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0PeakHistory

open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {g : Nat} {X : Execution}

/-- The peak already includes the current block at the vote, before adding its probabilities. -/
def blocksSeen (d : D) : Nat :=
  d.block + if d.site = .rescaleVote ∨ Wg0MassHistory.updated d.site then 1 else 0

def EmptyPeak (d : D) : Prop := blocksSeen d = 0 ∧ d.peak = ⊥

def Retained (old d : D) : Prop := blocksSeen d = blocksSeen old ∧ d.peak = old.peak

def Extended (L : Launch) (old d : D) : Prop :=
  old.site = .maxRead ∧ d.site = .rescaleVote ∧ d.block = old.block ∧
    blocksSeen d = old.block + 1 ∧
    ∃ peer out, withPeerMax L old peer = some out ∧ d.peak = out.peak ∧ d.blockMax = out.blockMax

private theorem initialized (P : Params) (L : Launch) (g : Nat) : EmptyPeak (Wg0.init P L g) := by
  simp only [EmptyPeak, blocksSeen, Wg0.init, firstSite, afterSink, afterLen]
  split_ifs <;> simp_all [Wg0MassHistory.updated]

private theorem vote_peak {d d' : D} {take : Bool} (h : afterReferenceVote d take = some d') :
    d'.peak = d.peak := by
  unfold afterReferenceVote at h
  split at h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      rfl
    · cases h
  · cases h
    rfl

private theorem probability_peak {d d' : D} (h : probabilityUpdate L g d = some d') :
    d'.peak = d.peak := by
  unfold probabilityUpdate at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  rfl

private theorem decode_peak (m : WithBot ℝ) : decodePeak (peakVal m) = some m := by
  cases m with
  | bot => simp [decodePeak, peakVal]
  | coe x =>
    have hn : peakVal (↑x : WithBot ℝ) ≠ negInf := by simp [peakVal_eq_negInf]
    rw [decodePeak, ite_eq_right hn]
    simp [peakVal, valFloat_float, PTX.Proof.fl, Except.toOption]
    rfl

theorem extension_peak {old out : D} {peer : Value} {b : WithBot ℝ}
    (h : withPeerMax L old peer = some out) (hb : out.blockMax = peakVal b) :
    out.peak = max old.peak b := by
  unfold withPeerMax at h
  obtain ⟨m, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨peak, hpeak, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  change m = peakVal b at hb
  subst m
  rw [peerMaxE_peak] at hp
  change some (peakVal (max old.peak b)) = some p at hp
  cases hp
  rw [decode_peak] at hpeak
  cases hpeak
  rfl

set_option maxHeartbeats 3500000 in
private theorem role_step {old d : D} {e : Event}
    (hn : Wg0.next P L g old e = some (some d)) :
    EmptyPeak d ∨ Retained old d ∨ Extended L old d := by
  cases hOld : old.site <;> simp only [Wg0.next, nextSite, writeStep, waitStep, hOld] at hn
  case sink | lenOrig | lenExtra =>
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals left
    all_goals simp only [EmptyPeak, blocksSeen, Wg0.init, afterSink, afterLen]
    all_goals (try split_ifs) <;> simp_all [Wg0MassHistory.updated]
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨peer, _, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hm
        have hb := (peer_preserves_sub hv).1
        exact .inr (.inr ⟨hOld, rfl, hb, by simp [blocksSeen, hb], peer, v, hv, rfl, rfl⟩)
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨mid, hv, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨out, hp, rfl⟩ := Option.map_eq_some_iff.mp hm
      have hOldBlock := (vote_preserves_sub hv).1
      have hNewBlock := (probability_preserves_sub hp).1
      refine .inr (.inl ⟨?_, ?_⟩)
      · simp [blocksSeen, Wg0MassHistory.updated, hNewBlock, hOldBlock, hOld]
      · have hm : mid.peak = old.peak := vote_peak hv
        exact (probability_peak hp).trans hm
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals right; left
  all_goals
    simp only [Retained, blocksSeen, Wg0MassHistory.updated, hOld, loadScores, afterScoreSite,
      epiAfterBar, loadOutput]
  all_goals (try split_ifs) <;> simp_all

/-- A followed softmax state initializes the peak, retains it or incorporates the current block. -/
theorem composed_step {q : Machine.ThreadD} {d : D} {e : Event}
    (hn : Machine.next P L g q e = some (some (.wg0 d))) :
    EmptyPeak d ∨ ∃ old, q = .wg0 old ∧ (Retained old d ∨ Extended L old d) := by
  cases q
  case wg0 old =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i a hnext
      cases hn
      rcases role_step hnext with hz | hs
      · exact .inl hz
      · exact .inr ⟨old, rfl, hs⟩
    · split at hn <;> cases hn
    · cases hn
  case prologue p =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          exact .inl (initialized P L g)
        · cases hn
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

theorem blocksSeen_max_read {d : D} (h : d.site = .maxRead) :
    blocksSeen d = d.block := by
  simp [blocksSeen, h, Wg0MassHistory.updated]

theorem blocksSeen_epilogue {d : D} (h : d.site.inEpilogue = true) :
    blocksSeen d = d.block + 1 := by
  cases hs : d.site <;> simp_all [Wg0.Site.inEpilogue, blocksSeen, Wg0MassHistory.updated]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0PeakHistory
