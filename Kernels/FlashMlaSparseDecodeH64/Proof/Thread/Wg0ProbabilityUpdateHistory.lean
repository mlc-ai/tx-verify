-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0StateFields

@[expose] public section

/-! # Packed probability stores retain their same-block vote update -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ProbabilityUpdateHistory

open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def VoteStep (L : Launch) (g : Nat) (old d : D) (e : Event) : Prop :=
  old.site = .rescaleVote ∧ old.block = d.block ∧
    ∃ mode mask arg take mid, e.kind = .voteMode mode mask arg take ∧
      afterReferenceVote old take = some mid ∧
      ∃ out, probabilityUpdate L g {mid with voteTaken := take} = some out ∧ d.pw = out.pw

private def StoreStep (old d : D) : Prop :=
  (∃ k, old.site = .pStore k) ∧ old.block = d.block ∧ old.pw = d.pw

set_option maxHeartbeats 3000000 in
private theorem role_previous {g : Nat} {old d : D} {k : Fin 4} {e : Event}
    (hn : Wg0.next P L g old e = some (some d)) (hd : d.site = .pStore k) :
    VoteStep L g old d e ∨ StoreStep old d := by
  cases hOld : old.site <;> simp only [Wg0.next, nextSite, writeStep, waitStep, hOld] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hm
        cases hd
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · rename_i mode mask arg take hk
      obtain ⟨mid, hv, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨out, hp, rfl⟩ := Option.map_eq_some_iff.mp hm
      exact .inl ⟨hOld, (vote_preserves_sub hv).1.symm.trans
        (probability_preserves_sub hp).1.symm, mode, mask, arg, take, mid, hk, hv, out, hp, rfl⟩
    · cases hn
  case pStore k =>
    by_cases hk : k.val + 1 < 4 <;> simp only [hk, dite_true, dite_false] at hn
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals exact .inr ⟨⟨k, hOld⟩, rfl, rfl⟩
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp_all [Wg0.init, firstSite, afterSink, afterLen, afterScoreSite, epiAfterBar]
  all_goals repeat' split_ifs at hd

private theorem composed_previous {g : Nat} {q : Machine.ThreadD} {d : D} {k : Fin 4} {e : Event}
    (hn : Machine.next P L g q e = some (some (.wg0 d))) (hd : d.site = .pStore k) :
    ∃ old, q = .wg0 old ∧ (VoteStep L g old d e ∨ StoreStep old d) := by
  cases q
  case prologue p =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        fin_cases w <;> split_ifs at hn <;> cases hn
        simp only [Wg0.init, Wg0.firstSite, Wg0.afterSink, Wg0.afterLen] at hd
        repeat' split_ifs at hd
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  case wg0 old =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i st hnext
      cases hn
      exact ⟨old, rfl, role_previous hnext hd⟩
    · split at hn <;> cases hn
    · cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

/-- The successful reference vote and its probability update supply the stored weights,
with the same block index on both sides. -/
theorem probability_update_of_store {g i : Nat} {d : D} {site : Fin 4}
    (ht : Frame.Tracked (Machine.code P L) X) (hg : g < L.threads)
    (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .pStore site) :
    ∃ j v e mode mask arg take mid out, j < i ∧
      X.get (g, j) = some e ∧ e.kind = .voteMode mode mask arg take ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 v)) ∧
      v.site = .rescaleVote ∧ v.block = d.block ∧ afterReferenceVote v take = some mid ∧
      probabilityUpdate L g {mid with voteTaken := take} = some out ∧ d.pw = out.pw := by
  cases i with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ i =>
    have hi' : i < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hi'⟩
    obtain ⟨q, hq⟩ := Frame.stateAt_live ht hg hd (Nat.le_succ i)
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, hq] at hn
    obtain ⟨v, rfl, hPrev⟩ := composed_previous hn.symm hsite
    rcases hPrev with ⟨hVote, hBlock, mode, mask, arg, take, mid, hk, hv, out, hp, hPW⟩ |
      ⟨⟨k, hvSite⟩, hBlock, hPW⟩
    · exact ⟨i, v, e, mode, mask, arg, take, mid, out, Nat.lt_succ_self i, he, hk,
        hq, hVote, hBlock, hv, hp, hPW⟩
    · obtain ⟨j, v', w, mode, mask, arg, take, mid, out, hj, hw, hk, hv', hs, hb, hr, hp, hpp⟩ :=
        probability_update_of_store ht hg hi'.le hq hvSite
      exact ⟨j, v', w, mode, mask, arg, take, mid, out, Nat.lt_succ_of_lt hj, hw, hk,
        hv', hs, hb.trans hBlock, hr, hp, hPW.symm.trans hpp⟩
termination_by i

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ProbabilityUpdateHistory
