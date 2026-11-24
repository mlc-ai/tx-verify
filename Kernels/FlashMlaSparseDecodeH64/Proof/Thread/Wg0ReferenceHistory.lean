-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0MaxTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteBranch

@[expose] public section

/-! # The input of an actual softmax vote comes from its row maximum and old reference -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ReferenceHistory

open PTX PTX.Proof PTX.Flow PTX.Assumption Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem peer_comparison {g : Nat} {q d : D} {e : Event}
    (hsite : q.site = .maxRead)
    (hn : Machine.next P L g (.wg0 q) e = some (some (.wg0 d))) :
    ∃ gap, subE true d.blockMax (miVal d) = .ok gap ∧
      setpE (.ord .gt) true gap (b32 1086324736) = .ok d.voteTest := by
  simp only [Machine.next] at hn
  split at hn
  · rename_i v hNext
    cases hn
    simp only [Wg0.next, nextSite, hsite] at hNext
    split at hNext
    · split at hNext
      · obtain ⟨_, _, hMap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hNext)
        obtain ⟨_, hPeer, rfl⟩ := Option.map_eq_some_iff.mp hMap
        simp only [withPeerMax, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hPeer
        obtain ⟨m, hm, p, hp, peak, hPeak, gap, hGap, test, hTest, rfl⟩ := hPeer
        refine ⟨gap, ?_, ?_⟩
        · change subE true m (miVal q) = .ok gap
          cases h : subE true m (miVal q) <;> simp_all [Except.toOption]
        · change setpE (.ord .gt) true gap (b32 1086324736) = .ok test
          cases h : setpE (.ord .gt) true gap (b32 1086324736) <;> simp_all [Except.toOption]
      · cases hNext
    · cases hNext
  · split_ifs at hn <;> cases hn
  · cases hn

/-- At the actual vote, its predicate is the comparison of the row's block maximum with
the lane's old exponent reference. -/
theorem comparison_at_vote {g i : Nat} {d : D}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hg : g < L.threads)
    (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) :
    ∃ gap, subE true d.blockMax (miVal d) = .ok gap ∧
      setpE (.ord .gt) true gap (b32 1086324736) = .ok d.voteTest := by
  obtain ⟨j, e, q, hj, he, hq, hMax, _⟩ :=
    Wg0MaxTrace.maxRead_before_vote hX hs hg hi hd hsite
  have hn : Machine.next P L g (.wg0 q) e = some (some (.wg0 d)) := by
    rw [← hj, Frame.stateAt_succ he, hq] at hd
    exact hd
  exact peer_comparison hMax hn

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ReferenceHistory
