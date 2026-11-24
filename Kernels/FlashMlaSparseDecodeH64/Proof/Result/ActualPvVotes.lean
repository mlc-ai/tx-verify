-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualPvBlock
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualScoreSums

@[expose] public section

/-! # The remaining numerical vote input is its actual reference -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The updated reference of each actual vote for a block, indexed by its logical head. -/
def PvVoteReference (P : Params) (L : Launch) (X : Execution) (cta block : Nat)
    (ref : Nat → ℝ) : Prop :=
  ∀ {lane j : Nat} {v mid : Wg0.D} {e : Event} {take : Bool},
    ctaOf L lane = cta →
    X.get (lane, j) = some e →
    (∃ mode mask arg, e.kind = .voteMode mode mask arg take) →
    Frame.stateAt (Machine.code P L) X lane j = some (some (.wg0 v)) →
    v.site = .rescaleVote → v.block = block →
    Wg0.afterReferenceVote v take = some mid →
    Wg0.reference mid = ref (Wg0.head L lane)

/-- Real QK scores and index bits determine all the probabilities once the actual vote
references are known. -/
theorem pv_vote_values_of_reference {g block : Nat} {ref : Nat → ℝ}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) g)
    (hVotes : PvVoteReference P L X (ctaOf L g) block ref) :
    PvVoteValues P L X g block (gatheredValid P L g block) ref := by
  intro lane j v mid e take hCta he hVote hState hSite hBlock hStep
  dsimp only
  refine ⟨hVotes hCta he hVote hState hSite hBlock hStep, fun p => ?_⟩
  have hIssuer : GemmRing.MmaIssuer P L X (ctaOf L lane) g := hCta.symm ▸ hmma
  have hPair := actual_vote_scores_from_indices hpre hX hs ht hIssuer hCta.symm
    (Frame.lt_of_get hX he) (PTX.len_of_get he).le hState hSite p
  have hValid : gatheredValid P L lane block = gatheredValid P L g block := by
    funext pos
    exact gatheredValid_same_cta hCta
  dsimp only at hPair
  rw [hBlock, hValid] at hPair
  have hDiv : lane / L.block = g / L.block := hCta
  simpa only [blockScore, blockDot, Wg0.head, Wg1Mma.batchOf, Wg1Mma.queryOf, Wg1Mma.ctaOf,
    hDiv] using hPair

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
