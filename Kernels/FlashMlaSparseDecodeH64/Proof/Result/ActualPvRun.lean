-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.PvRescaledSeed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.RunOfReference
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.OutputTmemWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.SparseBlockTerms
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PvIssueHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PvObservedCommit

@[expose] public section

/-! # The actual PV recurrence for every observed output cell -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow PTX.AsyncCopy Protocol
open MmaDataTrace (pvAccum)
open Wg1Mma (tmemO batchOf queryOf)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The row run with each reference selected from the actual votes of its CTA. -/
def actualRowRun (P : Params) (L : Launch) (X : Execution) (g head : Nat) :
    Run P (batchOf L g) (queryOf L g) head :=
  Run.ofReference P _ _ head (fun b => canonicalPvReference P L X (ctaOf L g) b head)

/-- A completed last PV issue at each half and feature contains the corresponding run value. -/
theorem pv_cell_of_observed_issue {g src block observe : Nat} {rank : Fin 16}
    (head : Fin 64) (half : Fin 2) (col : Fin 256)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) g)
    (hSrc : Frame.stateAt (Machine.code P L) X g src =
      some (some (.mma ⟨.pvMma (pvHalfIssue half 3), block⟩)))
    (hTrack : TracksMma X (g, src) (g, observe))
    (hn : rank ∈ X.tcNotified (g, observe)) :
    TcMma.Result L Assumptions.all X (g, src)
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
      (.float .f32 ((actualRowRun P L X g head.val).O block (256 * half.val + col.val))) := by
  let run := actualRowRun P L X g head.val
  let feature := 256 * half.val + col.val
  induction block using Nat.strong_induction_on generalizing src observe rank with
  | h block ih =>
    obtain ⟨c, tag, sp, hIdx, hLater, hc, hOwn⟩ :=
      PvObservedCommit.own_commit_of_observed hpre hX hs hSrc hTrack
    obtain ⟨_, _, _, obsSpec, obsTag, hObs⟩ := hTrack
    have ho : X.Commit (g, observe) obsSpec := ⟨obsTag, hObs⟩
    let ref := canonicalPvReference P L X (ctaOf L g) block
    have hv : PvVoteValues P L X g block (gatheredValid P L g block) ref :=
      pv_vote_values_of_reference hpre hX hs ht hmma
        (canonical_pv_vote_reference hpre hX hs ht (ctaOf L g) block)
    cases block with
    | zero =>
      have hAcc : pvAccum 0 (pvHalfIssue half 0) = false :=
        PvInitialAccumulator.first_overwrites half
      obtain ⟨i, hDist, hVal⟩ := pv_result_of_observed_block hpre hX hs ht hc hOwn rfl
        ho hLater hn hv head half col 0 1 (fun _ _ => by
          rw [hAcc, zero_mul]
          exact .overwrite)
      have he : i = src := by omega
      rw [he, gathered_pv_sum_spec, zero_mul, zero_add] at hVal
      rw [run.O_zero]
      exact hVal
    | succ b =>
      have hPos : 0 < b + 1 := Nat.zero_lt_succ _
      let prior := run.O b feature
      let gain : ℝ := 2 ^ (run.c b - run.c (b + 1))
      obtain ⟨first, hFirst, hFirstState, hFirstIssue⟩ :=
        PvIssueHistory.pv_issue_of_commit hpre hX hs hc hOwn rfl (pvHalfIssue half 0)
      have hSeed := pv_rescaled_seed head half col prior hpre hX hs ht hmma
        hFirstIssue hFirstState hPos
        (fun {_ _ _} hState _ hTrackPrev hNotify =>
          ih b (Nat.lt_succ_self b) hState hTrackPrev hNotify)
      obtain ⟨i, hDist, hVal⟩ := pv_result_of_observed_block hpre hX hs ht hc hOwn rfl
        ho hLater hn hv head half col prior gain (fun j hJ => by
          have he : j = first := by omega
          subst j
          exact hSeed)
      have he : i = src := by omega
      rw [he, gathered_pv_sum_spec] at hVal
      change TcMma.Result L Assumptions.all X _ _ (.float .f32 (run.O (b + 1) feature))
      rw [show run.O (b + 1) feature = prior * gain + ∑ j ∈ Finset.range topkBlock,
        blockWeight P (batchOf L g) (queryOf L g) head.val (b + 1) j * 2 ^ (-ref head.val) *
        blockValue P (batchOf L g) (queryOf L g) (b + 1) j feature from
          Run.ofReference_O_succ P _ _ _ _ _ _]
      exact hVal

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
