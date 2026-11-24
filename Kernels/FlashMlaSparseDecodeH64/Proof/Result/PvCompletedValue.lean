-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualPvRun
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PvIssueHistory
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-! # A completed PV issue has actual values even before its commit is issued -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow MmaDataTrace Protocol
open PvAccumulatorSource (Issue)
open Wg1Mma (pvDest tmemO)

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem pv_done_before {g j i block : Nat} {earlier issue : Fin 8}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hOld : Issue L X g j block earlier) (hi : Issue L X g i block issue)
    (hEq : pvDest earlier = pvDest issue) (hLt : j < i)
    (hDone : X.async.mmaDone (g, i) = true) : X.async.mmaDone (g, j) = true := by
  apply hX.mmaCompletion (g, j) (g, i) _ hDone
  have hg := Frame.lt_of_get hX hOld.choose_spec
  refine ⟨rfl, hLt, ?_, ?_⟩
  · exact ⟨TcMma.sameWarp_self hg,
      .inl (TcMma.baseCausality_of_tc_po hOld.choose_spec rfl hLt (PTX.len_of_get hi.choose_spec)),
      _, _, _, _, _, _, _, _, hOld, hi, hEq, rfl, rfl, rfl, rfl⟩
  · refine ⟨_, _, _, _, _, _, _, _, hOld, hi, ?_, _, _, _, pvWriteCell L g block earlier 0 0⟩
    intro row col
    rw [hEq]
    rfl

/-- A completed PV cell has both its actual accumulator source and its result. -/
theorem pv_completed_cell {g i block : Nat} (half : Fin 2) (part : Fin 4)
    (head : Fin 64) (col : Fin 256)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) g)
    (hi : Issue L X g i block (pvHalfIssue half part))
    (hState : Frame.stateAt (Machine.code P L) X g i =
      some (some (.mma ⟨.pvMma (pvHalfIssue half part), block⟩)))
    (hDone : X.async.mmaDone (g, i) = true) :
    (∃ prev, GemmAccumulator L X (g, i)
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
      (pvAccum block (pvHalfIssue half part)) prev) ∧
    ∃ x : ℝ, TcMma.Result L Assumptions.all X (g, i)
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
      (.float .f32 x) := by
  let issue := pvHalfIssue half part
  let cell : TcMma.Cell :=
    ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
  have hPart := part.isLt
  have hHalf := half.isLt
  have hIssue : issue.val % 2 = half.val := by dsimp [issue, pvHalfIssue]; omega
  have hDest : pvDest issue = tmemO + 128 * half.val := by rw [pvDest, hIssue]
  have hSeed : ∃ x, GemmAccumulator L X (g, i) cell (pvAccum block issue) x := by
    by_cases hZero : part.val = 0
    · have hPartZero : part = 0 := Fin.ext hZero
      subst part
      by_cases hb : block = 0
      · subst block
        have hAcc : pvAccum 0 issue = false := PvInitialAccumulator.first_overwrites half
        exact ⟨0, hAcc ▸ .overwrite⟩
      · let run := actualRowRun P L X g head.val
        let prior := run.O (block - 1) (256 * half.val + col.val)
        have hPrev := pv_rescaled_seed head half col prior hpre hX hs ht hmma
          hi hState (by omega) (fun hSrc hOld hTrack hn =>
            pv_cell_of_observed_issue head half col hpre hX hs ht hmma hSrc hTrack hn)
        exact ⟨_, hPrev⟩
    · let oldPart : Fin 4 := ⟨part.val - 1, by omega⟩
      let previous := pvHalfIssue half oldPart
      let middle : Fin 8 := ⟨issue.val - 1, by have := issue.isLt; omega⟩
      have hPrevVal : previous.val + 2 = issue.val := by
        dsimp [previous, oldPart, issue, pvHalfIssue]
        omega
      have hMidVal : middle.val + 1 = issue.val := by dsimp [middle, issue, pvHalfIssue]; omega
      have hParity : previous.val % 2 = issue.val % 2 := by omega
      have hDifferent : middle.val % 2 ≠ previous.val % 2 := by omega
      have hPrevDest : pvDest previous = pvDest issue := by simp [pvDest, hParity]
      obtain ⟨j, hJ, hPrevState, hPrev⟩ :=
        PvIssueHistory.pv_issue_before hpre hX hs hi.choose_spec hState previous (by omega)
      obtain ⟨m, hM, _, hMid⟩ :=
        PvIssueHistory.pv_issue_before hpre hX hs hi.choose_spec hState middle (by omega)
      have hJIdx : j + 2 = i := by omega
      have hMIdx : j + 1 = m := by omega
      have hPrevDone := pv_done_before hX hPrev hi hPrevDest (by omega) hDone
      obtain ⟨x, hValue⟩ :=
        (pv_completed_cell half oldPart head col hpre hX hs ht hmma hPrev hPrevState hPrevDone).2
      have hRead := PvAccumulatorSource.previous_of_adjacent hpre hX hs ht hPrev
        (by rwa [hMIdx]) (by rwa [hJIdx]) hPrevState (by rwa [hJIdx]) hParity hDifferent head col
      rw [hJIdx, hPrevDest, hDest] at hRead
      have hAcc : pvAccum block issue = true := by
        have hLarge : 2 ≤ issue.val := by dsimp [issue, pvHalfIssue]; omega
        simp [pvAccum, hLarge]
      exact ⟨x, hAcc ▸ .priorMma hRead hValue⟩
  refine ⟨hSeed, ?_⟩
  obtain ⟨prev, hPrev⟩ := hSeed
  obtain ⟨ops, hObserved⟩ := observed_operands_of_done hX hDone
  let ref := canonicalPvReference P L X (ctaOf L g) block
  have hVotes : PvVoteValues P L X g block (gatheredValid P L g block) ref :=
    pv_vote_values_of_reference hpre hX hs ht hmma
      (canonical_pv_vote_reference hpre hX hs ht (ctaOf L g) block)
  have hA := pv_probability_operand hpre hX hs ht hi hState hObserved hVotes head col
  have hB := pv_value_operand (d := ⟨.pvMma issue, block⟩)
    hpre hX hs hState rfl hi hObserved col
  have hPrev' : GemmAccumulator L X (g, i)
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), pvDest issue + col.val % 128⟩
      (pvAccum block issue) prev := by
    rw [hDest]
    exact hPrev
  let raw := Wg2.gatheredByte P L g block
  let weight := blockProbability P L g head.val (ref head.val) raw (gatheredValid P L g block)
  let value := fun (slot feature : Nat) => dequant (raw slot) feature
  have hVal := pv_chunk_result hX.tma.2.1 hi hObserved head col weight value hA hB hPrev'
  rw [hDest] at hVal
  exact ⟨_, hVal⟩
termination_by part.val
decreasing_by omega

/-- The actual operands and same-half accumulator give a finite value for a completed PV chunk. -/
theorem pv_completed_value {g i block : Nat} (half : Fin 2) (part : Fin 4)
    (head : Fin 64) (col : Fin 256)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) g)
    (hi : Issue L X g i block (pvHalfIssue half part))
    (hState : Frame.stateAt (Machine.code P L) X g i =
      some (some (.mma ⟨.pvMma (pvHalfIssue half part), block⟩)))
    (hDone : X.async.mmaDone (g, i) = true) :
    ∃ x : ℝ, TcMma.Result L Assumptions.all X (g, i)
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
      (.float .f32 x) :=
  (pv_completed_cell half part head col hpre hX hs ht hmma hi hState hDone).2

/-- The model's completed-value obligation holds for each actual PV issue. -/
theorem pv_completed_values {g i block : Nat} {issue : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hi : Issue L X g i block issue)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.pvMma issue, block⟩))) :
    TcMma.CompletedValues L Assumptions.all X (g, i) := by
  obtain ⟨issuer, hIssuer⟩ := GemmRing.exists_issuer (cta := ctaOf L g) hpre hX
    (fun t ht' => (hs t ht').machine)
  have hThis := hIssuer g i _ rfl hState (by simp)
  subst issuer
  intro hDone cell hCell
  obtain ⟨_, _, _, _, row, col, hIssue, hWrite⟩ := hCell
  have hKind := congrArg Event.kind (Option.some.inj (hIssue.choose_spec.symm.trans hi.choose_spec))
  obtain ⟨rfl, rfl, rfl, rfl⟩ := TcKind.mma.inj (Kind.tc.inj hKind)
  have hGeom := TcMma.writeCell_resultCell hWrite
  have hBound : row < 64 ∧ col < 256 := by
    unfold TcMma.resultCell at hGeom
    dsimp only at hGeom
    split at hGeom
    · rename_i h
      exact ⟨h.2.2.1, h.2.2.2.1⟩
    · cases hGeom
  let head : Fin 64 := ⟨row, hBound.1⟩
  let channel : Fin 256 := ⟨col, hBound.2⟩
  let half : Fin 2 := ⟨issue.val % 2, Nat.mod_lt _ (by decide)⟩
  let part : Fin 4 := ⟨issue.val / 2, by have := issue.isLt; omega⟩
  have hk : pvHalfIssue half part = issue := Fin.ext (by dsimp [half, part, pvHalfIssue]; omega)
  have hEq := Option.some.inj (hWrite.symm.trans (pvWriteCell L g block issue head channel))
  obtain ⟨x, hx⟩ := pv_completed_value half part head channel hpre hX hs ht hIssuer
    (hk.symm ▸ hi) (hk.symm ▸ hState) hDone
  exact ⟨.float .f32 x, hEq ▸ hx⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
