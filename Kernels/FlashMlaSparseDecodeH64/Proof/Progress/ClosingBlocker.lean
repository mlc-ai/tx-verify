-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Closing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.WaitOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.CtaClosingTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Clc.ClcExecution
import Lemmas.Step.CtaBarFinishExit

public section

/-! # Missing participants of the closing CTA barrier -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem closing_priority {d : Machine.ThreadD} (hd : ClosingOrder.AfterClosing d) :
    completionTime P L g < priority P L g d := by
  cases d <;> simp only [ClosingOrder.AfterClosing] at hd
  all_goals simp [priority, softmaxTime, matmulTime, gatherTime, hd]

private theorem return_after_closing {d : Machine.ThreadD} (hd : ClosingProgress.ReturnSite d) :
    ClosingOrder.AfterClosing d := by
  cases d <;> first | exact hd | exact hd.elim

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
private theorem softmax_before_closing {d : Wg0.D} (hd : Wg0.Inv P L g d)
    (hn : d.site ≠ .exit) : softmaxTime P L g d ≤ completionTime P L g := by
  have hb := hd.blockLt
  have hSub := hd.subLt
  change d.block < Result.blocks P (ctaidY L g) at hb
  cases h : d.site <;> simp only [h, reduceCtorEq, not_false_eq_true] at hn
  all_goals try contradiction
  all_goals
    simp only [h, Wg0.Site.elems] at hSub
    simp only [softmaxTime, h, wg0Ordinal, completionTime, blockTime]
    omega

private theorem mma_before_closing {d : Wg1Mma.D} (hd : Wg1Mma.Inv P L g d)
    (hn : d.site ≠ .exit) : matmulTime P L g d ≤ completionTime P L g := by
  have hb : Wg1Mma.blocks P L g = Result.blocks P (ctaidY L g) := by
    unfold Wg1Mma.blocks Wg1Mma.total Wg1Mma.pad64 Wg1Mma.len0 Wg1Mma.len1
    rw [Result.blocks_eq_kernel]
    unfold Result.origPadded Result.ceilToMultiple Result.topkBlock
    congr 4
  have hI := hd.i_le
  rw [hb] at hI
  cases h : d.site
  case' exit => exact (hn h).elim
  all_goals
    simp only [matmulTime, h, mmaOrdinal, completionTime, blockTime]
    omega

set_option linter.unusedSimpArgs false in
private theorem tma_before_closing {d : Wg1Tma.D} (hd : Wg1Tma.Inv P L g d)
    (hn : d.site ≠ .exit) : gatherTime P L g d ≤ completionTime P L g := by
  have hb : totalBlocks d.len0 d.len1 = Result.blocks P (ctaidY L g) := by
    rw [hd.len0, hd.len1]
    rfl
  have hBlock := hd.block_le
  rw [hb] at hBlock
  cases h : d.site
  case' exit => exact (hn h).elim
  all_goals
    simp only [h, reduceCtorEq, false_or] at hBlock
    simp only [gatherTime, h, tmaOrdinal, completionTime, blockTime]
    omega

private theorem index_before_closing {d : Wg1Index.D} (hd : Wg1Index.Inv P L g d) :
    indexTime P L g d ≤ completionTime P L g := by
  have hb := hd.block
  rw [hd.len0, hd.len1] at hb
  change d.block < Result.blocks P (ctaidY L g) at hb
  cases h : d.site
  case' pair _ first high => cases first <;> cases high
  case' coord _ high => cases high
  all_goals
    simp only [indexTime, h, indexOrdinal, completionTime, blockTime]
    omega

private theorem quant_before_closing {d : Wg2.D} (hd : Wg2.Inv P L g d) :
    quantTime P L g d ≤ completionTime P L g := by
  have hb := hd.block
  rw [hd.len0, hd.len1] at hb
  change d.block < Result.blocks P (ctaidY L g) at hb
  cases h : d.site
  all_goals
    simp only [quantTime, h, wg2Ordinal, completionTime, blockTime]
    (try split) <;> omega

theorem before_closing_priority {d : Machine.ThreadD}
    (hi : (Machine.code P L g).inv d) (h : ¬ ClosingOrder.AfterClosing d) :
    priority P L g d ≤ completionTime P L g := by
  cases d
  case wg0 d => exact softmax_before_closing hi h
  case mma d => exact mma_before_closing hi h
  case tma d => exact tma_before_closing hi h
  case index d => exact index_before_closing hi
  case wg2 d => exact quant_before_closing hi
  case done => exact (h trivial).elim
  case idle s =>
    cases s
    case exit => exact (h rfl).elim
    all_goals simp [priority, completionTime, blockTime]
  case prologue s =>
    simp only [priority, completionTime, blockTime]
    omega
  case head =>
    simp [priority, completionTime, blockTime]

/-- A closing arrival either releases with unchanged traces or has a missing CTA participant
at an earlier dependency priority. -/
theorem bar12_release_or_earlier (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X)
    (hNoFault : ∀ Y, Consistent L kernel Assumptions.all mem0 Y → ¬ CtaBarFault L Y)
    (hLive : ∀ g, Frame.Pending L X g →
      ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    {tag : Nat} (he : X.IsBarrier (g, (X.tr g).length - 1) 12 none tag) :
    ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d) ∧
      ((∃ Y, Maximal L kernel Assumptions.all mem0 Y ∧ Y.tr = X.tr ∧ PTX.Step.Released L Y g) ∨
        ∃ other q, SameCta L g other ∧ Frame.Pending L X other ∧
          Frame.stateAt (Machine.code P L) X other (X.tr other).length = some (some q) ∧
          priority P L other q < priority P L g d) := by
  have hg := Frame.lt_of_get hmax.1 he
  have hLen : (X.tr g).length - 1 < (X.tr g).length := PTX.len_of_get he
  have hIndex : (X.tr g).length - 1 + 1 = (X.tr g).length := by omega
  have hAfter : ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d) ∧
      ClosingOrder.AfterClosing d := by
    rw [← hIndex]
    rcases CtaClosingTrace.after_arrival hpre hmax.1 hs ht he with
      ⟨d, hAt, hExit, _⟩ | ⟨d, hAt, hExit, _⟩
    · exact ⟨d, hAt, return_after_closing hExit⟩
    · exact ⟨.wg0 d, hAt, hExit⟩
  obtain ⟨d, hState, hAfter⟩ := hAfter
  refine ⟨d, hState, ?_⟩
  classical
  by_cases hall : ∀ lane < L.block, ∃ i eventTag,
      X.IsBarrier (g / L.block * L.block + lane, i) 12 none eventTag
  · exact .inl (closing_released hpre hmax hs ht hNoFault he hall)
  push Not at hall
  obtain ⟨lane, hLane, hMissing⟩ := hall
  let other := g / L.block * L.block + lane
  have hOther := PTX.NamedBar.cta_thread_lt (PTX.NamedBar.cta_lt hg) hLane
  have hGeo : other / L.block = g / L.block := by
    change (g / L.block * L.block + lane) / L.block = g / L.block
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hLane),
      Nat.div_eq_of_lt hLane, Nat.zero_add]
  have hSame : SameCta L g other := ⟨hg, hOther, hGeo.symm⟩
  have hp : Frame.Pending L X other := by
    refine ⟨hOther, ?_, ?_⟩
    · rintro ⟨_, _, hc⟩
      obtain ⟨i, s, tg, _, hIssue, _⟩ := hmax.1.clc.canceled_has_issue hc
      exact GlobalWrites.no_clc (i := i) (s := s) (tg := tg) hmax.1 hIssue
    · intro et hLast
      have hExit : X.get (other, (X.tr other).length - 1) = some ⟨et, .exit⟩ := by
        change (X.tr other)[(X.tr other).length - 1]? = _
        rwa [← List.getLast?_eq_getElem?]
      obtain ⟨j, _, t, hj⟩ := ClosingOrder.arrival_before_exit hpre hmax.1 hs ht hExit
      exact hMissing j t hj
  obtain ⟨q, hQ⟩ := hLive other hp
  have hNot : ¬ ClosingOrder.AfterClosing q := by
    intro hClosed
    obtain ⟨j, _, t, hj⟩ := ClosingOrder.arrival_before_state hpre hmax.1
      (hs other hOther).machine hOther hQ hClosed
    exact hMissing j t hj
  obtain ⟨t, hRun⟩ := Frame.run_some hmax.1 hub hp
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.end_at hs hp.1 hRun hQ
  have hRow : completionTime P L other = completionTime P L g := by
    simp only [completionTime, ctaidY, ctaOf, hGeo]
  refine .inr ⟨other, q, hSame, hp, hQ, ?_⟩
  exact lt_of_le_of_lt ((before_closing_priority hInv hNot).trans_eq hRow)
    (closing_priority hAfter)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
