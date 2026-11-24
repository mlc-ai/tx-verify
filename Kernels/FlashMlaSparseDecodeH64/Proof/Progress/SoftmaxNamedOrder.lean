-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.WaitOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount

public section

/-! # Dependency priority of one softmax barrier generation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX Wg0 _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
/-- A lane that has issued no more barriers than the waiting arrival's source prefix has
not passed that arrival's instruction priority. -/
theorem softmax_before_bar9_priority {P : Params} {L : Launch} {g h : Nat} {d q : D}
    (hRow : ctaidY L g = ctaidY L h)
    (hd : Inv P L g d) (hq : Inv P L h q) (hBar : Wg0BarrierTrace.Bar9Site d.site)
    (hOrdinal : Wg0BarrierCount.ordinal q ≤ Wg0BarrierCount.ordinal d) :
    softmaxTime P L h q ≤ softmaxTime P L g d := by
  have hDLt := hd.blockLt
  have hQLt := hq.blockLt
  have hDLast := hd.epilogueLast
  have hQLast := hq.epilogueLast
  have hDSub := hd.subLt
  have hQSub := hq.subLt
  simp only [blocksOf, eOf, ← hRow] at hDLt hQLt hDLast hQLast
  clear hd hq
  cases hD : d.site <;> simp only [Wg0BarrierTrace.Bar9Site, hD] at hBar
  all_goals cases hQ : q.site
  all_goals
    simp only [Wg0BarrierCount.ordinal, Wg0BarrierCount.localOrdinal, hD, hQ] at hOrdinal
    simp [hD, Site.inEpilogue, Site.elems] at hDSub hDLast
    simp [hQ, Site.inEpilogue, Site.elems] at hQSub hQLast
    simp only [softmaxTime, hD, hQ, wg0Ordinal, blockTime, completionTime, ← hRow]
    omega

/-- The actual softmax barrier transition advances its dependency priority. -/
theorem softmax_after_bar9_priority {P : Params} {L : Launch} {g : Nat} {d : D} {e : Event}
    (hBar : Wg0BarrierTrace.Bar9Site d.site) (he : e.kind = .bar 9 (some 128) .sync) :
    ∃ d', Wg0.next P L g d e = some (some d') ∧
      softmaxTime P L g d < softmaxTime P L g d' := by
  cases hD : d.site <;> simp only [Wg0BarrierTrace.Bar9Site, hD] at hBar
  case epiBar j =>
    refine ⟨{ d with site := epiAfterBar L g j }, by simp [Wg0.next, Wg0.nextSite, hD, he], ?_⟩
    unfold epiAfterBar
    split_ifs
    all_goals simp only [softmaxTime, hD, wg0Ordinal, blockTime]
    all_goals omega
  case' wg0Sync => refine ⟨{ d with site := .maskReady }, ?_, ?_⟩
  case' wg0Sync2 => refine ⟨{ d with site := .validFree }, ?_, ?_⟩
  case' lseBar => refine ⟨{ d with site := .lseStore0 }, ?_, ?_⟩
  case' lseBar2 => refine ⟨{ d with site := .lseRead }, ?_, ?_⟩
  all_goals
    first
    | (solve | simp only [Wg0.next, Wg0.nextSite, hD, he])
    | simp only [softmaxTime, hD, wg0Ordinal, blockTime]; omega

/-- Every prologue state precedes any softmax barrier priority. -/
theorem prologue_before_bar9_priority {P : Params} {L : Launch} {g h : Nat} {d : D}
    {s : Machine.PSite} (hBar : Wg0BarrierTrace.Bar9Site d.site) :
    priority P L h (.prologue s) < softmaxTime P L g d := by
  cases hD : d.site <;> simp only [Wg0BarrierTrace.Bar9Site, hD] at hBar
  all_goals simp only [priority, softmaxTime, hD, wg0Ordinal, blockTime]
  all_goals omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
