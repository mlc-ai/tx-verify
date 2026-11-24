-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.WaitOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0TcRank
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0TcPositions

public section

/-! # The collective ordinal bounds the dependency priority of a softmax peer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX Wg0 TcCollectiveSites
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {g h : Nat} {d q : D} {vote : Nat → Bool}

private theorem local_time_bound
    (hq : Inv P L h q) (hE : q.site.inEpilogue = false) :
    softmaxTime P L h q < blockTime (q.block + 1) 0 := by
  have hSub := hq.subLt
  clear hq
  cases hQ : q.site <;> simp only [Site.inEpilogue, hQ, Bool.true_eq_false] at hE
  all_goals
    simp only [softmaxTime, hQ, wg0Ordinal, blockTime]
    simp only [hQ, Site.elems] at hSub
    omega

private theorem data_time_bound (hd : Inv P L g d) (hSite : DataSite d.site) :
    blockTime d.block 0 ≤ softmaxTime P L g d := by
  have hLt := hd.blockLt
  change d.block < Result.blocks P (ctaidY L g) at hLt
  generalize hD : d.site = s at hSite
  cases hSite <;> simp only [softmaxTime, hD, wg0Ordinal, blockTime] <;> omega

private theorem earlier_block_time (hRow : ctaidY L g = ctaidY L h)
    (hd : Inv P L g d) (hq : Inv P L h q) (hData : DataSite d.site)
    (hLt : q.block < d.block) :
    softmaxTime P L h q ≤ softmaxTime P L g d := by
  have hNotEpilogue : q.site.inEpilogue = false := by
    by_contra hb
    have hLast := hq.epilogueLast (Bool.eq_true_of_not_eq_false hb)
    have hBound := hd.blockLt
    simp only [blocksOf, eOf, hRow] at hBound hLast
    omega
  exact (local_time_bound hq hNotEpilogue).le.trans
    ((by unfold blockTime; omega :
      blockTime (q.block + 1) 0 ≤ blockTime d.block 0).trans (data_time_bound hd hData))

private theorem block_le_of_collective_rank (hd : Inv P L g d) (hq : Inv P L h q)
    (hRow : ctaidY L g = ctaidY L h)
    (hData : DataSite d.site) (hSched : Wg0TcRank.Scheduled vote d)
    (hQ : q.site ≠ .sink ∧ q.site ≠ .lenOrig ∧ q.site ≠ .lenExtra)
    (hr : Wg0TcRank.rank vote q ≤ Wg0TcRank.rank vote d) : q.block ≤ d.block := by
  by_contra! hLt
  have hNoEpi : d.site.inEpilogue = false := by
    by_contra hn
    have hb := hd.epilogueLast (Bool.eq_true_of_not_eq_false hn)
    have hqLt := hq.blockLt
    simp only [blocksOf, eOf, hRow] at hb hqLt
    omega
  have hRank := (Wg0TcPositions.interval hSched hData hd.rescaleArm).2
  simp only [Wg0TcPositions.blockIndex, hNoEpi, Bool.false_eq_true, ↓reduceIte] at hRank
  have hBound : Wg0TcPositions.beforeBlock vote q.block ≤ Wg0TcRank.rank vote q := by
    cases hSite : q.site <;> simp [hSite] at hQ
    all_goals simp only [Wg0TcPositions.beforeBlock, Wg0TcRank.rank, hSite]; omega
  have hPrev := Wg0TcPositions.beforeBlock_mono vote (show d.block + 1 ≤ q.block by omega)
  omega

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2800000 in
private theorem same_block_time (hRow : ctaidY L g = ctaidY L h)
    (hd : Inv P L g d) (hq : Inv P L h q) (hData : DataSite d.site)
    (hDSched : Wg0TcRank.Scheduled vote d) (hQSched : Wg0TcRank.Scheduled vote q)
    (hBlock : q.block = d.block)
    (hr : Wg0TcRank.rank vote q ≤ Wg0TcRank.rank vote d) :
    softmaxTime P L h q ≤ softmaxTime P L g d := by
  have hLt := hd.blockLt
  have hDSub := hd.subLt
  have hQSub := hq.subLt
  have hDTrue := hd.rescaleArm
  have hCommon
      (hD : d.site.inRescale = true ∨ Wg0TcRank.pastRescale d.site = true)
      (hQ : q.site.inRescale = true ∨ Wg0TcRank.pastRescale q.site = true) :
      q.rescale = d.rescale := by rw [hQSched.2 hQ, hDSched.2 hD, hBlock]
  clear hd hq hDSched hQSched
  change d.block < Result.blocks P (ctaidY L g) at hLt
  have hToNat (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
  have hNatD := hToNat d.rescale
  have hNatQ := hToNat q.rescale
  generalize hD : d.site = s at hData
  cases hData <;> cases hQ : q.site
  all_goals
    simp [hD, Site.inRescale] at hDTrue
    simp [hD, hQ, Site.inRescale, Wg0TcRank.pastRescale] at hCommon
    simp only [hD, hQ, Site.elems] at hDSub hQSub
    simp only [softmaxTime, hD, hQ, wg0Ordinal, blockTime, completionTime, hBlock, ← hRow]
    simp only [Wg0TcRank.rank, hD, hQ, Wg0TcRank.blockOffset,
      Wg0TcRank.pastRescale, hBlock, Bool.false_eq_true, ↓reduceIte] at hr
    try (rw [hCommon] at hr)
    try (rw [hDTrue] at hr)
    try simp only [Bool.true_eq, Bool.toNat_true, ↓reduceIte] at hr
    omega

/-- At a missing ordinal in the same softmax schedule, the peer is no later than the
collective that another lane already issued. -/
theorem softmax_before_data_priority (hRow : ctaidY L g = ctaidY L h)
    (hd : Inv P L g d) (hq : Inv P L h q) (hData : DataSite d.site)
    (hDSched : Wg0TcRank.Scheduled vote d) (hQSched : Wg0TcRank.Scheduled vote q)
    (hr : Wg0TcRank.rank vote q ≤ Wg0TcRank.rank vote d) :
    softmaxTime P L h q ≤ softmaxTime P L g d := by
  by_cases hEarly : q.site = .sink ∨ q.site = .lenOrig ∨ q.site = .lenExtra
  · have hSmall : softmaxTime P L h q ≤ blockTime d.block 0 := by
      rcases hEarly with hQ | hQ | hQ <;>
        simp only [softmaxTime, hQ, wg0Ordinal, blockTime] <;> omega
    exact hSmall.trans (data_time_bound hd hData)
  push Not at hEarly
  have hLe := block_le_of_collective_rank hd hq hRow hData hDSched hEarly hr
  rcases lt_or_eq_of_le hLe with hLt | hEq
  · exact earlier_block_time hRow hd hq hData hLt
  · exact same_block_time hRow hd hq hData hDSched hQSched hEq hr

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
/-- Advancing through a followed Tensor Memory data event increases the dependency priority. -/
theorem softmax_after_data_priority {e : Event}
    (hData : DataSite d.site) (hn : Wg0.next P L g d e = some (some q)) :
    softmaxTime P L g d < softmaxTime P L g q := by
  generalize hD : d.site = s at hData
  cases hData
  all_goals simp only [Wg0.next, Wg0.nextSite, hD] at hn
  all_goals repeat' split at hn
  all_goals simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals cases hn
  all_goals
    simp only [softmaxTime, hD, wg0Ordinal, blockTime, afterScoreSite, loadScores, loadOutput]
    try split_ifs
    all_goals (try simp only [softmaxTime, wg0Ordinal, blockTime]); omega

/-- The shared prologue precedes every Tensor Memory data instruction. -/
theorem prologue_before_data_priority {s : Machine.PSite} (hData : DataSite d.site) :
    priority P L h (.prologue s) < softmaxTime P L g d := by
  generalize hD : d.site = site at hData
  cases hData <;> simp only [priority, softmaxTime, hD, wg0Ordinal, blockTime] <;> omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
