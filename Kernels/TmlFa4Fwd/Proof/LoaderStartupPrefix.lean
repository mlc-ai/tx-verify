-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderBatchSelect

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

private theorem suffixAtEvent {X : Execution} {g pos j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hp : pos ≤ j) : (X.tr g).drop pos ≠ [] :=
  fun h => Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp he).1
    ((List.drop_eq_nil_iff.mp h).trans hp)

private theorem indexOfDifferent {X : Execution} {g pos j : Nat} {a b : Event}
    (ha : X.get (g, pos) = some a) (hb : X.get (g, j) = some b)
    (hle : pos ≤ j) (hDiff : a ≠ b) : pos + 1 ≤ j := by
  by_contra h
  have he : pos = j := by omega
  exact hDiff (Option.some.inj (ha.symm.trans (he ▸ hb)))

/-- Any cue to the next collective fixes the actual first loader metadata. -/
private theorem loaderCuQCursorOfDemand {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    {e : Event} (he : X.get (g, j) = some e)
    (hDemand : 186 < e.pc ∨ e.kind = .exit ∨ 3 ≤ j ∧ Execution.isShfl e = true) :
    let pos := if laneOf l g ≤ p.batch then 7 else 6
    ∃ t ending, pos ≤ j ∧ At t 187 (loaderCuQFacts p l g (warpIndex l g)) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending ∧
      ((X.tr g).take pos).countP Execution.isShfl = 3 ∧
      ((X.tr g).take pos).countP isFullWarpVote = 0 := by
  obtain ⟨s, ending, hIndex, hs, hTid, hRun, hFence, hBar⟩ :=
    nonzeroCommonPrefixOfDemand hp hX hg (by omega) he (hDemand.imp_left (by omega))
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  have hAt : At s 174 (loaderBarrierFacts p l g warp.val) := by
    have h := hs.2.2.2.2
    have hAbi : Holds s.regs (abiFacts p l) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    apply hs.mono
    rw [loaderBarrierFacts, holds_append]
    exact ⟨⟨h.1, h.2.1, hAbi⟩, hTid, trivial⟩
  obtain ⟨inst, u, hh, hu, hTail⟩ :=
    loaderHintObservedPrefix hp hg warp hw hAt hRun (suffixAtEvent he hIndex)
  have differs {a : Event} (hPc : a.pc ≤ 186) (hExit : a.kind ≠ .exit)
      (hShuffle : Execution.isShfl a = false) : a ≠ e := by
    rintro rfl
    rcases hDemand with h | h | ⟨_, h⟩
    · omega
    · exact hExit h
    · cases hShuffle.symm.trans h
  have hSix := indexOfDifferent hh he hIndex
    (differs (by change 179 ≤ 186; decide) (by intro h; cases h) rfl)
  obtain ⟨t, ht, hRead, htRun⟩ := loaderCuQReadyInPrefix hp hX hu hTail
    (suffixAtEvent he hSix) (hProtected _)
  have takeStep {k : Nat} {a : Event} (ha : X.get (g, k) = some a) :
      (X.tr g).take (k + 1) = (X.tr g).take k ++ [a] := by
    rw [List.take_add_one, show (X.tr g)[k]? = some a from ha]
    rfl
  have hLength : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have h0 := List.getElem?_eq_getElem (show 0 < (X.tr g).length by omega)
  have h1 := List.getElem?_eq_getElem (show 1 < (X.tr g).length by omega)
  have h2 := List.getElem?_eq_getElem (show 2 < (X.tr g).length by omega)
  have hCounts : ((X.tr g).take 6).countP Execution.isShfl = 3 ∧
      ((X.tr g).take 6).countP isFullWarpVote = 0 := by
    rw [show 6 = 5 + 1 by decide, takeStep hh, takeStep hBar, takeStep hFence,
      takeStep h2, takeStep h1, takeStep h0,
      firstSharedValue hp hX g hg h0, secondWarpValue hp hX g hg h1,
      thirdWarpValue hp hX g hg h2]
    exact ⟨rfl, rfl⟩
  by_cases hReadLane : laneOf l g ≤ p.batch
  · have hSeven := indexOfDifferent (hRead hReadLane) he hSix
      (differs (by change 186 ≤ 186; decide) (by intro h; cases h) rfl)
    refine ⟨t, ending, by simpa [hReadLane] using hSeven, ht,
      by simpa [hReadLane] using htRun, ?_⟩
    rw [ite_eq_left hReadLane, show 7 = 6 + 1 by decide, takeStep (hRead hReadLane)]
    simpa only [List.countP_append, List.countP_singleton, Execution.isShfl, isFullWarpVote,
      isWarpVote, voteClass, Option.any, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using hCounts
  · exact ⟨t, ending, by simpa [hReadLane] using hSix, ht,
      by simpa [hReadLane] using htRun, by simpa [hReadLane] using hCounts⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g src j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
include hp hX hg hw hSrc hProtected

/-- A later event forces the first actual loader shuffle of every lane in its warp. -/
theorem loaderWarpFirstShuffleOfEvent {target : Event}
    (he : X.get (warpLane l g src, j) = some target) (hPc : 187 < target.pc) :
    ∃ ending, ∃ cur : SchedulerWarpAt l X g 188 (fun lane =>
      (1707, b32 (drainCuQ p (shflSource .down lane 1 31).1)) ::
        loaderCuQFacts p l (warpLane l g lane) (warpIndex l g)) 4 0 ending,
      WarpFollowsEvent l X g cur.pos src j target := by
  let thread := warpLane l g
  let pos := fun lane => if lane ≤ p.batch then 7 else 6
  let frame := fun lane => loaderCuQFacts p l (thread lane) (warpIndex l g)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hWarp (lane : Nat) (hl : lane < 32) := (Step.sameWarp_lane hBlock hg hl).1
  have hWarpEq (lane : Nat) (hl : lane < 32) : warpIndex l g = warpIndex l (thread lane) :=
    (hWarp lane hl).2
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (thread lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  obtain ⟨seed, ending, hSeed, hAt, hr, hShfl, _⟩ :=
    loaderCuQCursorOfDemand hp hX (hWarp src hSrc).1.2.1 (hWarpEq src hSrc ▸ hw)
      hProtected he (.inl (by omega))
  let step := fun val (_ : Bool) => next (setReg seed 1707 val)
  have hNext : Next kernel Assumptions.all l (thread src) seed seed
      (.shfl .down (b32 (drainCuQ p (laneOf l (thread src)))) 1 31 step) :=
    ⟨.refl, loaderDownTemplate hp hAt⟩
  obtain ⟨recv, ok, hObserved, hOrdinal, _⟩ :=
    hNext.shuffle_at_nonempty hr (suffixAtEvent he hSeed) hShfl
  have hCursors (lane : Nat) (hl : lane < 32) : ∃ t ending, At t 187 (frame lane) ∧
      Run kernel Assumptions.all l (thread lane) t ((X.tr (thread lane)).drop (pos lane)) ending ∧
      ((X.tr (thread lane)).take (pos lane)).countP Execution.isShfl = 3 ∧
      ((X.tr (thread lane)).take (pos lane)).countP isFullWarpVote = 0 ∧
      ∀ k < pos lane, ∀ pc, X.get (thread lane, k) ≠ some ⟨pc, .exit⟩ := by
    have hSame := Step.sameWarp_trans (sameWarp_symm (hWarp src hSrc)) (hWarp lane hl)
    have hDemand : ∃ k e, X.get (thread lane, k) = some e ∧
        (186 < e.pc ∨ e.kind = .exit ∨ 3 ≤ k ∧ Execution.isShfl e = true) := by
      rcases Step.shfl_lane_of_ready hX hObserved hOrdinal hSame with
        ⟨k, ⟨⟨pc, md, a, b, c, val, yes, hGet⟩, hCount⟩⟩ | ⟨k, pc, hGet, _⟩
      · have hIndex : 3 ≤ k :=
          hCount.symm.le.trans ((List.countP_le_length ..).trans (List.length_take_le ..))
        exact ⟨k, _, hGet, .inr (.inr ⟨hIndex, rfl⟩)⟩
      · exact ⟨k, _, hGet, .inr (.inl rfl)⟩
    obtain ⟨i, e, hGet, hNeed⟩ := hDemand
    obtain ⟨s, stop, hBefore, hs, hRun, hS, hV⟩ := loaderCuQCursorOfDemand hp hX
      (hWarp lane hl).1.2.1 (hWarpEq lane hl ▸ hw) hProtected hGet hNeed
    let site := if laneOf l (thread lane) ≤ p.batch then 7 else 6
    have hSite : site = pos lane := by simp only [site, pos, hLane lane hl]
    have hAt : At s 187 (loaderCuQFacts p l (thread lane) (warpIndex l (thread lane))) := hs
    rw [← hWarpEq lane hl] at hAt
    change site ≤ i at hBefore
    change Run kernel Assumptions.all l (thread lane) s
      ((X.tr (thread lane)).drop site) stop at hRun
    change ((X.tr (thread lane)).take site).countP Execution.isShfl = 3 at hS
    change ((X.tr (thread lane)).take site).countP isFullWarpVote = 0 at hV
    rw [hSite] at hBefore hRun hS hV
    have hs : At s 187 (frame lane) := hAt
    refine ⟨s, stop, hs, hRun, hS, hV, ?_⟩
    intro k hk pc hExit
    have hLast : k + 1 = (X.tr (thread lane)).length :=
      Execution.exit_last hX (hWarp lane hl).1.2.1 hExit
    have hLength : i < (X.tr (thread lane)).length := (List.getElem?_eq_some_iff.mp hGet).1
    change (if lane ≤ p.batch then 7 else 6) ≤ i at hBefore
    change k < (if lane ≤ p.batch then 7 else 6) at hk
    omega
  let _ : Nonempty TState := ⟨seed⟩
  choose! states ending hAt hRun hS hV hExit using hCursors
  let cur : SchedulerWarpAt l X g 187 frame 3 0 ending :=
    ⟨pos, states, states, ⟨hS, hV⟩, hRun, fun _ _ => .refl, hAt⟩
  have hBefore : WarpFollowsEvent l X g pos src j target := by
    have h : (if laneOf l (thread src) ≤ p.batch then 7 else 6) ≤ j := hSeed
    rw [hLane src hSrc] at h
    exact ⟨hSrc, he, h, hExit⟩
  have hFresh : ∀ lane < 32, ∀ pair ∈ frame lane, pair.1 ≠ 1707 := by
    intro lane _ pair hMember hEq
    have hReg := List.mem_map_of_mem (f := Prod.fst) hMember
    rw [hEq] at hReg
    exact (of_decide_eq_true rfl : 1707 ∉ (frame lane).map Prod.fst) hReg
  have hOut (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (thread lane) (cur.state lane) = .ev
        (.shfl .down (b32 (drainCuQ p lane)) 1 31
          (fun val _ => next (setReg (cur.state lane) 1707 val))) := by
    simpa only [hLane lane hl] using loaderDownTemplate hp (cur.checkpoint lane hl)
  obtain ⟨ready, hAdvance⟩ :=
    cur.consumeShuffleTo hp hX hg .down (fun lane => b32 (drainCuQ p lane))
      (fun _ => 1) (fun _ => 31) hFresh hOut (.inr hBefore) hPc
  exact ⟨ending, ready, hAdvance hBefore⟩

/-- A priming copy is downstream of the actual first loader search decision.
The selected case reaches the first-group ballot, and the other reaches its fallback scan. -/
theorem loaderFirstScheduleOfEvent {target : Event} (he : X.get (warpLane l g src, j) = some target)
    (hPc : 226 < target.pc) :
    ∃ ending, ∃ cur : SchedulerWarpAt l X g
      (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 288 else 231)
      (loaderFirstRouteFacts p l g (warpIndex l g)) 10 0 ending,
      WarpFollowsEvent l X g cur.pos src j target := by
  obtain ⟨ending, cur, hFollows⟩ :=
    loaderWarpFirstShuffleOfEvent hp hX hg hw hSrc hProtected he (by omega)
  obtain ⟨ready, hAdvance⟩ := loaderFirstScheduleTo hp hX hg cur (.inr hFollows) hPc
  exact ⟨ending, ready, hAdvance hFollows⟩

/-- A late copy in a first-group CTA fixes the selected request through the actual ballot. -/
theorem loaderFirstBatchOfEvent (hCTA : g / l.block < tilePrefix p (min p.batch 31) * p.heads)
    {target : Event} (he : X.get (warpLane l g src, j) = some target) (hPc : 297 < target.pc) :
    ∃ batch < min p.batch 31,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      ∃ ending, ∃ cur : SchedulerWarpAt l X g 302
        (loaderChosenFacts p l g (warpIndex l g) 0 batch) 10 1 ending,
        WarpFollowsEvent l X g cur.pos src j target := by
  have hRoute := loaderFirstScheduleOfEvent hp hX hg hw hSrc hProtected he (by omega)
  rw [ite_eq_left hCTA] at hRoute
  obtain ⟨ending, cur, hFollows⟩ := hRoute
  obtain ⟨batch, hIn, hLo, hHi, chosen, hAdvance⟩ := loaderFirstBatchTo hp hX hg hCTA cur
    (.inr hFollows) hPc
  exact ⟨batch, hIn, hLo, hHi, ending, chosen, hAdvance hFollows⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
