-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundKeySlot
import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundHighShuffleFloor
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKFirstPrefix
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Proof.TerminalSite

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

set_option maxRecDepth 100000 in
private theorem warmRoundKeyObservedLane {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g lane batch iteration j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (pair : Fin 16) {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hPc : 1003 < e.pc) (hRound : WarmRoundDemand p l X g lane batch iteration j e)
    (hSecond : 8 ≤ pair.val → 1072 < e.pc)
    (hLater : warmKShufflePc pair < e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
        primingSearchShuffleCount batch + 64 + 64 * iteration + 2 * pair.val + 1))
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let row := warmKInputRow (Mma.trips p batch co.1 - 2 - iteration) tid pair
    let ptr := primingKRowPointer p batch (co.2 / 6) row
    ∃ pos ≤ j, ∃ ending, Nonempty (PointerBroadcastInPrefix l X thread pos
      (primingSearchShuffleCount batch + 64 + 64 * iteration + 2 * pair.val)
      (warmKShufflePc pair) ptr
      (warmKShuffleOutput pair) (pair.val % 8) (warmKSlotWords pair ptr tid) ending) := by
  obtain ⟨index, hBefore, s, ending, hs, hr, hRank⟩ :=
    warmRoundKeySlotOfEvent hp hX hFrame hg hw hl hCTA hb hLo hHi pair he hPc
      hRound hSecond hLater hSafe
  let start := warmKInputPc pair
  let stop := warmKShufflePc pair
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let row := warmKInputRow (Mma.trips p batch co.1 - 2 - iteration) tid pair
  let ptr := primingKRowPointer p batch (co.2 / 6) row
  let F := warmKSlotWords pair ptr tid
  let ordinal := primingSearchShuffleCount batch + 64 + 64 * iteration + 2 * pair.val
  have hRange : 174 ≤ start ∧ start ≤ stop ∧ stop ≤ 1901 := by fin_cases pair <;> decide
  have hCount : warmKInputRank pair + loaderShuffleTail stop start = 64 + 2 * pair.val := by
    fin_cases pair <;> kernel_rfl
  have hAudit (n : Nat) : ((kernel.code.drop start).take (stop - start)).all
      (fun i => loaderPipelineCutOp start stop n (F.map Prod.fst) i.op) = true := by
    fin_cases pair <;> kernel_rfl
  have hRanked : (((kernel.code.drop start).take (stop - start)).zipIdx start).all
      (fun (i, pc) => LoaderRankedInstr stop pc i) = true := by fin_cases pair <;> kernel_rfl
  have hDemand : stop ≤ e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr thread).take index).countP Execution.isShfl + loaderShuffleTail stop start ≤
        ((X.tr thread).take j).countP Execution.isShfl) := by
    rcases hLater with h | ⟨hMark, hNth⟩
    · exact .inl h.le
    · exact .inr ⟨hMark, by rw [hRank, hNth]; omega⟩
  obtain ⟨u, front, ending', _, hu, huRun, huRank, huBefore⟩ :=
    prefixRankedShuffleCut hRange hAudit hRanked hs hr he hBefore hDemand hSafe
  have huNth : ((X.tr thread).take (index + front.length)).countP Execution.isShfl = ordinal := by
    rw [huRank, hRank]
    unfold ordinal
    omega
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hScope : 174 ≤ stop ∧ stop + 1 < 1906 := by fin_cases pair <;> decide
  have hFresh : ∀ r ∈ F, r.1 ≠ warmKShuffleOutput pair ∧
      r.1 ≠ warmKShuffleOutput pair + 1 := by
    intro r hm
    have h := List.mem_map_of_mem (f := Prod.fst) hm
    have ha : (F.map Prod.fst).all
        (fun n => decide (n ≠ warmKShuffleOutput pair ∧ n ≠ warmKShuffleOutput pair + 1)) =
        true := by fin_cases pair <;> kernel_rfl
    exact of_decide_eq_true (List.all_eq_true.mp ha _ h)
  refine ⟨index + front.length, huBefore, ending', ?_⟩
  refine pointerBroadcastObserved (F := F) (base := ptr) (src := warmKShuffleInput pair)
    hBlock hScope (Nat.mod_lt _ (by decide)) (warmKShuffleCode pair 0) (warmKShuffleCode pair 1)
    hFresh hu (by simp [F, warmKSlotWords]) (by simp [F, warmKSlotWords]) huRun huNth
    (traceAfterObservedEvent he huBefore) ?_
  intro low hGet hLow _
  apply traceAfterObservedEvent he
  by_contra! hNo
  have hEq : index + front.length = j := by omega
  rw [hEq] at hGet
  have same := Option.some.inj (hGet.symm.trans he)
  rcases hLater with hLate | ⟨_, hCount⟩
  · rw [← same, hLow] at hLate
    exact (Nat.lt_irrefl _) hLate
  · rw [← hEq, huNth] at hCount
    unfold ordinal at hCount
    omega

set_option maxRecDepth 100000 in
/-- Every K pair consumes the actual subgroup pointer of its observed warm round. -/
theorem warmRoundKeyPairBroadcastOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g src j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (pair : Fin 16) (upper : Bool) {sp : AsyncCopy.Spec}
    (he : X.get (warpLane l g src, j) =
      some ⟨packetPlanePc (recurringPacketSite 0) pair upper, .copy sp⟩)
    (hRequest : ((X.tr (warpLane l g src)).take j).countP Execution.isShfl =
      primingSearchShuffleCount batch + 64 + 64 * iteration + 2 * pair.val + 2) :
      let co := assignedCoordinates p batch (g / l.block)
      let thread := warpLane l g src
      let sender := warpLane l g (warmKShuffleSender src pair)
      let tid := thread % l.block
      let row := warmKInputRow (Mma.trips p batch co.1 - 2 - iteration) (sender % l.block) pair
      let ptr := primingKRowPointer p batch (co.2 / 6) row
      ∃ pos ending s, pos + 2 ≤ j ∧ At s (warmKShufflePc pair + 2) (warmKPairInputs pair ptr tid) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop (pos + 2)) ending ∧
        ((X.tr thread).take (pos + 2)).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 + 64 * iteration + 2 * pair.val + 2 := by
  let pc := packetPlanePc (recurringPacketSite 0) pair upper
  let shflPc := warmKShufflePc pair
  let e : Event := ⟨pc, .copy sp⟩
  have hOrdered : 1003 < pc ∧ shflPc + 1 < pc ∧ pc < 1353 := by
    fin_cases pair <;> cases upper <;> decide
  have hSecond : 8 ≤ pair.val → 1072 < pc := by fin_cases pair <;> cases upper <;> decide
  have hExitPc : shflPc < 9205 := by fin_cases pair <;> decide
  have hEvent : X.get (warpLane l g src, j) = some e := he
  have writes (w a data loc) (hw : X.MemWrites w a data) (hc : a.Covers loc)
      (hg : loc.space = .global) : p.oRegion.Contains loc ∨ p.lseRegion.Contains loc := by
    rcases hFrame w a data loc hw hc hg with ho | ⟨q, hq, head, hh, k, hk, rfl⟩
    · exact .inl ho
    · exact .inr (lseByte_in hq hh hk)
  have hSafe : ∀ f, e.kind ≠ .ub f := by intro f h; cases h
  have hRound : WarmRoundDemand p l X g src batch iteration j e :=
    ⟨.inr hOrdered.2.2, .inr (by rw [hRequest]; omega)⟩
  have hCan := (warmRoundEntryOfEvent hp hX hg hw hSrc writes hCTA hb hLo hHi hEvent
    (show 917 ≤ pc by omega) hSafe hRound).1
  have hWarm : HasWarmTile p l g := by
    refine ⟨batch, hb, hLo, hHi, ?_⟩
    have hBelow := hCan.trans_le (Nat.min_le_left _ _)
    omega
  obtain ⟨b, hb', hlo, hhi, _, cur, _⟩ :=
    loaderPrimingEntryOfActiveEvent hp hX hg hw hSrc (hp.cuQ_protected writes)
      hCTA hEvent (show 308 < pc by omega)
  obtain ⟨_, _, only⟩ := tileBatch_existsUnique p hCTA
  have hbEq : b = batch := (only b ⟨hb', hlo, hhi⟩).trans (only batch ⟨hb, hLo, hHi⟩).symm
  subst b
  obtain ⟨pos, hPos, ending, ⟨recv⟩⟩ :=
    warmRoundKeyObservedLane hp hX hFrame hg hw hSrc hCTA hb hLo hHi pair hEvent
      hOrdered.1 hRound hSecond (.inl (by change shflPc < pc; omega)) hSafe
  let lane := warmKShuffleSender src pair
  let thread := warpLane l g
  let rank := primingSearchShuffleCount batch + 64 + 64 * iteration + 2 * pair.val
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hl : lane < 32 := by unfold lane warmKShuffleSender pointerBroadcastLane; omega
  have hWarp := Step.sameWarp_trans
    (sameWarp_symm (Step.sameWarp_lane hBlock hg hSrc).1) (Step.sameWarp_lane hBlock hg hl).1
  have hPeer : ∃ k peer, X.get (thread lane, k) = some peer ∧ 1003 < peer.pc ∧
      WarmRoundDemand p l X g lane batch iteration k peer ∧ (8 ≤ pair.val → 1072 < peer.pc) ∧
      (shflPc < peer.pc ∨ (Execution.isShfl peer = true ∧
        ((X.tr (thread lane)).take k).countP Execution.isShfl = rank + 1)) ∧
      ∀ f, peer.kind ≠ .ub f := by
    rcases Step.shfl_lane_of_ready hX recv.second recv.secondOrdinal hWarp with
      ⟨k, ⟨⟨s, mode, input, select, clamp, result, good, hGet⟩, hCount⟩⟩ |
      ⟨k, s, hExit, _⟩
    · let peer : Event := ⟨s, .shfl mode input select clamp result good⟩
      have hk : ((X.tr (thread lane)).take k).countP Execution.isShfl = rank + 1 := hCount
      have hBefore : cur.pos lane ≤ k := by
        by_contra! h
        have hLe := Flow.countP_take_mono Execution.isShfl (X.tr (thread lane)) h.le
        rw [hk, cur.ordinals.shfl lane hl] at hLe
        dsimp only [rank] at hLe
        omega
      have hLate := firstKPeerAfterMetadata hp hw hl cur hGet hBefore (.inl rfl)
      have hFloor : 805 ≤ peer.pc :=
        primingVPeerFirstBroadcastFloor hp hX hg hw hl writes hb hLo hHi hCTA hGet hLate rfl
          (by rw [hk]; dsimp only [rank]; omega)
      have hWarmFloor : 1004 ≤ peer.pc :=
        warmShuffleFloor hp hX hg hw hl writes hb hLo hHi hCTA hGet hFloor rfl
          (by rw [hk]; dsimp only [rank]; omega)
      have hPeerRound : WarmRoundDemand p l X g lane batch iteration k peer :=
        ⟨.inl hCan, .inr (by rw [hk]; dsimp only [rank]; omega)⟩
      refine ⟨k, peer, hGet, hWarmFloor, hPeerRound, ?_, .inr ⟨rfl, hk⟩, by intro f h; cases h⟩
      intro hUpper
      exact warmRoundHighShuffleFloor hp hX hFrame hg hw hl hCTA hb hLo hHi hGet hWarmFloor
        hPeerRound rfl (by rw [hk]; dsimp only [rank]; omega)
          (by rw [hk]; dsimp only [rank]; have := pair.isLt; omega)
    · obtain rfl := actualExitPc hX hExit
      exact ⟨k, ⟨9205, .exit⟩, hExit, by decide, ⟨.inl hCan, .inl (by decide)⟩,
        fun _ => by decide, .inl hExitPc,
        by intro f h; cases h⟩
  obtain ⟨k, peer, hPeer, hLate, hPeerRound, hPeerSecond, hDemand, hPeerSafe⟩ := hPeer
  obtain ⟨partner, _, _, ⟨sent⟩⟩ :=
    warmRoundKeyObservedLane hp hX hFrame hg hw hl hCTA hb hLo hHi pair hPeer hLate
      hPeerRound hPeerSecond hDemand hPeerSafe
  have hSource : (shflSource .idx src (pair.val % 8) 6175).1 = lane := by
    let s : Fin 8 := ⟨pair.val % 8, Nat.mod_lt _ (by decide)⟩
    exact congrArg Prod.fst (kv_shuffle_source ⟨src, hSrc⟩ s)
  have hLane : laneOf l (thread src) = src := (Step.sameWarp_lane hBlock hg hSrc).2
  have hFrom : thread src - laneOf l (thread src) +
      (shflSource .idx (laneOf l (thread src)) (pair.val % 8) 6175).1 = thread lane := by
    rw [hLane, hSource]
    unfold thread warpLane
    omega
  have hThread : thread lane < l.threads := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
  have hLoWord := (Flow.shfl_source_value hX recv.first recv.firstOrdinal
    (by rw [hFrom]; exact sent.first) (by rw [hFrom]; exact sent.firstOrdinal)
    (by rw [hFrom]; exact ShflK.not_exited hX hThread sent.firstOrdinal)).1
  have hHiWord := (Flow.shfl_source_value hX recv.second recv.secondOrdinal
    (by rw [hFrom]; exact sent.second) (by rw [hFrom]; exact sent.secondOrdinal)
    (by rw [hFrom]; exact ShflK.not_exited hX hThread sent.secondOrdinal)).1
  have hAt := recv.checkpoint
  rw [hLoWord, hHiWord] at hAt
  refine ⟨pos, ending, recv.state, ?_, hAt.mono ?_, recv.continuation, ?_⟩
  · by_contra! hClose
    have impossible {ev : Event} (h : X.get (thread src, j) = some ev) (hb : ev.pc < pc) :
        False := by
      obtain rfl := Option.some.inj (hEvent.symm.trans h)
      exact Nat.lt_irrefl _ hb
    rcases (show pos = j ∨ pos + 1 = j by omega) with hA | hB
    · have hGet := congrArg (fun n => X.get (thread src, n)) hA
      exact impossible (hGet.symm.trans recv.first) (show shflPc < pc by omega)
    · have hGet := congrArg (fun n => X.get (thread src, n)) hB
      exact impossible (hGet.symm.trans recv.second) hOrdered.2.1
  · unfold warmKPairInputs
    split
    · exact ⟨hAt.2.2.2.2.1, hAt.2.2.2.2.2.1, by
        simpa [warmKSlotWords, warmKInputColumn, *] using hAt.2.2.2.2.2.2.2.2⟩
    · exact ⟨hAt.2.2.2.2.1, hAt.2.2.2.2.2.1, by
        simpa [warmKSlotWords, warmKInputColumn, *] using hAt.2.2.2.2.2.2.2.2⟩
  · have hCount := countP_take_succ (p := Execution.isShfl) recv.second rfl
    rw [show pos + 2 = pos + 1 + 1 by omega, hCount, recv.secondOrdinal.2]

end
end PTX.Kernels.TmlFa4Fwd.Loader
