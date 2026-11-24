-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundValueReload
import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundValueShuffleFloor
import Kernels.TmlFa4Fwd.Proof.LoaderWarmFirstCopyBacking
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmShuffleFloor
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKFirstPrefix
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Flow.Code.Part019

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

private theorem warmRoundValueObservedLane {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g lane batch iteration j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e) (hPc : 1238 < e.pc)
    (hRound : WarmRoundDemand p l X g lane batch iteration j e)
    (hLater : 1239 < e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
        primingSearchShuffleCount batch + 64 + 64 * iteration + 32 + 1))
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let ptr := primingVRowPointer p batch (co.2 / 6) (primingLaneRow (trips - 2 - iteration) tid)
    let F := [(2077, b32 (ptr % 2 ^ 32)), (2078, b32 (ptr / 2 ^ 32))] ++
      [(2066, b32 (16 * tid))] ++ warmCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid
    ∃ pos ≤ j, ∃ ending, Nonempty (PointerBroadcastInPrefix l X thread pos
      (primingSearchShuffleCount batch + 64 + 64 * iteration + 32) 1239 ptr 2079 0 F ending) := by
  obtain ⟨start, hStart, t, ending, ht, hr, hRank⟩ :=
    warmRoundFirstValueReloadOfEvent hp hX hFrame hg hw hl hCTA hb hLo hHi he hPc hSafe hRound
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let ptr := primingVRowPointer p batch (co.2 / 6) (primingLaneRow (trips - 2 - iteration) tid)
  let F := [(2077, b32 (ptr % 2 ^ 32)), (2078, b32 (ptr / 2 ^ 32))] ++
    [(2066, b32 (16 * tid))] ++ warmCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hFresh : ∀ r ∈ F, r.1 ≠ 2079 ∧ r.1 ≠ 2079 + 1 := by
    intro r hIn
    have hAudit : (F.map Prod.fst).all (fun k => decide (k ≠ 2079 ∧ k ≠ 2079 + 1)) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    exact of_decide_eq_true (List.all_eq_true.mp hAudit _ (List.mem_map_of_mem hIn))
  refine ⟨start + 2, hStart, ending, ?_⟩
  refine pointerBroadcastObserved (F := F) (base := ptr) (src := 2077)
    hBlock (by decide) (by decide) Flow.code_1239 Flow.code_1240 hFresh ht
    (by simp [F]) (by simp [F]) hr hRank (traceAfterObservedEvent he hStart) ?_
  intro low hGet hLow _
  apply traceAfterObservedEvent he
  by_contra! hNo
  have here : start + 2 = j := by omega
  rw [here] at hGet
  have same := Option.some.inj (hGet.symm.trans he)
  rcases hLater with hp | ⟨_, hCount⟩
  · rw [← same, hLow] at hp
    exact (Nat.lt_irrefl _) hp
  · rw [← here, hRank] at hCount
    omega

/-- A real first-pair issue identifies the subgroup pointer of its warm visit. -/
theorem warmRoundValueBroadcastOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g src j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (upper : Bool) {sp : AsyncCopy.Spec}
    (he : X.get (warpLane l g src, j) = some
      ⟨packetPlanePc (recurringPacketSite 1) 0 upper, .copy sp⟩)
    (hRank : ((X.tr (warpLane l g src)).take j).countP Execution.isShfl =
      primingSearchShuffleCount batch + 64 + 64 * iteration + 32 + 2) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g src
    let tid := thread % l.block
    let sender := warpLane l g (pointerBroadcastLane src)
    let trips := Mma.trips p batch co.1
    let row := primingLaneRow (trips - 2 - iteration) (sender % l.block)
    let ptr := primingVRowPointer p batch (co.2 / 6) row
    ∃ pos ending s, pos + 2 ≤ j ∧
      At s 1241 ([(2079, b32 (ptr % 2 ^ 32)), (2080, b32 (ptr / 2 ^ 32))] ++
        [(2066, b32 (16 * tid))] ++ warmCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid) ∧
      Run kernel Assumptions.all l thread s ((X.tr thread).drop (pos + 2)) ending ∧
      ((X.tr thread).take (pos + 2)).countP Execution.isShfl =
        primingSearchShuffleCount batch + 64 + 64 * iteration + 32 + 2 := by
  let pc := packetPlanePc (recurringPacketSite 1) 0 upper
  let e : Event := ⟨pc, .copy sp⟩
  have hEvent : X.get (warpLane l g src, j) = some e := he
  have hSite : 1240 < pc ∧ pc < 1353 := by cases upper <;> decide
  have hSafe : ∀ f, e.kind ≠ .ub f := by intro f h; cases h
  have writes (w a data loc) (hw : X.MemWrites w a data) (hc : a.Covers loc)
      (hg : loc.space = .global) : p.oRegion.Contains loc ∨ p.lseRegion.Contains loc := by
    rcases hFrame w a data loc hw hc hg with ho | ⟨q, hq, head, hh, k, hk, rfl⟩
    · exact .inl ho
    · exact .inr (lseByte_in hq hh hk)
  have hRound : WarmRoundDemand p l X g src batch iteration j e :=
    ⟨.inr hSite.2, .inr (by rw [hRank]; omega)⟩
  have hCan := (warmRoundEntryOfEvent hp hX hg hw hSrc writes hCTA hb hLo hHi hEvent
    (show 917 ≤ pc by omega) hSafe hRound).1
  obtain ⟨b, hb', hlo, hhi, _, cur, _⟩ :=
    loaderPrimingEntryOfActiveEvent hp hX hg hw hSrc (hp.cuQ_protected writes) hCTA hEvent
      (show 308 < pc by omega)
  obtain ⟨_, _, only⟩ := tileBatch_existsUnique p hCTA
  have same : b = batch := (only b ⟨hb', hlo, hhi⟩).trans (only batch ⟨hb, hLo, hHi⟩).symm
  subst b
  obtain ⟨pos, hPos, ending, ⟨recv⟩⟩ :=
    warmRoundValueObservedLane hp hX hFrame hg hw hSrc hCTA hb hLo hHi hEvent
      (show 1238 < pc by omega) hRound (.inl (show 1239 < pc by omega)) hSafe
  let lane := pointerBroadcastLane src
  let thread := warpLane l g
  let rank := primingSearchShuffleCount batch + 64 + 64 * iteration + 32
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hl : lane < 32 := by unfold lane pointerBroadcastLane; omega
  have hWarp := Step.sameWarp_trans
    (sameWarp_symm (Step.sameWarp_lane hBlock hg hSrc).1) (Step.sameWarp_lane hBlock hg hl).1
  have hPeer : ∃ k peer, X.get (thread lane, k) = some peer ∧
      1238 < peer.pc ∧ WarmRoundDemand p l X g lane batch iteration k peer ∧
      (1239 < peer.pc ∨ (Execution.isShfl peer = true ∧
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
      have hLower : 1004 ≤ peer.pc :=
        warmShuffleFloor hp hX hg hw hl writes hb hLo hHi hCTA hGet hFloor rfl
          (by rw [hk]; dsimp only [rank]; omega)
      have hPeerRound : WarmRoundDemand p l X g lane batch iteration k peer :=
        ⟨.inl hCan, .inr (by rw [hk]; dsimp only [rank]; omega)⟩
      have hValueFloor := warmRoundValueShuffleFloor hp hX hFrame hg hw hl hCTA
        hb hLo hHi hGet hLower hPeerRound rfl hk
      exact ⟨k, peer, hGet, hValueFloor, hPeerRound, .inr ⟨rfl, hk⟩, by intro f h; cases h⟩
    · obtain rfl := actualExitPc hX hExit
      exact ⟨k, ⟨9205, .exit⟩, hExit, by decide,
        ⟨.inl hCan, .inl (by decide)⟩, .inl (by decide), by intro f h; cases h⟩
  obtain ⟨k, peer, hPeer, hLate, hRoundPeer, hDemand, hPeerSafe⟩ := hPeer
  obtain ⟨partner, _, _, ⟨sent⟩⟩ :=
    warmRoundValueObservedLane hp hX hFrame hg hw hl hCTA hb hLo hHi hPeer
      hLate hRoundPeer hDemand hPeerSafe
  have hSource : (shflSource .idx src 0 6175).1 = lane := by
    simpa only [lane, pointerBroadcastLane, Fin.val_zero, Nat.add_zero] using
      congrArg Prod.fst (kv_shuffle_source ⟨src, hSrc⟩ (0 : Fin 8))
  have hLane : laneOf l (thread src) = src := (Step.sameWarp_lane hBlock hg hSrc).2
  have hFrom : thread src - laneOf l (thread src) +
      (shflSource .idx (laneOf l (thread src)) 0 6175).1 = thread lane := by
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
    have impossible {event : Event} (h : X.get (thread src, j) = some event)
        (hLt : event.pc < pc) : False := by
      obtain rfl := Option.some.inj (hEvent.symm.trans h)
      exact Nat.lt_irrefl _ hLt
    rcases (show pos = j ∨ pos + 1 = j by omega) with hHere | hNext
    · have hGet := congrArg (fun n => X.get (thread src, n)) hHere
      exact impossible (hGet.symm.trans recv.first) (show 1239 < pc by omega)
    · have hGet := congrArg (fun n => X.get (thread src, n)) hNext
      exact impossible (hGet.symm.trans recv.second) hSite.1
  · exact ⟨hAt.2.2.2.2.1, hAt.2.2.2.2.2.1, hAt.2.2.2.2.2.2.2.2⟩
  · have hCount := countP_take_succ (p := Execution.isShfl) recv.second rfl
    have hOrd := recv.secondOrdinal.2
    change ((X.tr (thread src)).take (pos + 1)).countP Execution.isShfl = rank + 1 at hOrd
    rw [show pos + 2 = pos + 1 + 1 by omega, hCount, hOrd]

end
end PTX.Kernels.TmlFa4Fwd.Loader
