-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixOperands
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixPeer
public import Kernels.TmlFa4Fwd.Proof.LoaderPointerBroadcastPrefix
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKFirstPrefix
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Flow.Code.Part012

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

private theorem vObservedLane {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane batch j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (pair : Fin 16) {e : Event} (he : X.get (warpLane l g lane, j) = some e) (hPc : 804 < e.pc)
    (hDemand : vPacketShufflePc pair < e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
        primingSearchShuffleCount batch + 32 + 2 * pair.val + 1))
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    let co := assignedCoordinates p batch (g / l.block)
    let tile := Mma.trips p batch co.1 - 1
    let warp := warpIndex l g
    let base := primingVPairBases p batch (co.2 / 6) tile warp pair lane
    let frame := if pair.val = 0 then
      vPacketFrame p l batch tile warp lane (fun _ => vPrimingResidual p batch co.1)
      else vPacketCarry p l batch tile warp lane (fun _ => vPrimingResidual p batch co.1)
    let F := primingVReloadWords (vPacketSlot pair) base ++ frame
    ∃ pos ≤ j, ∃ ending, Nonempty (PointerBroadcastInPrefix l X (warpLane l g lane) pos
      (primingSearchShuffleCount batch + 32 + 2 * pair.val)
      (vPacketShufflePc pair) base (vPacketShflLow pair) (vPacketSelect pair) F ending) := by
  obtain ⟨b, hb', hlo, hhi, start, hStart, t, ending, ht, hRun, hOrdinal,
    read, a, data, _, hRead, hSaved⟩ :=
    loaderPrimingVFirstPointerAndSavedOfActiveEvent hp hX hg hw hl writes hCTA he hPc hSafe
  obtain ⟨selected, _, only⟩ := tileBatch_existsUnique p hCTA
  have hEq : b = batch := (only b ⟨hb', hlo, hhi⟩).trans (only batch ⟨hb, hLo, hHi⟩).symm
  subst b
  let co := assignedCoordinates p batch (g / l.block)
  let tile := Mma.trips p batch co.1 - 1
  let warp := warpIndex l g
  let thread := warpLane l g lane
  let residual := fun _ : Nat => vPrimingResidual p batch co.1
  let base := primingVPairBases p batch (co.2 / 6) tile warp pair lane
  let frame := if pair.val = 0 then vPacketFrame p l batch tile warp lane residual
    else vPacketCarry p l batch tile warp lane residual
  let F := primingVReloadWords (vPacketSlot pair) base ++ frame
  have hh := (assignedCoordinates_valid hp hLo hHi).2
  have hHead : co.2 / 6 < p.kvHeads := by unfold co; unfold Params.heads at hh; omega
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSame : warpIndex l g = warpIndex l thread := (Step.sameWarp_lane hBlock hg hl).1.2
  have hWarp : 14 ≤ warpIndex l thread := hSame ▸ hw
  have htAt : At t 805 (primingVReloadWords 0 (primingVPairBases p batch (co.2 / 6) tile warp
      0 lane) ++ vPacketFrame p l batch tile warp lane residual) := by
    obtain ⟨hPtr, hFrame⟩ := (holds_append ..).mp ht.2.2.2.2
    exact ht.mono ((holds_append ..).mpr ⟨hPtr, ((holds_append ..).mp hFrame).2⟩)
  obtain ⟨u, pos, endAt, hPos, hu, huRun, huRank⟩ :=
    primingVPairOperandsInPrefix hp hX hWarp hb hHead htAt hRun hOrdinal hRead hSaved
      pair he hStart (hDemand.imp_right (fun ⟨hMark, hCount⟩ =>
        ⟨hMark, (Nat.le_succ _).trans hCount.ge⟩)) hSafe
  have hCode0 : kernel.code[vPacketShufflePc pair]? =
      some (pointerBroadcastInstr (vPacketShflSrc pair 0) (vPacketShflLow pair)
        (vPacketSelect pair)) := vPacketShuffleCode pair 0
  have hCode1 : kernel.code[vPacketShufflePc pair + 1]? =
      some (pointerBroadcastInstr (vPacketShflSrc pair 0 + 1) (vPacketShflLow pair + 1)
        (vPacketSelect pair)) := vPacketShuffleCode pair 1
  have hFresh : ∀ r ∈ F, r.1 ≠ vPacketShflLow pair ∧ r.1 ≠ vPacketShflLow pair + 1 := by
    intro r hIn
    have hAudit : (F.map Prod.fst).all (fun k =>
        decide (k ≠ vPacketShflLow pair ∧ k ≠ vPacketShflLow pair + 1)) = true := by
      fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)
    exact of_decide_eq_true (List.all_eq_true.mp hAudit _ (List.mem_map_of_mem hIn))
  have hLow : (vPacketShflSrc pair 0, b32 (base % 2 ^ 32)) ∈ F := by
    fin_cases pair <;> simp [F, primingVReloadWords, vPacketShflSrc]
  have hHigh : (vPacketShflSrc pair 0 + 1, b32 (base / 2 ^ 32)) ∈ F := by
    fin_cases pair <;>
      simp [F, primingVReloadWords, vPacketShflSrc, vPacketSlot, primingVPointerReload]
  refine ⟨pos, hPos, endAt, pointerBroadcastObserved hBlock (by fin_cases pair <;> decide)
    (Nat.mod_lt _ (by decide)) hCode0 hCode1 hFresh hu hLow hHigh huRun huRank
    (traceAfterObservedEvent he hPos) ?_⟩
  intro low hGet hLow _
  apply traceAfterObservedEvent he
  by_contra! hNo
  have hSame : pos = j := by omega
  rw [hSame] at hGet
  have hEq : low = e := Option.some.inj (hGet.symm.trans he)
  rcases hDemand with hLate | ⟨_, hCount⟩
  · rw [← hEq, hLow] at hLate
    exact Nat.lt_irrefl _ hLate
  · rw [← hSame, huRank] at hCount
    omega

/-- The two observed shuffles supply the issuing lane's actual V subgroup pointer. -/
theorem primingVPrefixShuffleSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (pair : Fin 16) (upper : Bool) {spec : AsyncCopy.Spec}
    (he : X.get (warpLane l g src, j) =
      some ⟨vCopyPc pair + if upper then 1 else 0, .copy spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let tile := Mma.trips p batch co.1 - 1
      let warp := warpIndex l g
      let thread := warpLane l g src
      let base := primingVPairBases p batch (co.2 / 6) tile warp pair (vPacketSender pair src)
      let residual := fun _ : Nat => vPrimingResidual p batch co.1
      let frame := if pair.val = 0 then vPacketFrame p l batch tile warp src residual
        else vPacketCarry p l batch tile warp src residual
      ∃ index ending s, index + 2 ≤ j ∧
        At s (vPacketShufflePc pair + 2) ([(vPacketShflLow pair, b32 (base % 2 ^ 32)),
          (vPacketShflLow pair + 1, b32 (base / 2 ^ 32))] ++ frame) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop (index + 2)) ending := by
  let e : Event := ⟨vCopyPc pair + if upper then 1 else 0, .copy spec⟩
  let pc := vCopyPc pair
  let shflPc := vPacketShufflePc pair
  have hPcs : 810 ≤ pc ∧ 804 < shflPc ∧ shflPc + 1 < pc ∧ shflPc < 9205 := by
    fin_cases pair <;> decide
  have hEvent : X.get (warpLane l g src, j) = some e := he
  obtain ⟨batch, hb, hLo, hHi, _, cur, hFollows⟩ :=
    loaderPrimingEntryOfActiveEvent hp hX hg hw hSrc (hp.cuQ_protected writes)
      hCTA hEvent (by change 308 < pc + _; omega)
  obtain ⟨pos, hPos, ending, ⟨recv⟩⟩ :=
    vObservedLane hp hX hg hw hSrc writes hb hLo hHi hCTA pair hEvent
      (by change 804 < pc + _; omega) (.inl (by change shflPc < pc + _; omega))
      (by intro f h; cases h)
  let lane := vPacketSender pair src
  let thread := warpLane l g
  let rank := primingSearchShuffleCount batch + 32 + 2 * pair.val
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hl : lane < 32 := vPacketSender_lt pair hSrc
  have hWarp := Step.sameWarp_trans
    (sameWarp_symm (Step.sameWarp_lane hBlock hg hSrc).1) (Step.sameWarp_lane hBlock hg hl).1
  have hPeer : ∃ k peer, X.get (thread lane, k) = some peer ∧ 804 < peer.pc ∧
      (shflPc < peer.pc ∨ (Execution.isShfl peer = true ∧
        ((X.tr (thread lane)).take k).countP Execution.isShfl = rank + 1)) ∧
      ∀ f, peer.kind ≠ .ub f := by
    rcases Step.shfl_lane_of_ready hX recv.second recv.secondOrdinal hWarp with
      ⟨k, ⟨⟨pc, mode, input, select, clamp, result, good, hGet⟩, hCount⟩⟩ |
      ⟨k, pc, hExit, _⟩
    · let peer : Event := ⟨pc, .shfl mode input select clamp result good⟩
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
      exact ⟨k, peer, hGet, hFloor, .inr ⟨rfl, hk⟩, by intro f h; cases h⟩
    · obtain rfl := actualExitPc hX hExit
      exact ⟨k, ⟨9205, .exit⟩, hExit, by decide, .inl hPcs.2.2.2, by intro f h; cases h⟩
  obtain ⟨k, peer, hPeer, hLate, hDemand, hSafe⟩ := hPeer
  obtain ⟨partner, _, _, ⟨sent⟩⟩ :=
    vObservedLane hp hX hg hw hl writes hb hLo hHi hCTA pair hPeer hLate hDemand hSafe
  have hSource : (shflSource .idx src (vPacketSelect pair) 6175).1 = lane := by
    let select : Fin 8 := ⟨vPacketSelect pair, Nat.mod_lt _ (by decide)⟩
    simpa only [lane, vPacketSender, pointerBroadcastLane, select] using
      congrArg Prod.fst (kv_shuffle_source ⟨src, hSrc⟩ select)
  have hLane : laneOf l (thread src) = src := (Step.sameWarp_lane hBlock hg hSrc).2
  have hFrom : thread src - laneOf l (thread src) +
      (shflSource .idx (laneOf l (thread src)) (vPacketSelect pair) 6175).1 = thread lane := by
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
  refine ⟨batch, hb, hLo, hHi, pos, ending, recv.state, ?_, hAt.mono ?_, recv.continuation⟩
  swap
  · exact ⟨hAt.2.2.2.2.1, hAt.2.2.2.2.2.1, hAt.2.2.2.2.2.2.2.2⟩
  by_contra! hClose
  have hBad {ev : Event} (hGet : X.get (thread src, j) = some ev) (hEarly : ev.pc < pc) :
      False := by
    obtain rfl := Option.some.inj (hEvent.symm.trans hGet)
    change pc + (if upper then 1 else 0) < pc at hEarly
    omega
  rcases (show pos = j ∨ pos + 1 = j by omega) with hHere | hNext
  · have hGet := congrArg (fun n => X.get (thread src, n)) hHere
    exact hBad (hGet.symm.trans recv.first) (by change shflPc < pc; omega)
  · have hGet := congrArg (fun n => X.get (thread src, n)) hNext
    exact hBad (hGet.symm.trans recv.second) hPcs.2.2.1

end
end PTX.Kernels.TmlFa4Fwd.Loader
