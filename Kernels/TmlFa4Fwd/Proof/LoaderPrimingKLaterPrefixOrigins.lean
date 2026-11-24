-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKPrefixOperands
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKFirstPrefix
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Lemmas.Flow.NotShfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue

noncomputable section

private theorem traceAfter {X : Execution} {g i j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hle : i ≤ j) : (X.tr g).drop i ≠ [] := by
  intro h
  exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp he).1
    ((List.drop_eq_nil_iff.mp h).trans hle)

set_option maxRecDepth 100000 in
private theorem primingKExitLater {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hExit : e.kind = .exit) (hStart : 543 < e.pc) :
    674 ≤ e.pc := by
  by_contra! hEarlier
  obtain ⟨_, hRun⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t, _, hStep⟩ := hRun.estep (List.mem_of_getElem? he)
  have hPc := estep_source_pc hStep
  obtain ⟨_, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨i, hCode, rfl⟩
  · obtain ⟨rfl, _⟩ := hFire
    cases hExit
  have hGet : ((kernel.code.drop 544).take (674 - 544))[e.pc - 544]? = some i := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le (by omega), hPc]
    exact hCode
  have hAudit : ((kernel.code.drop 544).take (674 - 544)).all
      (fun i => match i.op with | .ret | .exit => false | _ => true) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hi := List.all_eq_true.mp hAudit i (List.mem_of_getElem? hGet)
  obtain h | h := fires_exit_op hFire hExit <;> rw [h] at hi <;> contradiction

private theorem localPointerBeforeLater {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j index batch tile warp lane : Nat} (hWarp : 14 ≤ warpIndex l g)
    {e : Event} (he : X.get (g, j) = some e) (hPc : 545 ≤ e.pc)
    {bases : Nat → Nat} {s : TState} {ending : Option TState}
    (hs : At s 544 (primingKSourceInputs p l batch tile warp bases lane))
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hDemand : PrefixDemand X g index 543 ending)
    (hRank : ((X.tr g).take index).countP Execution.isShfl = primingSearchShuffleCount batch) :
    index ≤ j := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  let step := fun v (_ : Bool) => next (setReg s 1855 v)
  have hn : Next kernel Assumptions.all l g s s
      (.shfl .idx (b32 (bases lane % 2 ^ 32)) 0 6175 step) :=
    ⟨.refl, primingKShuffleTemplate hBlock 0 hs hs.2.2.2.2.1⟩
  obtain ⟨v, ok, hGet, _, _⟩ := hn.shuffle_at_nonempty hRun (hDemand.nonempty hRun) hRank
  rw [hs.1] at hGet
  by_contra! hLate
  have hAudit : ∀ branch, ((kernel.code.drop 545).take (1901 - 545)).all
      (fun i => loaderPipelineCutOp 545 1901 branch [2535, 1062] i.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  have hEarly := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 545) (by decide)
    hAudit he hGet (by omega) (show 173 < 544 by decide) (show 544 < 545 by decide)
  omega

private theorem primingKObservedLane {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane batch j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (pair : Fin 15) {e : Event} (he : X.get (warpLane l g lane, j) = some e) (hPc : 543 < e.pc)
    (hDemand : kCopyPc (primingKLaterPair pair) - 5 < e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
        primingSearchShuffleCount batch + 2 * (pair.val + 1) + 1))
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    let co := assignedCoordinates p batch (g / l.block)
    let tile := Mma.trips p batch co.1 - 1
    let warp := warpIndex l g
    let thread := warpLane l g lane
    let base := primingKPairBases p batch (co.2 / 6) tile warp (primingKLaterPair pair)
    ∃ pos ending, pos ≤ j ∧
      Nonempty (PrimingKLaterLaneShuffle p l X thread batch tile warp lane pos
        (primingSearchShuffleCount batch + 2 * (pair.val + 1)) base pair ending) := by
  obtain ⟨b, hb', hlo, hhi, hTile, index, t, ending, hAt, hRun, hStill, hRank,
    read, a, bytes, _, hRead, hSaved⟩ :=
    loaderPrimingKPointerAndSavedOfActiveEvent hp hX hg hw hl writes hCTA he
      (by decide : 543 ≤ 543) hPc
  obtain ⟨actual, _, hUnique⟩ := tileBatch_existsUnique p hCTA
  have hEq : b = batch := (hUnique b ⟨hb', hlo, hhi⟩).trans (hUnique batch ⟨hb, hLo, hHi⟩).symm
  subst b
  let thread := warpLane l g lane
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSameWarp : warpIndex l g = warpIndex l thread := (Step.sameWarp_lane hBlock hg hl).1.2
  have hWarp : 14 ≤ warpIndex l thread := hSameWarp ▸ hw
  have hSite : 545 ≤ kCopyPc (primingKLaterPair pair) - 5 ∧
      primingKPredicatePc (primingKLaterPair pair) ≤ kCopyPc (primingKLaterPair pair) - 5 :=
    by fin_cases pair <;> decide
  have hOrder : index ≤ j := by
    rcases hDemand with hLate | ⟨hMark, hCount⟩
    · exact localPointerBeforeLater hp hX hWarp he (by omega) hAt hRun hStill hRank
    · by_contra! hEarly
      have hLe := Flow.countP_take_mono Execution.isShfl (X.tr thread) hEarly.le
      rw [hCount, hRank] at hLe
      omega
  have hh := (assignedCoordinates_valid hp hLo hHi).2
  have hHead : (assignedCoordinates p batch (g / l.block)).2 / 6 < p.kvHeads := by
    unfold Params.heads at hh
    omega
  obtain ⟨u, pos, stop, hPos, hU, hTail, hOrdinal⟩ :=
    primingKPairOperandsInPrefix hp hX (rank := primingSearchShuffleCount batch)
      hWarp hb hHead hTile hAt hRun hRank hRead hSaved
      pair he hOrder (hDemand.imp_right (fun ⟨hMark, hCount⟩ =>
        ⟨hMark, (Nat.le_succ _).trans hCount.ge⟩)) hSafe
  refine ⟨pos, stop, hPos, primingKLaterLaneShuffles hp pair hU hTail hOrdinal
    (traceAfter he hPos) ?_⟩
  intro low hGet hLow _
  apply traceAfter he
  by_contra! hNo
  have hSame : pos = j := by omega
  rw [hSame] at hGet
  have hEq : low = e := Option.some.inj (hGet.symm.trans he)
  rcases hDemand with hLate | ⟨_, hCount⟩
  · rw [← hEq, hLow] at hLate
    omega
  · rw [← hSame, hOrdinal] at hCount
    omega

/-- An issued K vector receives both actual words from its selected peer. -/
theorem primingLaterShuffleSource {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (i : Fin 15) (upper : Bool) {spec : AsyncCopy.Spec}
    (he : X.get (warpLane l g src, j) =
      some ⟨kCopyPc (primingKLaterPair i) + if upper then 1 else 0, .copy spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let tile := Mma.trips p batch co.1 - 1
      let warp := warpIndex l g
      let pair := primingKLaterPair i
      let thread := warpLane l g src
      let bases := primingKPairBases p batch (co.2 / 6) tile warp pair
      let base := bases (pointerBroadcastLane src + primingKBroadcastSlot i)
      ∃ index ending s, index + 2 ≤ j ∧
        At s (kCopyPc pair - 3)
          ((primingKBroadcastReg i, b32 (base % 2 ^ 32)) ::
            (primingKBroadcastReg i + 1, b32 (base / 2 ^ 32)) ::
            primingKPairPredicate p batch tile warp i src ::
              primingKLaterFrame p l batch tile warp bases i src) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop (index + 2)) ending := by
  let pair := primingKLaterPair i
  let kpc := kCopyPc pair
  let e : Event := ⟨kpc + if upper then 1 else 0, .copy spec⟩
  have hSite : 550 ≤ kpc ∧ kpc < 674 := by fin_cases i <;> decide
  have hEvent : X.get (warpLane l g src, j) = some e := he
  obtain ⟨batch, hb, hLo, hHi, _, cur, hFollows⟩ :=
    loaderPrimingEntryOfActiveEvent hp hX hg hw hSrc (hp.cuQ_protected writes)
      hCTA hEvent (by change 308 < kpc + _; omega)
  obtain ⟨pos, ending, hPos, ⟨recv⟩⟩ :=
    primingKObservedLane hp hX hg hw hSrc writes hb hLo hHi hCTA i hEvent
      (by change 543 < kpc + _; omega)
      (.inl (by change kpc - 5 < kpc + _; omega)) (by intro f h; cases h)
  let lane := pointerBroadcastLane src + primingKBroadcastSlot i
  let thread := warpLane l g
  let rank := primingSearchShuffleCount batch + 2 * (i.val + 1)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSlot : primingKBroadcastSlot i < 8 := Nat.mod_lt _ (by decide)
  have hl : lane < 32 := by unfold lane pointerBroadcastLane; omega
  have hWarp := Step.sameWarp_trans
    (sameWarp_symm (Step.sameWarp_lane hBlock hg hSrc).1) (Step.sameWarp_lane hBlock hg hl).1
  have hPeer : ∃ k peer, X.get (thread lane, k) = some peer ∧ 543 < peer.pc ∧
      (X.ShflK (thread lane, k) (rank + 1) ∨ peer.kind = .exit) := by
    rcases Step.shfl_lane_of_ready hX recv.second recv.secondOrdinal hWarp with
      ⟨k, ⟨⟨pc, mode, input, select, clamp, result, good, hGet⟩, hCount⟩⟩ |
      ⟨k, pc, hExit, _⟩
    · let ev : Event := ⟨pc, .shfl mode input select clamp result good⟩
      have hOrd : X.ShflK (thread lane, k) (rank + 1) :=
        ⟨⟨pc, mode, input, select, clamp, result, good, hGet⟩, hCount⟩
      have hBefore : cur.pos lane ≤ k := by
        by_contra! h
        have hLe := Flow.countP_take_mono Execution.isShfl (X.tr (thread lane)) h.le
        have hk : ((X.tr (thread lane)).take k).countP Execution.isShfl = rank + 1 := hCount
        rw [hk, cur.ordinals.shfl lane hl] at hLe
        dsimp only [rank] at hLe
        omega
      exact ⟨k, ev, hGet, firstKPeerAfterMetadata hp hw hl cur hGet hBefore (.inl rfl), .inl hOrd⟩
    · have hBefore : cur.pos lane ≤ k := by
        by_contra! hLt
        exact hFollows.noExit lane hl k hLt pc hExit
      exact ⟨k, ⟨pc, .exit⟩, hExit,
        firstKPeerAfterMetadata hp hw hl cur hExit hBefore (.inr rfl), .inr rfl⟩
  obtain ⟨k, peer, hPeer, hLate, hKind⟩ := hPeer
  have hPeerDemand : kpc - 5 < peer.pc ∨ (Execution.isShfl peer = true ∧
      ((X.tr (thread lane)).take k).countP Execution.isShfl = rank + 1) := by
    rcases hKind with hOrd | hExit
    · obtain ⟨⟨_, _, _, _, _, _, _, hGet⟩, hCount⟩ := hOrd
      obtain rfl := Option.some.inj (hPeer.symm.trans hGet)
      exact .inr ⟨rfl, hCount⟩
    · have hBound := primingKExitLater hX hPeer hExit hLate
      exact .inl (by omega)
  have hPeerSafe : ∀ f, peer.kind ≠ .ub f := by
    intro f hFault
    rcases hKind with ⟨⟨_, _, _, _, _, _, _, hGet⟩, _⟩ | hExit
    · obtain rfl := Option.some.inj (hPeer.symm.trans hGet)
      cases hFault
    · rw [hExit] at hFault
      cases hFault
  obtain ⟨partner, _, _, ⟨sent⟩⟩ :=
    primingKObservedLane hp hX hg hw hl writes hb hLo hHi hCTA i hPeer hLate
      hPeerDemand hPeerSafe
  have hSource : (shflSource .idx src (primingKBroadcastSlot i) 6175).1 = lane := by
    let select : Fin 8 := ⟨primingKBroadcastSlot i, hSlot⟩
    simpa only [lane, pointerBroadcastLane, select] using
      congrArg Prod.fst (kv_shuffle_source ⟨src, hSrc⟩ select)
  have hLaneNumber : laneOf l (thread src) = src := (Step.sameWarp_lane hBlock hg hSrc).2
  have hFrom : thread src - laneOf l (thread src) +
      (shflSource .idx (laneOf l (thread src)) (primingKBroadcastSlot i) 6175).1 = thread lane := by
    rw [hLaneNumber, hSource]
    unfold thread warpLane
    omega
  have hThread : thread lane < l.threads := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
  have hLoWord := (Flow.shfl_source_value hX recv.first recv.firstOrdinal
    (by rw [hFrom]; exact sent.first) (by rw [hFrom]; exact sent.firstOrdinal)
    (by rw [hFrom]; exact ShflK.not_exited hX hThread sent.firstOrdinal)).1
  have hHiWord := (Flow.shfl_source_value hX recv.second recv.secondOrdinal
    (by rw [hFrom]; exact sent.second) (by rw [hFrom]; exact sent.secondOrdinal)
    (by rw [hFrom]; exact ShflK.not_exited hX hThread sent.secondOrdinal)).1
  have hReady := recv.checkpoint
  rw [hLoWord, hHiWord] at hReady
  refine ⟨batch, hb, hLo, hHi, pos, ending, recv.state, ?_, hReady, recv.continuation⟩
  by_contra! hClose
  have hBad {e' : Event} (hGet : X.get (thread src, j) = some e') (hEarly : e'.pc < kpc) :
      False := by
    obtain rfl := Option.some.inj (hEvent.symm.trans hGet)
    change kpc + (if upper then 1 else 0) < kpc at hEarly
    omega
  rcases (show pos = j ∨ pos + 1 = j by omega) with hHere | hNext
  · have hGet := congrArg (fun n => X.get (thread src, n)) hHere
    exact hBad (hGet.symm.trans recv.first) (by change kpc - 5 < kpc; omega)
  · have hGet := congrArg (fun n => X.get (thread src, n)) hNext
    exact hBad (hGet.symm.trans recv.second) (by change kpc - 5 + 1 < kpc; omega)

end
end PTX.Kernels.TmlFa4Fwd.Loader
