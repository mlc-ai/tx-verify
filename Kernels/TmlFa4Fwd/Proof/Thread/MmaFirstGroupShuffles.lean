-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstGroupVote
import Kernels.TmlFa4Fwd.Proof.MmaSelectionPath
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Lemmas.Step.WarpShuffleProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (selectedPreviousLane selectedPreviousPrefixShuffle
  selectedPreviousPrefixStep selectedPreviousWork selectedPrefixBranch selectedTileParameters
  selectedRequestTilesShuffle selectedRequestTilesStep selectedMmaTileEntry)

private def selectionLanePrefix (p : Params) (first lane : Nat) : Nat :=
  ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i

private def mmaSelectionFrame (p : Params) (l : Launch)
    (g first batch : Nat) : List (Nat × Value) :=
  [(1187, b32 (batch - first)), (7196, b32 (groupLaneTiles p first (laneOf l g))),
    (7197, b32 (selectionLanePrefix p first (laneOf l g))),
    (1186, b32 (tilePrefix p first * p.heads)), (1072, b32 (g / l.block)),
    (7139, b32 p.heads), (7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
    (2535, b32 l.sharedBase)]

private structure MmaGroupIndexCursor (l : Launch) (X : Execution) (g site index count dst : Nat)
    (src : Value) (facts : List (Nat × Value)) where
  pos : Nat
  before : TState
  ready : TState
  lastState : Option TState
  pos_le : pos ≤ (X.tr g).length
  shuffleCount : ((X.tr g).take pos).countP Execution.isShfl = count
  voteCount : ((X.tr g).take pos).countP isFullWarpVote = 1
  released : pos = (X.tr g).length → Step.Released l X g
  checkpoint : At ready site facts
  runPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before)
  continuation : Run kernel Assumptions.all l g before ((X.tr g).drop pos) lastState
  shuffle : Next kernel Assumptions.all l g before ready
    (.shfl .idx src index 31 (fun word _ => next (setReg ready dst word)))

private theorem mmaGroupIndexEvents {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g site index count dst : Nat} (hCount : 0 < count)
    (src : Nat → Value) (facts : Nat → List (Nat × Value))
    (cur : ∀ h, SameWarp l g h → MmaGroupIndexCursor l X h site index count dst
      (src h) (facts h)) :
    ∀ h (hh : SameWarp l g h), ∃ recv ok,
      X.get (h, (cur h hh).pos) =
        some ⟨site, .shfl .idx (src h) index 31 recv ok⟩ ∧
      X.ShflK (h, (cur h hh).pos) count := by
  classical
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  let pos (h : Nat) := if hh : SameWarp l g h then (cur h hh).pos else 0
  intro h hh
  have hActual := Step.shfl_occurs_of_maximal hMax hBlock hh.1.2.1
    pos src (fun _ => index) (fun _ => 31)
    (by
      intro peer hs
      let c := cur peer (Step.sameWarp_trans hh hs)
      refine .inl (fun hNil => ?_)
      have hOrd := c.shuffleCount
      rw [hNil, List.take_nil, List.countP_nil] at hOrd
      omega)
    (by
      intro peer hs
      have hPeer := Step.sameWarp_trans hh hs
      simp only [pos, dite_eq_left hPeer]
      let c := cur peer hPeer
      exact ⟨c.before, c.ready, c.lastState, _, c.pos_le, c.shuffleCount, c.released,
        c.checkpoint.1, c.runPrefix, c.continuation, c.shuffle⟩)
    (fun _ h => Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
      (noNewRead_appendLanes h))
  simpa only [pos, dite_eq_left hh] using hActual

private theorem indexShuffleReturning {l : Launch} {X : Execution}
    {g site index count dst : Nat} {src recv : Value} {ok : Bool}
    {facts : List (Nat × Value)}
    (cur : MmaGroupIndexCursor l X g site index count dst src facts)
    (he : X.get (g, cur.pos) = some ⟨site, .shfl .idx src index 31 recv ok⟩) :
    let u := next (setReg cur.ready dst recv)
    EStep kernel Assumptions.all l g cur.ready ⟨site, .shfl .idx src index 31 recv ok⟩ (some u) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (cur.pos + 1)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (cur.pos + 1)) cur.lastState := by
  have hLen : cur.pos < (X.tr g).length := len_of_get he
  have hNotEmpty : (X.tr g).drop cur.pos ≠ [] :=
    fun h => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp h)
  obtain ⟨other, otherOk, hOther, _, hRest⟩ :=
    cur.shuffle.shuffle_at_nonempty cur.continuation hNotEmpty cur.shuffleCount
  rw [cur.checkpoint.1] at hOther
  have hKind := congrArg Event.kind (Option.some.inj (hOther.symm.trans he))
  obtain ⟨_, _, _, _, hRecv, hOk⟩ := Kind.shfl.inj hKind
  subst other
  subst otherOk
  have hStep : EStep kernel Assumptions.all l g cur.ready
      ⟨site, .shfl .idx src index 31 recv ok⟩ (some (next (setReg cur.ready dst recv))) :=
    ⟨_, cur.shuffle.stop, recv, ok, by rw [cur.checkpoint.1], rfl⟩
  refine ⟨hStep, ?_, hRest⟩
  rw [List.take_succ_eq_append_getElem hLen]
  have hEvent := he
  change (X.tr g)[cur.pos]? = _ at hEvent
  rw [List.getElem?_eq_getElem hLen, Option.some.injEq] at hEvent
  rw [hEvent]
  exact cur.runPrefix.snoc cur.shuffle.steps hStep

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g first batch shuffles : Nat}
    (hg : g < l.threads) (hFirst : first ≤ batch) (hBatch : batch < p.batch)
    (hGroup : batch < first + 31) (hNonzero : 0 < batch - first)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (start : ∀ h, SameWarp l g h →
      FallbackScanCursor l X h 2042 shuffles (mmaGroupEntryFacts p l h first))
include hp hMax hg hFirst hBatch hGroup hNonzero hLo hHi start

private theorem previousPrefixCursor :
    Nonempty (MmaGroupIndexCursor l X g 2057 (batch - first - 1) shuffles 2502
      (b32 (selectionLanePrefix p first (laneOf l g)))
      ((2501, b32 (batch - first - 1)) :: mmaSelectionFrame p l g first batch)) := by
  obtain ⟨pos, t, u, o, hLen, hCount, hVote, hRel, hAt, hPrefix, hTau, hRest⟩ :=
    mmaGroupRequestSelectedWithCounts hp hMax hg hFirst hBatch hGroup hLo hHi start
  let F := mmaSelectionFrame p l g first batch
  have hFresh : ∀ pair ∈ F, pair.1 ≠ 2501 := by
    intro pair hm
    simp only [F, mmaSelectionFrame, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact of_decide_eq_true rfl
  have hU : At u 2055 F := by at_select hAt
  have hPred := hAt.2.2.2.2.1
  obtain ⟨v, hv, hV⟩ := selectedPreviousLane (l := l) (g := g) hNonzero (by omega) hU hPred
    (by simp [F, mmaSelectionFrame]) hFresh
  have hOut := selectedPreviousPrefixShuffle hp (g := g) hV.1 hV.2.2.2.1 (by omega)
    (holds_lookup hV.2.2.2.2 (r := 2501) rfl) (holds_lookup hV.2.2.2.2 (r := 7197) rfl)
  exact ⟨⟨pos, t, v, o, hLen, hCount, hVote, hRel, hV, hPrefix, hRest,
    ⟨hTau.trans (run_rtg hv), hOut⟩⟩⟩

private theorem previousPrefixReady (hShuffles : 0 < shuffles) :
    let prefixWork := (∑ i ∈ Finset.range (batch - first), groupLaneTiles p first i) * p.heads
    ∃ pos t u o, pos ≤ (X.tr g).length ∧
      ((X.tr g).take pos).countP Execution.isShfl = shuffles + 1 ∧
      ((X.tr g).take pos).countP isFullWarpVote = 1 ∧
      (pos = (X.tr g).length → Step.Released l X g) ∧
      At u 2059 ((7201, b32 prefixWork) :: mmaSelectionFrame p l g first batch) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o := by
  classical
  let src (h : Nat) := b32 (selectionLanePrefix p first (laneOf l h))
  let facts (h : Nat) := (2501, b32 (batch - first - 1)) :: mmaSelectionFrame p l h first batch
  have cur (h : Nat) (hs : SameWarp l g h) :
      MmaGroupIndexCursor l X h 2057 (batch - first - 1) shuffles 2502 (src h) (facts h) :=
    Classical.choice (previousPrefixCursor hp hMax hs.1.2.1 hFirst hBatch hGroup hNonzero
      (hs.1.2.2 ▸ hLo) (hs.1.2.2 ▸ hHi) (fun peer hs' => start peer (Step.sameWarp_trans hs hs')))
  have hActual := mmaGroupIndexEvents hp hMax hShuffles src facts cur
  have hSelf : SameWarp l g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
  let c := cur g hSelf
  obtain ⟨recv, ok, he, hK⟩ := hActual g hSelf
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane : batch - first - 1 < 32 := by omega
  obtain ⟨hSame, hPeerLane⟩ := Step.sameWarp_lane hBlock hg hLane
  let peer := g - laneOf l g + (batch - first - 1)
  let d := cur peer hSame
  obtain ⟨peerRecv, peerOk, hPeer, hPeerK⟩ := hActual peer hSame
  have hPeerLane' : laneOf l peer = batch - first - 1 := hPeerLane
  have hSource : X.get (peer, d.pos) =
      some ⟨2057, .shfl .idx (b32 (selectionLanePrefix p first (batch - first - 1)))
        (batch - first - 1) 31 peerRecv peerOk⟩ := by
    simpa only [src, hPeerLane'] using hPeer
  have hFrame : ∀ pair ∈ facts g, pair.1 ≠ 2502 := by
    intro pair hm
    simp only [facts, mmaSelectionFrame, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact of_decide_eq_true rfl
  have hStepInfo := selectedPreviousPrefixStep hp hMax.1 (g := g) (i := c.pos) (j := d.pos)
    (ordinal := shuffles) (first := first) (peerIndex := batch - first - 1) (t := c.ready)
    (F := facts g) (recv := recv) (peerRecv := peerRecv) (ok := ok) (peerOk := peerOk)
    (show first < batch by omega) hGroup
  dsimp only at hStepInfo
  obtain ⟨t, hStep, hAt⟩ := hStepInfo c.checkpoint
    (holds_lookup c.checkpoint.2.2.2.2 (r := 2501) rfl)
    (holds_lookup c.checkpoint.2.2.2.2 (r := 7197) rfl)
    hFrame he hK hSource hPeerK (ShflK.not_exited hMax.1 hSame.1.2.1 hPeerK)
  obtain ⟨hReturn, hPast, hRest⟩ := indexShuffleReturning c he
  have hEq := Option.some.inj (estep_det hStep hReturn)
  subst t
  let F := mmaSelectionFrame p l g first batch
  have hF : ∀ pair ∈ F, pair.1 ≠ 7201 := by
    intro pair hm
    simp only [F, mmaSelectionFrame, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact of_decide_eq_true rfl
  obtain ⟨u, hu, hU⟩ := selectedPreviousWork hp g hFirst hGroup hBatch hF
    (by simp [F, mmaSelectionFrame])
    (hAt.mono ⟨hAt.2.2.2.2.1, hAt.2.2.2.2.2.2⟩)
  have hCount := countP_take_succ he (rfl : Execution.isShfl _ = true)
  change ((X.tr g).take (c.pos + 1)).countP Execution.isShfl =
    ((X.tr g).take c.pos).countP Execution.isShfl + 1 at hCount
  have hCount' : ((X.tr g).take (c.pos + 1)).countP Execution.isShfl = shuffles + 1 := by
    simpa only [c.shuffleCount] using hCount
  have hVote : ((X.tr g).take (c.pos + 1)).countP isFullWarpVote = 1 := by
    rw [List.take_add_one, show (X.tr g)[c.pos]? = _ from he]
    simpa [isWarpVote, voteClass] using c.voteCount
  exact ⟨c.pos + 1, _, u, c.lastState, len_of_get he, hCount', hVote,
    releasedIfLast he (by intro h; cases h), hU,
    hPast, run_rtg hu, hRest⟩
end

private def mmaSelectionPrefixWork (p : Params) (first batch : Nat) : Nat :=
  (∑ i ∈ Finset.range (batch - first), groupLaneTiles p first i) * p.heads

private def mmaSelectionRequestFacts (p : Params) (l : Launch) (g first batch : Nat) :
    List (Nat × Value) :=
  [(7148, b32 p.batch), (7156, b32 800), (7201, b32 (mmaSelectionPrefixWork p first batch))] ++
    mmaSelectionFrame p l g first batch

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g first batch shuffles : Nat}
    (hg : g < l.threads) (hFirst : first ≤ batch) (hBatch : batch < p.batch)
    (hGroup : batch < first + 31) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (start : ∀ h, SameWarp l g h →
      FallbackScanCursor l X h 2042 shuffles (mmaGroupEntryFacts p l h first))
include hp hMax hg hFirst hBatch hGroup hLo hHi start

private theorem requestTilesCursor (hShuffles : 0 < shuffles) :
    let count := if batch - first = 0 then shuffles else shuffles + 1
    Nonempty (MmaGroupIndexCursor l X g 2061 (batch - first) count 2503
      (b32 (groupLaneTiles p first (laneOf l g)))
      (mmaSelectionRequestFacts p l g first batch)) := by
  let F := (7201, b32 (mmaSelectionPrefixWork p first batch)) :: mmaSelectionFrame p l g first batch
  have hReady : ∃ pos t u o, pos ≤ (X.tr g).length ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        (if batch - first = 0 then shuffles else shuffles + 1) ∧
      ((X.tr g).take pos).countP isFullWarpVote = 1 ∧
      (pos = (X.tr g).length → Step.Released l X g) ∧ At u 2059 F ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o := by
    by_cases hZero : batch - first = 0
    · obtain ⟨pos, t, u, o, hLen, hCount, hVote, hRel, hAt, hPrefix, hTau, hRest⟩ :=
        mmaGroupRequestSelectedWithCounts hp hMax hg hFirst hBatch hGroup hLo hHi start
      have hWork : mmaSelectionPrefixWork p first batch = 0 := by
        simp [mmaSelectionPrefixWork, hZero]
      have hU : At u 2055 F := by
        simp only [F, hWork]
        at_select hAt
      obtain ⟨v, hv, hV⟩ :=
        selectedPrefixBranch (l := l) (g := g) hU hAt.2.2.2.2.1
      exact ⟨pos, t, v, o, hLen, by rwa [ite_eq_left hZero], hVote, hRel,
        by simpa only [ite_eq_left hZero] using hV, hPrefix, hTau.trans (run_rtg hv), hRest⟩
    · simpa only [ite_eq_right hZero, F, mmaSelectionPrefixWork] using
        previousPrefixReady hp hMax hg hFirst hBatch hGroup
          (Nat.pos_of_ne_zero hZero) hLo hHi start hShuffles
  obtain ⟨pos, t, u, o, hLen, hCount, hVote, hRel, hAt, hPast, hTau, hRest⟩ := hReady
  have hFrame : ∀ pair ∈ F, pair.1 ≠ 7156 ∧ pair.1 ≠ 7148 := by
    intro pair hm
    simp only [F, mmaSelectionFrame, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact of_decide_eq_true rfl
  obtain ⟨v, hv, hV⟩ := selectedTileParameters hp g hAt hFrame
  have hOut := selectedRequestTilesShuffle hp (g := g) hV.1 hV.2.2.2.1 (by omega)
    (holds_lookup hV.2.2.2.2 (r := 1187) rfl) (holds_lookup hV.2.2.2.2 (r := 7196) rfl)
  exact ⟨⟨pos, t, v, o, hLen, hCount, hVote, hRel, hV, hPast, hRest,
    ⟨hTau.trans (run_rtg hv), hOut⟩⟩⟩

/-- For a populated scheduler group, the actual ballot and indexed exchanges
reach the metadata reads of the assigned MMA request and tile in every maximal trace. -/
theorem mmaGroupMetadataOfMaximal (hShuffles : 0 < shuffles) :
    ∃ pos t u o, 0 < pos ∧ pos ≤ (X.tr g).length ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        (if batch - first = 0 then shuffles + 1 else shuffles + 2) ∧
      ((X.tr g).take pos).countP isFullWarpVote = 1 ∧
      (pos = (X.tr g).length → Step.Released l X g) ∧
      At u 2109 [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
        (7202, b32 (256 * ((assignedCoordinates p batch (g / l.block)).1 + 1))),
        (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o := by
  classical
  let count := if batch - first = 0 then shuffles else shuffles + 1
  let src (h : Nat) := b32 (groupLaneTiles p first (laneOf l h))
  let facts (h : Nat) := mmaSelectionRequestFacts p l h first batch
  have hCount : 0 < count := by dsimp [count]; split_ifs <;> omega
  have cur (h : Nat) (hs : SameWarp l g h) :
      MmaGroupIndexCursor l X h 2061 (batch - first) count 2503 (src h) (facts h) :=
    Classical.choice (requestTilesCursor hp hMax hs.1.2.1 hFirst hBatch hGroup (hs.1.2.2 ▸ hLo)
      (hs.1.2.2 ▸ hHi) (fun peer hs' => start peer (Step.sameWarp_trans hs hs')) hShuffles)
  have hActual := mmaGroupIndexEvents hp hMax hCount src facts cur
  have hSelf : SameWarp l g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
  let c := cur g hSelf
  obtain ⟨recv, ok, he, hK⟩ := hActual g hSelf
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane : batch - first < 32 := by omega
  obtain ⟨hSame, hPeerLane⟩ := Step.sameWarp_lane hBlock hg hLane
  let peer := g - laneOf l g + (batch - first)
  let d := cur peer hSame
  obtain ⟨peerRecv, peerOk, hPeer, hPeerK⟩ := hActual peer hSame
  have hPeerLane' : laneOf l peer = batch - first := hPeerLane
  have hSource : X.get (peer, d.pos) =
      some ⟨2061, .shfl .idx (b32 (groupLaneTiles p first (batch - first)))
        (batch - first) 31 peerRecv peerOk⟩ := by
    simpa only [src, hPeerLane'] using hPeer
  have hFrame : ∀ pair ∈ facts g, pair.1 ≠ 2503 := by
    intro pair hm
    simp only [facts, mmaSelectionRequestFacts, mmaSelectionFrame, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact of_decide_eq_true rfl
  have hStepInfo := selectedRequestTilesStep hp hMax.1 (g := g) (i := c.pos) (j := d.pos)
    (ordinal := count) (first := first) (peerIndex := batch - first) (t := c.ready) (F := facts g)
    (recv := recv) (peerRecv := peerRecv) (ok := ok) (peerOk := peerOk) hFirst hGroup hBatch
  dsimp only at hStepInfo
  obtain ⟨t, hStep, hAt⟩ := hStepInfo c.checkpoint
    (holds_lookup c.checkpoint.2.2.2.2 (r := 1187) rfl)
    (holds_lookup c.checkpoint.2.2.2.2 (r := 7196) rfl)
    hFrame he hK hSource hPeerK (ShflK.not_exited hMax.1 hSame.1.2.1 hPeerK)
  obtain ⟨hReturn, hPast, hRest⟩ := indexShuffleReturning c he
  have hEq := Option.some.inj (estep_det hStep hReturn)
  subst t
  have hWork : tilePrefix p first * p.heads + mmaSelectionPrefixWork p first batch =
      tilePrefix p batch * p.heads := by
    exact precedingGroupWork p hFirst hBatch hGroup
  obtain ⟨u, hu, hU⟩ := selectedMmaTileEntry hp g hBatch hWork hLo hHi _ (by at_select hAt)
  have hShfl : ((X.tr g).take (c.pos + 1)).countP Execution.isShfl =
      (if batch - first = 0 then shuffles + 1 else shuffles + 2) := by
    rw [countP_take_succ he (rfl : Execution.isShfl _ = true), c.shuffleCount]
    by_cases h : batch - first = 0 <;> simp [count, h, Nat.add_assoc]
  have hVote : ((X.tr g).take (c.pos + 1)).countP isFullWarpVote = 1 := by
    rw [List.take_add_one, show (X.tr g)[c.pos]? = _ from he]
    simpa [isWarpVote, voteClass] using c.voteCount
  exact ⟨c.pos + 1, _, u, c.lastState, Nat.zero_lt_succ _, len_of_get he, hShfl, hVote,
    releasedIfLast he (by intro h; cases h), hU, hPast, run_rtg hu, hRest⟩
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) (hProtected : DrainCuQProtected p X) (hBatch : batch < p.batch)
include hp hMax hg hw hProtected hBatch

/-- Every active MMA CTA reaches its assigned request's metadata reads. Search and
selection retain the real shuffle and ballot counts across arbitrarily many groups. -/
theorem mmaMetadataOfMaximal (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    let group := batch / 31
    let shuffles := 11 + 7 * group
    ∃ pos t u o, 0 < pos ∧ pos ≤ (X.tr g).length ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        (if batch % 31 = 0 then shuffles + 1 else shuffles + 2) ∧
      ((X.tr g).take pos).countP isFullWarpVote = 1 ∧
      (pos = (X.tr g).length → Step.Released l X g) ∧
      At u 2109 [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
        (7202, b32 (256 * ((assignedCoordinates p batch (g / l.block)).1 + 1))),
        (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o := by
  classical
  let group := batch / 31
  let first := 31 * group
  let shuffles := 11 + 7 * group
  have hDecomp : batch % 31 + first = batch := Nat.mod_add_div batch 31
  have hRest : batch % 31 < 31 := Nat.mod_lt _ (by decide)
  have hFirst : first ≤ batch := by omega
  have hGroup : batch < first + 31 := by omega
  have hRelative : batch - first = batch % 31 := by omega
  have hStart (peer : Nat) (hs : SameWarp l g peer) :
      Nonempty (FallbackScanCursor l X peer 2042 shuffles
        (mmaGroupEntryFacts p l peer first)) := by
    by_cases hZero : group = 0
    · have hFirstZero : first = 0 := by simp [first, hZero]
      have hOrdinal : shuffles = 11 := by simp [shuffles, hZero]
      have hEnd : batch + 1 ≤ min p.batch 31 := by omega
      have hCut := hHi.trans_le (Nat.mul_le_mul_right p.heads (tilePrefix_mono p hEnd))
      rw [hFirstZero, hOrdinal]
      exact firstMmaGroupEntryOfMaximal hp hMax hs.1.2.1 (hs.2.symm.trans hw)
        hProtected (hs.1.2.2 ▸ hCut)
    · let later := group - 1
      have hLater : 31 * (later + 1) = first := by dsimp [later, first]; omega
      have hOrdinal : 18 + 7 * later = shuffles := by dsimp [later, shuffles]; omega
      have hMore : first < p.batch := hFirst.trans_lt hBatch
      have hLower := (Nat.mul_le_mul_right p.heads (tilePrefix_mono p hFirst)).trans hLo
      have hEnd : batch + 1 ≤ min p.batch (first + 31) := by omega
      have hUpper : g / l.block < mmaFallbackCutoff p first :=
        hHi.trans_le (Nat.mul_le_mul_right p.heads (tilePrefix_mono p hEnd))
      have hLaterStart := laterMmaGroupOfMaximal hp hMax hProtected later hs.1.2.1
        (hs.2.symm.trans hw) (hLater.symm ▸ hMore)
        (hLater.symm ▸ hs.1.2.2 ▸ hLower) (hLater.symm ▸ hs.1.2.2 ▸ hUpper)
      rw [hLater, hOrdinal] at hLaterStart
      obtain ⟨c⟩ := hLaterStart
      exact ⟨⟨c.pos, c.before, c.state, c.lastState, c.pos_pos, c.pos_le, c.shuffleCount,
        c.ballotCount, c.released, by at_select c.checkpoint, c.runPrefix, c.localSteps,
        c.continuation⟩⟩
  simpa only [hRelative] using mmaGroupMetadataOfMaximal hp hMax hg hFirst hBatch hGroup hLo hHi
    (fun peer hs => Classical.choice (hStart peer hs)) (by dsimp [shuffles]; omega)

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
