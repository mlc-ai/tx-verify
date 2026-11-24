-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFallbackSearch
import Kernels.TmlFa4Fwd.Proof.MmaBallotObservation
import Kernels.TmlFa4Fwd.Proof.MmaModel
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Lemmas.Step.WarpVoteProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (prepareMmaGroupVote selectedGroupVote out_eq_core
  groupInputRegs voteFrameRegs observedMmaGroupVote)

/-- The register facts shared by first and later populated MMA group entrances. -/
noncomputable def mmaGroupEntryFacts (p : Params) (l : Launch) (g first : Nat) :
    List (Nat × Value) :=
  [(7199, b32 first), (7203, b32 p.batch),
    (7198, b32 (∑ i ∈ Finset.range 32, groupLaneTiles p first i)),
    (7197, b32 (∑ i ∈ Finset.range (laneOf l g + 1), groupLaneTiles p first i)),
    (7200, b32 (mmaFallbackCutoff p first)), (7139, b32 p.heads),
    (1072, b32 (g / l.block)), (7196, b32 (groupLaneTiles p first (laneOf l g))),
    (7502, b64 p.cuQBase), (7503, b64 p.usedKBase), (2535, b32 l.sharedBase)]

theorem firstMmaGroupEntryOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hProtected : DrainCuQProtected p X)
    (hCut : g / l.block < tilePrefix p (min p.batch 31) * p.heads) :
    Nonempty (FallbackScanCursor l X g 2042 11 (mmaGroupEntryFacts p l g 0)) := by
  obtain ⟨pos, e, t, u, o, hPos, hLen, he, hSite, hBefore, hShfl, hRel, hAt, hPast, hTau, hRest⟩ :=
    firstGroupSelectionStart hp hMax hg hw hProtected hCut
  have hIndex : pos - 1 + 1 = pos := by omega
  have hCount := firstGroupBroadcastBallotCount hp hMax.1 hg hw he hSite hBefore
    (hIndex.symm ▸ hPast)
  rw [hIndex] at hCount
  exact ⟨⟨pos, t, u, o, hPos, hLen, hShfl, hCount, hRel, hAt, hPast, hTau, hRest⟩⟩

private def selectedGroupVoteFacts (p : Params) (l : Launch) (g first batch : Nat) :
    List (Nat × Value) :=
  [(362, .pred (decide (first + laneOf l g < batch))), (1186, b32 (tilePrefix p first * p.heads)),
    (7199, b32 first), (7196, b32 (groupLaneTiles p first (laneOf l g))),
    (7197, b32 (∑ i ∈ Finset.range (laneOf l g + 1), groupLaneTiles p first i)),
    (1072, b32 (g / l.block)), (7139, b32 p.heads), (7502, b64 p.cuQBase),
    (7503, b64 p.usedKBase), (2535, b32 l.sharedBase)]

private structure SelectedGroupVoteCursor (p : Params) (l : Launch) (X : Execution)
    (g first batch shuffles : Nat) where
  pos : Nat
  before : TState
  ready : TState
  lastState : Option TState
  pos_pos : 0 < pos
  pos_le : pos ≤ (X.tr g).length
  released : pos = (X.tr g).length → Step.Released l X g
  shuffleCount : ((X.tr g).take pos).countP Execution.isShfl = shuffles
  ordinal : ((X.tr g).take pos).countP isFullWarpVote = 0
  checkpoint : At ready 2050 (selectedGroupVoteFacts p l g first batch)
  runPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before)
  continuation : Run kernel Assumptions.all l g before ((X.tr g).drop pos) lastState
  vote : Next kernel Assumptions.all l g before ready
    (.vote (2 ^ 32 - 1) (decide (first + laneOf l g < batch))
      (fun word => next (setReg ready 2500 (b32 word.toNat))))

private theorem selectedGroupVoteCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first batch shuffles : Nat}
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (c : FallbackScanCursor l X g 2042 shuffles (mmaGroupEntryFacts p l g first)) :
    Nonempty (SelectedGroupVoteCursor p l X g first batch shuffles) := by
  let F := [(7199, b32 first), (7196, b32 (groupLaneTiles p first (laneOf l g))),
    (7197, b32 (∑ i ∈ Finset.range (laneOf l g + 1), groupLaneTiles p first i)),
    (1072, b32 (g / l.block)), (7139, b32 p.heads), (7502, b64 p.cuQBase),
    (7503, b64 p.usedKBase), (2535, b32 l.sharedBase)]
  have hFrame : ∀ pair ∈ F, pair.1 ∈ groupInputRegs := by
    intro pair hm
    simp only [F, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact of_decide_eq_true rfl
  obtain ⟨v, hv, hV⟩ :=
    prepareMmaGroupVote hp hFirst hGroup hBatch hLo hHi
      hFrame (by at_select c.checkpoint)
  have hV' : At v 2050 (selectedGroupVoteFacts p l g first batch) := by
    simpa only [selectedGroupVoteFacts, F, List.cons_append, List.nil_append] using hV
  have hOut := selectedGroupVote hp g v _ hV'.1 hV'.2.2.2.1 hV'.2.2.2.2.1
  exact ⟨⟨c.pos, c.before, v, c.lastState, c.pos_pos, c.pos_le, c.released, c.shuffleCount,
    c.ballotCount, hV', c.runPrefix, c.continuation,
    ⟨c.localSteps.trans (run_rtg hv),
      (out_eq_core (by rw [hV'.1]; decide) (by rw [hV'.1]; decide)).trans hOut⟩⟩⟩

private theorem selectedGroupWarpVote {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first batch shuffles : Nat} (hFirst : first ≤ batch)
    (hBatch : batch < p.batch) (hGroup : batch < first + 31)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (start : ∀ h, SameWarp l g h →
      FallbackScanCursor l X h 2042 shuffles (mmaGroupEntryFacts p l h first)) :
    ∃ cur : ∀ h, SameWarp l g h → SelectedGroupVoteCursor p l X h first batch shuffles,
      ∀ h (hw : SameWarp l g h), ∃ word,
        X.get (h, (cur h hw).pos) =
          some ⟨2050, .vote (2 ^ 32 - 1) (decide (first + laneOf l h < batch)) word⟩ ∧
        X.MaskK voteClass (h, (cur h hw).pos) (2 ^ 32 - 1) 0 := by
  classical
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have cur (h : Nat) (hh : SameWarp l g h) : SelectedGroupVoteCursor p l X h first batch shuffles :=
    Classical.choice (selectedGroupVoteCursor hp hFirst hGroup hBatch
      (hh.1.2.2 ▸ hLo) (hh.1.2.2 ▸ hHi) (start h hh))
  let pos (h : Nat) := if hh : SameWarp l g h then (cur h hh).pos else 0
  refine ⟨cur, ?_⟩
  intro h hh
  have hActual := Step.ballot_occurs_of_maximal hMax hBlock hh.1.2.1
    pos (fun h => decide (first + laneOf l h < batch))
    (by
      intro peer _
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true (Nat.mod_lt _ (by decide)))
    (by
      intro peer hpWarp
      let c := cur peer (Step.sameWarp_trans hh hpWarp)
      exact .inl (List.ne_nil_of_length_pos (c.pos_pos.trans_le c.pos_le)))
    (by
      intro peer hpWarp
      have hPeer := Step.sameWarp_trans hh hpWarp
      simp only [pos, dite_eq_left hPeer]
      let c := cur peer hPeer
      exact ⟨c.before, c.ready, c.lastState, _, c.pos_le, c.ordinal, c.released,
        c.checkpoint.1, c.runPrefix, c.continuation, c.vote⟩)
    (fun _ h => Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
      (noNewRead_appendLanes h))
  simpa only [pos, dite_eq_left hh] using hActual

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) (hProtected : DrainCuQProtected p X) (hBatch : batch < p.batch)
    (hGroup : batch < 31) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
include hp hMax hg hw hProtected hBatch hGroup hLo

omit hp hMax hg hw hProtected hBatch hGroup hLo in
private theorem countBallotReturn {X : Execution} {g pos site mask : Nat} {hit : Bool}
    {word : BitVec 32} (he : X.get (g, pos) = some ⟨site, .vote mask hit word⟩)
    (hc : ((X.tr g).take pos).countP (isWarpVote mask) = 0) :
    ((X.tr g).take (pos + 1)).countP (isWarpVote mask) = 1 := by
  rw [List.take_add_one, show (X.tr g)[pos]? = _ from he]
  simp only [Option.toList_some, List.countP_append, List.countP_cons, hc, isWarpVote, voteClass,
    Option.any_some, BEq.rfl, List.countP_nil, ite_true, Nat.zero_add]

omit hp hMax hg hw hProtected hBatch hGroup hLo in
/-- The actual selected-group vote selects the request and leaves a returning cursor for the
two indexed scheduler exchanges. -/
theorem mmaGroupRequestSelectedWithCounts {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first batch shuffles : Nat} (hg : g < l.threads) (hFirst : first ≤ batch)
    (hBatch : batch < p.batch) (hGroup : batch < first + 31)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (start : ∀ h, SameWarp l g h →
      FallbackScanCursor l X h 2042 shuffles (mmaGroupEntryFacts p l h first)) :
    ∃ pos t u o, pos ≤ (X.tr g).length ∧
      ((X.tr g).take pos).countP Execution.isShfl = shuffles ∧
      ((X.tr g).take pos).countP isFullWarpVote = 1 ∧
      (pos = (X.tr g).length → Step.Released l X g) ∧
      At u 2055 [(363, .pred (decide (batch - first = 0))), (7201, b32 0),
        (1187, b32 (batch - first)),
        (7196, b32 (groupLaneTiles p first (laneOf l g))),
        (7197, b32 (∑ i ∈ Finset.range (laneOf l g + 1), groupLaneTiles p first i)),
        (1186, b32 (tilePrefix p first * p.heads)), (1072, b32 (g / l.block)),
        (7139, b32 p.heads), (7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
        (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o := by
  obtain ⟨cur, hActual⟩ := selectedGroupWarpVote hp hMax hFirst hBatch hGroup hLo hHi start
  have hSelf : SameWarp l g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
  let c := cur g hSelf
  obtain ⟨word, he, hOrdinal⟩ := hActual g hSelf
  change X.get (g, c.pos) = _ at he
  have hLen : c.pos < (X.tr g).length := len_of_get he
  have hNotEmpty : (X.tr g).drop c.pos ≠ [] :=
    fun h => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp h)
  obtain ⟨other, hOther, _, hRest⟩ :=
    c.vote.ballot_at_nonempty c.continuation hNotEmpty c.ordinal
  rw [c.checkpoint.1] at hOther
  have hWord : other = word := by
    have hE := congrArg Event.kind (Option.some.inj (hOther.symm.trans he))
    exact (Kind.vote.inj hE).2.2
  subst other
  let F := [(1186, b32 (tilePrefix p first * p.heads)),
    (7199, b32 first), (7196, b32 (groupLaneTiles p first (laneOf l g))),
    (7197, b32 (∑ i ∈ Finset.range (laneOf l g + 1), groupLaneTiles p first i)),
    (1072, b32 (g / l.block)), (7139, b32 p.heads), (7502, b64 p.cuQBase),
    (7503, b64 p.usedKBase), (2535, b32 l.sharedBase)]
  have hFrame : ∀ pair ∈ F, pair.1 ∈ voteFrameRegs := by
    intro pair hm
    simp only [F, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact of_decide_eq_true rfl
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hPeers : ∀ lane < 32, ∃ j val,
      let e := (g - laneOf l g + lane, j)
      X.get e = some ⟨2050, .vote (2 ^ 32 - 1) (decide (first + lane < batch)) val⟩ ∧
        X.MaskK voteClass e (2 ^ 32 - 1) 0 := by
    intro lane hl
    obtain ⟨sameWarp, hLane⟩ := Step.sameWarp_lane hBlock hg hl
    obtain ⟨val, hGet, hK⟩ := hActual (warpLane l g lane) sameWarp
    refine ⟨(cur (warpLane l g lane) sameWarp).pos, val, ?_, hK⟩
    change laneOf l (warpLane l g lane) = lane at hLane
    rw [hLane] at hGet
    simpa only [warpLane] using hGet
  obtain ⟨u, hStep, hRun, hU⟩ := observedMmaGroupVote hp hMax.1 hFirst hGroup hBatch
    c.checkpoint hFrame (by simp) he hOrdinal hPeers
  have hReturning : Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos + 1))
      (some (next (setReg c.ready 2500 (b32 word.toNat)))) := by
    rw [List.take_succ_eq_append_getElem hLen]
    have hEvent := he
    change (X.tr g)[c.pos]? = _ at hEvent
    rw [List.getElem?_eq_getElem hLen, Option.some.injEq] at hEvent
    rw [hEvent]
    exact c.runPrefix.snoc c.vote.steps hStep
  have hShfl : ((X.tr g).take (c.pos + 1)).countP Execution.isShfl = shuffles := by
    rw [List.take_add_one, show (X.tr g)[c.pos]? = _ from he]
    simpa [Execution.isShfl] using c.shuffleCount
  have hVote := countBallotReturn he c.ordinal
  exact ⟨c.pos + 1, _, u, c.lastState, len_of_get he, hShfl, hVote,
    releasedIfLast he (by intro h; cases h), by at_select hU, hReturning, run_rtg hRun, hRest⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
