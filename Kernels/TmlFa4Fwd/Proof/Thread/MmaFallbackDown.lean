-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFallbackReads
import Lemmas.Step.WarpShuffleProgress
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (fallbackAbi groupScanFacts localRun out_eq_core)

def fallbackOffsetFacts (p : Params) (l : Launch) (g first : Nat) : List (Nat × Value) :=
  (7195, b32 (drainCuQ p (first + laneOf l g))) ::
    (1184, b32 (first + laneOf l g)) :: fallbackReadFrame p l g first

/-- Exact maximal-trace boundary for one lane of the fallback group's scan. -/
structure FallbackScanCursor (l : Launch) (X : Execution) (g site shuffles : Nat)
    (facts : List (Nat × Value)) where
  pos : Nat
  before : TState
  state : TState
  lastState : Option TState
  pos_pos : 0 < pos
  pos_le : pos ≤ (X.tr g).length
  shuffleCount : ((X.tr g).take pos).countP Execution.isShfl = shuffles
  ballotCount : ((X.tr g).take pos).countP isFullWarpVote = 0
  released : pos = (X.tr g).length → Step.Released l X g
  checkpoint : At state site facts
  runPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before)
  localSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before state
  continuation : Run kernel Assumptions.all l g before ((X.tr g).drop pos) lastState

theorem firstFallbackOffsetCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hProtected : DrainCuQProtected p X) (hBatch : 31 < p.batch)
    (hCut : tilePrefix p 31 * p.heads ≤ g / l.block) :
    Nonempty (FallbackScanCursor l X g 2000 11 (fallbackOffsetFacts p l g 31)) := by
  obtain ⟨pos, t, u, o, hPos, hLen, hShfl, hVote, hRel, hAt, hPast, hTau, hTail⟩ :=
    firstFallbackLaneReadOfMaximal hp hMax hg hw hProtected hBatch hCut
  exact ⟨⟨pos, t, u, o, hPos, hLen, hShfl, hVote, hRel, hAt, hPast, hTau, hTail⟩⟩

private theorem fallbackLaneSentinel (l : Launch) (g : Nat) {lane : Nat} (hLane : lane < 32) :
    Seg kernel [] l g 1 2000 [(1180, b32 lane)] 2001
      [(349, .pred (decide (lane = 31)))] := by
  intro t ht
  have h32 : lane < 2 ^ 32 := by omega
  have h64 : lane < 2 ^ 64 := by omega
  have h31 : (↑(truncBits 32 (BitVec.ofInt 64 31)).toNat : Int) = 31 := rfl
  seg_fp ht using
    simp only [compare, Option.getD_some, truncBits_ofNat h32 (by decide),
      toNat_ofNat_lt h64, h31, Value.pred.injEq, decide_eq_decide]
    omega

private theorem fallbackDownTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {word : Nat} (ht : At t 2001 [(7195, b32 word)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .down (b32 word) 1 31
      (fun v _ => next (setReg t 2477 v))) := by
  rw [out_eq_core (by rw [ht.1]; decide) (by rw [ht.1]; decide),
    out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_2001) rfl rfl]
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  change Out.ev (shflTmpl l g t .down 2477 none (.reg 7195) (.imm 1) (.imm 31) (.imm (-1))) = _
  simp [shflTmpl, readValue, readReg, ht.2.2.2.2.1, hBlock, Value.bytes, b32, readBits,
    pure, Except.pure]
  rfl

def fallbackDownFacts (p : Params) (l : Launch) (g first : Nat) :
    List (Nat × Value) :=
  (349, .pred (decide (laneOf l g = 31))) :: fallbackOffsetFacts p l g first

private theorem prepareFallbackDown {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {X : Execution} {g first count : Nat}
    (c : FallbackScanCursor l X g 2000 count (fallbackOffsetFacts p l g first)) :
    ∃ u, At u 2001 (fallbackDownFacts p l g first) ∧
      Next kernel Assumptions.all l g c.before u
        (.shfl .down (b32 (drainCuQ p (first + laneOf l g))) 1 31
          (fun v _ => next (setReg u 2477 v))) := by
  obtain ⟨u, hu, hU⟩ :=
    fallbackLaneSentinel l g (Nat.mod_lt _ (by decide)) c.state (by at_select c.checkpoint)
  have hKeep : ∀ r ∈ [7195, 1184, 1183, 7199, 7203, 1182, 1072, 7194, 1180, 7139,
      2535, 7502, 7506, 7503], u.regs r = c.state.regs r :=
    fun _ => schedulerLocalFrame (lo := 2000) (len := 1) (by decide +kernel) (by decide)
      hu c.checkpoint.1.ge (by rw [c.checkpoint.1])
  have hFrame := holdsSchedulerFrame c.checkpoint.2.2.2.2 hKeep (fun _ hm =>
    List.mem_map_of_mem (f := Prod.fst) hm)
  have hAt : At u 2001 (fallbackDownFacts p l g first) :=
    hU.mono ⟨hU.2.2.2.2.1, hFrame⟩
  exact ⟨u, hAt, c.localSteps.trans
    (run_rtg (localRun (by decide) (by decide) c.checkpoint.1 (by decide) hu)),
    fallbackDownTemplate hp (by at_select hAt)⟩

def fallbackNeighborFacts (p : Params) (l : Launch) (g first : Nat) :
    List (Nat × Value) :=
  (2477, b32 (drainCuQ p (first + (shflSource .down (laneOf l g) 1 31).1))) ::
    fallbackDownFacts p l g first

/-- Consume the actual full-warp exchange at the cursor's ordinal and preserve the
remaining register facts. Each source lane can have its own event position. -/
theorem FallbackScanCursor.shuffleOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g site count dst : Nat} (hg : g < l.threads) (mode : ShflMode) (offset clamp : Nat)
    (facts : Nat → List (Nat × Value)) (value : Nat → Value)
    (cur : ∀ h, SameWarp l g h → FallbackScanCursor l X h site count (facts h))
    (hOut : ∀ h (hw : SameWarp l g h),
      out kernel Assumptions.all l h (cur h hw).state =
        .ev (.shfl mode (value (laneOf l h)) offset clamp
          (fun v _ => next (setReg (cur h hw).state dst v))))
    (hKeep : ∀ pair ∈ facts g, pair.1 ≠ dst) :
    Nonempty (FallbackScanCursor l X g (site + 1) (count + 1)
      ((dst, value (shflSource mode (laneOf l g) offset clamp).1) :: facts g)) := by
  classical
  let sent (h : Nat) := value (laneOf l h)
  let pos (h : Nat) := if hs : SameWarp l g h then (cur h hs).pos else 0
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hActual (h : Nat) (hs : SameWarp l g h) :
      ∃ recv ok, X.get (h, (cur h hs).pos) = some ⟨site, .shfl mode (sent h) offset clamp recv ok⟩ ∧
        X.ShflK (h, (cur h hs).pos) count := by
    have h := Step.shfl_occurs_of_maximal hMax hBlock hs.1.2.1 pos sent (fun _ => offset)
      (fun _ => clamp)
      (by
        intro peer hw
        let c := cur peer (Step.sameWarp_trans hs hw)
        exact .inl (List.ne_nil_of_length_pos (c.pos_pos.trans_le c.pos_le)))
      (by
        intro peer hw
        have hpWarp := Step.sameWarp_trans hs hw
        simp only [pos, dite_eq_left hpWarp]
        let c := cur peer hpWarp
        exact ⟨c.before, c.state, c.lastState, _, c.pos_le, c.shuffleCount, c.released,
          c.checkpoint.1, c.runPrefix, c.continuation, c.localSteps, hOut peer hpWarp⟩)
      (fun _ h => Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
        (noNewRead_appendLanes h))
    simpa only [pos, dite_eq_left hs] using h
  have hSelf : SameWarp l g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
  let c := cur g hSelf
  let v := c.state
  obtain ⟨recv, ok, he, hK⟩ := hActual g hSelf
  change X.get (g, c.pos) = _ at he
  have hLen : c.pos < (X.tr g).length := len_of_get he
  let source := (shflSource mode (laneOf l g) offset clamp).1
  let peer := g - laneOf l g + source
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨hSame, hLaneOf⟩ :=
    Step.sameWarp_lane hBlock hg (Step.shflSource_lt mode hLane offset clamp)
  obtain ⟨other, peerOk, hPeer, hPeerK⟩ := hActual peer hSame
  have hValue := (shfl_source_value hMax.1 he hK hPeer hPeerK
    (ShflK.not_exited hMax.1 hSame.1.2.1 hPeerK)).1
  have hLaneOf' : laneOf l peer = source := hLaneOf
  have hRecv : recv = value source := by simpa only [sent, hLaneOf'] using hValue
  have hV := c.checkpoint
  have hNext : Next kernel Assumptions.all l g c.before v
      (.shfl mode (sent g) offset clamp (fun w _ => next (setReg v dst w))) :=
    ⟨c.localSteps, hOut g hSelf⟩
  have hRemain : (X.tr g).drop c.pos ≠ [] :=
    fun h => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp h)
  obtain ⟨val, valid, hGet, _, hRest⟩ :=
    hNext.shuffle_at_nonempty c.continuation hRemain c.shuffleCount
  rw [hV.1] at hGet
  have hKind := congrArg Event.kind (Option.some.inj (hGet.symm.trans he))
  obtain ⟨_, _, _, _, hVal, hFlag⟩ := Kind.shfl.inj hKind
  subst val
  subst valid
  let u := next (setReg v dst recv)
  have hStep : EStep kernel Assumptions.all l g v
      ⟨site, .shfl mode (sent g) offset clamp recv ok⟩ (some u) :=
    ⟨_, hNext.stop, recv, ok, by rw [hV.1], rfl⟩
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos + 1)) (some u) := by
    rw [List.take_succ_eq_append_getElem hLen]
    have hEvent := he
    change (X.tr g)[c.pos]? = _ at hEvent
    rw [List.getElem?_eq_getElem hLen, Option.some.injEq] at hEvent
    rw [hEvent]
    exact c.runPrefix.snoc hNext.steps hStep
  have hU := hV.set (r := dst) (v := recv) hKeep
  have hAt : At u (site + 1) ((dst, value source) :: facts g) :=
    hU.mono ⟨hRecv ▸ hU.2.2.2.2.1, hU.2.2.2.2.2⟩
  have hShfl := countP_take_succ he (rfl : Execution.isShfl _ = true)
  rw [c.shuffleCount] at hShfl
  have hBallot : ((X.tr g).take (c.pos + 1)).countP isFullWarpVote = 0 := by
    rw [List.take_add_one, show (X.tr g)[c.pos]? = _ from he]
    simpa [isWarpVote, voteClass] using c.ballotCount
  exact ⟨⟨c.pos + 1, u, u, c.lastState, Nat.zero_lt_succ _, len_of_get he, hShfl, hBallot,
    releasedIfLast he (by intro h; cases h), hAt, hPast, .refl, hRest⟩⟩

/-- The fallback group's recorded down exchange supplies the next lane's launch offset,
while preserving the exact execution cursor and the original group ABI. -/
theorem fallbackDownOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first count : Nat} (hg : g < l.threads)
    (cur : ∀ h, SameWarp l g h → FallbackScanCursor l X h 2000 count
      (fallbackOffsetFacts p l h first)) :
    Nonempty (FallbackScanCursor l X g 2002 (count + 1) (fallbackNeighborFacts p l g first)) := by
  classical
  let ready (h : Nat) (hw : SameWarp l g h) := Classical.choose (prepareFallbackDown hp (cur h hw))
  let nextCursor (h : Nat) (hw : SameWarp l g h) :
      FallbackScanCursor l X h 2001 count (fallbackDownFacts p l h first) :=
    let c := cur h hw
    let hs := Classical.choose_spec (prepareFallbackDown hp c)
    ⟨c.pos, c.before, ready h hw, c.lastState, c.pos_pos, c.pos_le, c.shuffleCount, c.ballotCount,
      c.released, hs.1, c.runPrefix, hs.2.steps, c.continuation⟩
  exact FallbackScanCursor.shuffleOfMaximal hp hMax hg .down 1 31
    (fun h => fallbackDownFacts p l h first) (fun lane => b32 (drainCuQ p (first + lane)))
    nextCursor (fun h hw => (Classical.choose_spec (prepareFallbackDown hp (cur h hw))).2.stop)
    (of_decide_eq_true rfl)

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
