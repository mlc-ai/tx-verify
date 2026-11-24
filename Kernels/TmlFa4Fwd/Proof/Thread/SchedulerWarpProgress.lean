-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupRoute
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Step.WarpShuffleProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- An actual scheduler checkpoint with the recorded prefix and readiness of each lane. -/
structure SchedulerWarpReached (l : Launch) (X : Execution) (g pc : Nat)
    (F : Nat → List (Nat × Value)) (shuffles votes : Nat) (ends : Nat → Option TState)
    extends SchedulerWarpAt l X g pc F shuffles votes ends where
  positive : ∀ lane < 32, 0 < pos lane
  bounded : ∀ lane < 32, pos lane ≤ (X.tr (warpLane l g lane)).length
  released : ∀ lane < 32, pos lane = (X.tr (warpLane l g lane)).length →
    Step.Released l X (warpLane l g lane)
  recorded : ∀ lane < 32, Run kernel Assumptions.all l (warpLane l g lane) {}
    ((X.tr (warpLane l g lane)).take (pos lane)) (some (before lane))

/-- Reframe a checkpoint that preserves the recorded lane boundaries. -/
def SchedulerWarpReached.reframe {l : Launch} {X : Execution}
    {g pc pc' shuffles votes : Nat} {F G : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g pc F shuffles votes ends)
    (next : SchedulerWarpAt l X g pc' G shuffles votes ends)
    (hPos : next.pos = cur.pos) (hState : next.before = cur.before) :
    SchedulerWarpReached l X g pc' G shuffles votes ends := by
  refine { toSchedulerWarpAt := next
           positive := ?_, bounded := ?_, released := ?_, recorded := ?_ }
  · rw [hPos]; exact cur.positive
  · rw [hPos]; exact cur.bounded
  · rw [hPos]; exact cur.released
  · rw [hPos,hState]; exact cur.recorded

/-- Move every lane through an event-free decoded segment at the same trace boundary. -/
theorem SchedulerWarpReached.advanceLocalWithPosition {l : Launch} {X : Execution}
    {g pc pc' shuffles votes : Nat} {F G : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g pc F shuffles votes ends)
    (hLocal : ∀ lane < 32, ∃ u : TState,
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) (cur.state lane) u ∧
        At u pc' (G lane)) :
    ∃ next : SchedulerWarpReached l X g pc' G shuffles votes ends, next.pos = cur.pos := by
  obtain ⟨next,hPos,hState⟩ := cur.toSchedulerWarpAt.advanceLocalPreserving hLocal
  exact ⟨cur.reframe next hPos hState,hPos⟩

/-- Move every lane through an event-free decoded segment at the same trace boundary. -/
theorem SchedulerWarpReached.advanceLocal {l : Launch} {X : Execution}
    {g pc pc' shuffles votes : Nat} {F G : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g pc F shuffles votes ends)
    (hLocal : ∀ lane < 32, ∃ u : TState,
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) (cur.state lane) u ∧
        At u pc' (G lane)) : Nonempty (SchedulerWarpReached l X g pc' G shuffles votes ends) := by
  obtain ⟨next,_⟩ := cur.advanceLocalWithPosition hLocal
  exact ⟨next⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g pc shuffles votes dst : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g pc F shuffles votes ends) (mode : ShflMode) (a : Nat → Value)
    (b c : Nat → Nat) (hFresh : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ dst)
    (hOut : ∀ lane < 32,
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
        .ev (.shfl mode (a lane) (b lane) (c lane)
          (fun v _ => next (setReg (cur.state lane) dst v))))
include hp hMax hg cur mode a b c hFresh hOut

/-- A reached warp consumes its actual matched shuffles and keeps their recorded boundaries. -/
theorem SchedulerWarpReached.consumeShuffleWithEvents :
    ∃ next : SchedulerWarpReached l X g (pc+1)
      (fun lane => (dst, a (shflSource mode lane (b lane) (c lane)).1) :: F lane)
      (shuffles+1) votes ends,
      ∀ lane < 32, next.pos lane = cur.pos lane+1 ∧
        ∃ recv ok, X.get (warpLane l g lane,cur.pos lane) =
          some ⟨pc,.shfl mode (a lane) (b lane) (c lane) recv ok⟩ ∧
          X.ShflK (warpLane l g lane,cur.pos lane) shuffles := by
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSame (lane : Nat) (hl : lane < 32) := Step.sameWarp_lane hBlock hg hl
  have hSuffix (lane : Nat) (hl : lane < 32) : (X.tr (thread lane)).drop (cur.pos lane) ≠ [] := by
    have hWarp (h : Nat) (hs : SameWarp l (thread lane) h) : SameWarp l g h :=
      Step.sameWarp_trans (hSame lane hl).1 hs
    obtain ⟨recv, ok, he, _⟩ := Step.shfl_occurs_of_maximal hMax hBlock (hSame lane hl).1.1.2.1
      (cur.pos ∘ laneOf l) (a ∘ laneOf l) (b ∘ laneOf l) (c ∘ laneOf l)
      (pc := pc) (ordinal := shuffles) (mode := mode)
      (fun h hs => by
        have hEq := Step.warpLane_of_sameWarp (hWarp h hs)
        rw [← hEq]
        apply Or.inl
        let hLane := laneOf l h
        have hLaneLt : hLane < 32 := Nat.mod_lt _ (by decide)
        have hPos := cur.positive hLane hLaneLt
        have hBound := cur.bounded hLane hLaneLt
        change X.tr (thread hLane) ≠ []
        intro hNil
        rw [hNil,List.length_nil] at hBound
        omega)
      (fun h hs => by
        let k := laneOf l h
        have hk : k < 32 := Nat.mod_lt _ (by decide)
        have hEq : warpLane l g k = h := Step.warpLane_of_sameWarp (hWarp h hs)
        let dest := fun (v : Value) (_ : Bool) => next (setReg (cur.state k) dst v)
        refine ⟨cur.before k,cur.state k,ends k,dest,?_,?_,?_,
          (cur.checkpoint k hk).1,?_,?_,?_⟩
        · simpa only [Function.comp_apply,hEq] using cur.bounded k hk
        · simpa only [Function.comp_apply,hEq] using cur.ordinals.shfl k hk
        · simpa only [Function.comp_apply,hEq] using cur.released k hk
        · simpa only [Function.comp_apply,hEq] using cur.recorded k hk
        · simpa only [Function.comp_apply,hEq] using cur.continuation k hk
        · have hn : Next kernel Assumptions.all l (warpLane l g k) (cur.before k) (cur.state k)
              (.shfl mode (a k) (b k) (c k) dest) := ⟨cur.localSteps k hk,hOut k hk⟩
          simpa only [Function.comp_apply,hEq] using hn)
      (fun _ h => Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
        (noNewRead_appendLanes h))
    have hIndex : laneOf l (thread lane) = lane := (hSame lane hl).2
    change X.get (thread lane,cur.pos (laneOf l (thread lane))) = _ at he
    have hLen := len_of_get he
    change cur.pos (laneOf l (thread lane)) < (X.tr (thread lane)).length at hLen
    rw [hIndex] at hLen
    exact fun hNil => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp hNil)
  obtain ⟨result,hPos,recv,ok,hEvent⟩ :=
    cur.toSchedulerWarpAt.consumeShufflePresent hp hMax.1 hg mode a b c hFresh hOut hSuffix
  refine ⟨{ toSchedulerWarpAt := result
            positive := ?_, bounded := ?_, released := ?_, recorded := ?_ },?_⟩
  · rw [hPos]
    intro lane _
    exact Nat.succ_pos _
  · rw [hPos]
    exact fun lane hl => len_of_get (hEvent lane hl).1
  · rw [hPos]
    exact fun lane hl => releasedIfLast (hEvent lane hl).1 (by intro h; cases h)
  · intro lane hl
    have hGet := (hEvent lane hl).1
    have hState := (hEvent lane hl).2
    have hLen : cur.pos lane < (X.tr (thread lane)).length := len_of_get hGet
    rw [hPos,hState,List.take_succ_eq_append_getElem hLen,
      (List.getElem?_eq_some_iff.mp hGet).2]
    apply (cur.recorded lane hl).snoc (cur.localSteps lane hl)
    exact ⟨_,hOut lane hl,recv lane,ok lane,by rw [(cur.checkpoint lane hl).1],rfl⟩
  · intro lane hl
    exact ⟨congrFun hPos lane,recv lane,ok lane,(hEvent lane hl).1,
      ⟨⟨_,_,_,_,_,_,_,(hEvent lane hl).1⟩,cur.ordinals.shfl lane hl⟩⟩

/-- Every reached lane executes the same scheduler shuffle in a maximal execution. -/
theorem SchedulerWarpReached.consumeShuffle :
    Nonempty (SchedulerWarpReached l X g (pc+1)
      (fun lane => (dst, a (shflSource mode lane (b lane) (c lane)).1) :: F lane)
      (shuffles+1) votes ends) := by
  obtain ⟨next,_⟩ := cur.consumeShuffleWithEvents hp hMax hg mode a b c hFresh hOut
  exact ⟨next⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
