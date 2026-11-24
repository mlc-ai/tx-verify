-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.DrainInOrder
import Lemmas.Step.WarpVoteProgress
import Lemmas.Protocol.ElectCount

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow

/-- Every lane of a reached full-mask scheduler ballot has its actual ballot recorded. -/
theorem SchedulerWarpReached.ballotSuffix {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g pc shuffles votes : Nat} (hg : g < l.threads) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g pc F shuffles votes ends)
    (hit : Nat → Bool) (post : Nat → BitVec 32 → TState)
    (hNext : ∀ lane < 32,
      Next kernel Assumptions.all l (warpLane l g lane) (cur.before lane) (cur.state lane)
        (.vote (2 ^ 32 - 1) (hit lane) (post lane))) :
    ∀ lane < 32, (X.tr (warpLane l g lane)).drop (cur.pos lane) ≠ [] := by
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  intro lane hl
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hPeer (h : Nat) (hs : SameWarp l (thread lane) h) : SameWarp l g h :=
    Step.sameWarp_trans hSame hs
  obtain ⟨word,he,_⟩ := Step.ballot_occurs_of_maximal hMax hBlock hSame.1.2.1
    (cur.pos ∘ laneOf l) (hit ∘ laneOf l) (mask := 2 ^ 32 - 1) (pc := pc) (ordinal := votes)
    (fun h _ => (PTX.electMember_full l h).2)
    (fun h hs => by
      have hEq := Step.warpLane_of_sameWarp (hPeer h hs)
      rw [← hEq]
      apply Or.inl
      let k := laneOf l h
      have hk : k < 32 := Nat.mod_lt _ (by decide)
      have hLen := cur.bounded k hk
      change X.tr (thread k) ≠ []
      intro hNil
      rw [hNil,List.length_nil] at hLen
      have hPos := cur.positive k hk
      omega)
    (fun h hs => by
      let k := laneOf l h
      have hk : k < 32 := Nat.mod_lt _ (by decide)
      have hEq : warpLane l g k = h := Step.warpLane_of_sameWarp (hPeer h hs)
      refine ⟨cur.before k,cur.state k,ends k,post k,?_,?_,?_,(cur.checkpoint k hk).1,?_,?_,?_⟩
      · simpa only [Function.comp_apply,hEq] using cur.bounded k hk
      · change ((X.tr h).take (cur.pos k)).countP isFullWarpVote = votes
        simpa only [hEq] using cur.ordinals.vote k hk
      · simpa only [Function.comp_apply,hEq] using cur.released k hk
      · simpa only [Function.comp_apply,hEq] using cur.recorded k hk
      · simpa only [Function.comp_apply,hEq] using cur.continuation k hk
      · simpa only [Function.comp_apply,hEq] using hNext k hk)
    (fun _ h => Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl
      (noNewRead_appendLanes h))
  have hIndex : laneOf l (thread lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
  have hLen := len_of_get he
  change cur.pos (laneOf l (thread lane)) < (X.tr (thread lane)).length at hLen
  rw [hIndex] at hLen
  exact fun hNil => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp hNil)

end PTX.Kernels.TmlFa4Fwd.Epilogue
