-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0StateFields

@[expose] public section

/-! # The softmax lane's barrier, pair-barrier and vote ordinals

The number of whole-warpgroup barriers, pair barriers and full-mask reference votes a softmax lane
has issued, as functions of its state, and how a step changes them. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

open PTX PTX.Flow Wg0BarrierTrace

namespace Wg0BarrierCount

/-- Number of softmax warpgroup barriers already issued within the current block. -/
def localOrdinal : Wg0.Site → Nat
  | .sink | .lenOrig | .lenExtra | .bulkWait | .lastStore | .wg0Sync => 0
  | .maskReady | .qkDone | .fenceLoad | .scoreLoad .. | .scoreWait | .fenceBefore
  | .maskRead | .exchStore _ | .pairBar | .peerRead _ | .rowMax | .wg0Sync2 => 1
  | .lseStore0 | .lseBar2 => 3
  | .lseRead | .lseStore | .svDone | .fenceEpilogue => 4
  | .oLoad j | .oWait j | .oStage j _ | .stageFence j | .epiBar j => 4 + j.val
  | .elect j | .tmaStore j => 5 + j.val
  | .commit | .everyone | .exit => 8
  | _ => 2

/-- Expected number of softmax warpgroup barriers at a tracked state. -/
def ordinal (d : Wg0.D) : Nat :=
  match d.site with
  | .sink | .lenOrig | .lenExtra => 0
  | _ => 2 * d.block + localOrdinal d.site

end Wg0BarrierCount

namespace Wg0PeerTrace

/-- Whether this state has passed its current block’s pair barrier. -/
def completedPair : Wg0.Site → Nat
  | .sink | .lenOrig | .lenExtra | .bulkWait | .lastStore | .wg0Sync
  | .maskReady | .qkDone | .fenceLoad | .scoreLoad .. | .scoreWait | .fenceBefore
  | .maskRead | .exchStore _ | .pairBar => 0
  | _ => 1

/-- Expected number of pair barriers at a tracked softmax state. -/
def ordinal (d : Wg0.D) : Nat :=
  match d.site with
  | .sink | .lenOrig | .lenExtra => 0
  | _ => d.block + completedPair d.site

end Wg0PeerTrace

namespace Wg0VoteCount

/-- The sites after the reference vote of this block. -/
def afterVote : Wg0.Site → Bool
  | .pStore _ | .rescaleFence | .rescaleLoad _ | .rescaleWait _ | .rescaleStore _
  | .rescaleWaitSt _ | .rescaleFenceB | .soFence | .soReady | .lseBar | .lseStore0
  | .lseBar2 | .lseRead | .lseStore | .svDone | .fenceEpilogue | .oLoad _ | .oWait _
  | .oStage .. | .stageFence _ | .epiBar _ | .elect _ | .tmaStore _ | .commit
  | .everyone | .exit => true
  | _ => false

/-- The number of completed reference votes at this state. -/
def ordinal (d : Wg0.D) : Nat :=
  match d.site with
  | .sink | .lenOrig | .lenExtra => 0
  | s => d.block + (afterVote s).toNat

end Wg0VoteCount

namespace Wg0Ordinals

instance (s : Wg0.Site) : Decidable (Bar9Site s) := by
  cases s <;> unfold Bar9Site <;> infer_instance

theorem init_zero (P : Params) (L : Launch) (g : Nat) :
    Wg0BarrierCount.ordinal (Wg0.init P L g) = 0 ∧ Wg0PeerTrace.ordinal (Wg0.init P L g) = 0 ∧
      Wg0VoteCount.ordinal (Wg0.init P L g) = 0 := by
  unfold Wg0BarrierCount.ordinal Wg0PeerTrace.ordinal Wg0VoteCount.ordinal Wg0.init Wg0.firstSite
    Wg0.afterSink Wg0.afterLen
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

/-- **The three ordinals after a step**: each grows by one at its own site. -/
theorem step {P : Params} {L : Launch} {g : Nat} {d d' : Wg0.D} {e : Event}
    (hn : Wg0.next P L g d e = some (some d')) :
    Wg0BarrierCount.ordinal d' =
        Wg0BarrierCount.ordinal d + (if Bar9Site d.site then 1 else 0) ∧
      Wg0PeerTrace.ordinal d' = Wg0PeerTrace.ordinal d + (if d.site = .pairBar then 1 else 0) ∧
      Wg0VoteCount.ordinal d' =
        Wg0VoteCount.ordinal d + (if d.site = .rescaleVote then 1 else 0) := by
  cases hd : d.site <;>
    simp only [Wg0.next, Wg0.nextSite, Wg0.writeStep, Wg0.waitStep, hd] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, hpeer, rfl⟩ := Option.map_eq_some_iff.mp hmap
        simp [Wg0BarrierCount.ordinal, Wg0BarrierCount.localOrdinal, Bar9Site,
          Wg0PeerTrace.ordinal, Wg0PeerTrace.completedPair, Wg0VoteCount.ordinal,
          Wg0VoteCount.afterVote, hd, (Wg0.peer_preserves_sub hpeer).1]
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨voted, hv, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨updated, hp, rfl⟩ := Option.map_eq_some_iff.mp hmap
      simp [Wg0BarrierCount.ordinal, Wg0BarrierCount.localOrdinal, Bar9Site,
        Wg0PeerTrace.ordinal, Wg0PeerTrace.completedPair, Wg0VoteCount.ordinal,
        Wg0VoteCount.afterVote, hd, (Wg0.probability_preserves_sub hp).1,
        (Wg0.vote_preserves_sub hv).1]
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [Wg0BarrierCount.ordinal, Wg0BarrierCount.localOrdinal, Bar9Site,
    Wg0PeerTrace.ordinal, Wg0PeerTrace.completedPair, Wg0VoteCount.ordinal,
    Wg0VoteCount.afterVote, Wg0.afterScoreSite, Wg0.afterLen, Wg0.afterSink, Wg0.epiAfterBar,
    Wg0.loadScores, Wg0.loadOutput, Wg0.init]
  all_goals try (split_ifs <;> simp_all)
  all_goals omega

end Wg0Ordinals

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
