-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveOperands
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteBranch

@[expose] public section

/-! # Tensor Memory collective ranks inside the softmax role -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0TcRank

open PTX PTX.Flow TcCollectiveSites

/-- The first block never rescales. Each later true vote contributes one rescale. -/
def priorRescales (vote : Nat → Bool) : Nat → Nat
  | 0 => 0
  | i + 1 => priorRescales vote i + ((i != 0) && vote i).toNat

/-- Sites with the full optional rescale behind them. -/
def pastRescale : Wg0.Site → Bool
  | .soFence | .soReady | .lseBar | .lseStore0 | .lseBar2 | .lseRead | .lseStore
  | .svDone | .fenceEpilogue | .oLoad _ | .oWait _ | .oStage .. | .stageFence _
  | .epiBar _ | .elect _ | .tmaStore _ | .commit | .everyone | .exit => true
  | _ => false

/-- Each sparse block issues three score collectives and optionally sixteen rescale collectives.
The output load and wait pairs follow the last block. -/
def blockOffset (rescale : Bool) : Wg0.Site → Nat
  | .sink | .lenOrig | .lenExtra | .bulkWait | .lastStore | .wg0Sync
  | .maskReady | .qkDone | .fenceLoad => 0
  | .scoreLoad _ k => k.val
  | .scoreWait => 2
  | .rescaleLoad j => 3 + 4 * j.val
  | .rescaleWait j => 4 + 4 * j.val
  | .rescaleStore j => 5 + 4 * j.val
  | .rescaleWaitSt j => 6 + 4 * j.val
  | .rescaleFenceB => 19
  | .oLoad j => 3 + 16 * rescale.toNat + 2 * j.val
  | .oWait j => 4 + 16 * rescale.toNat + 2 * j.val
  | .oStage j _ | .stageFence j | .epiBar j | .elect j | .tmaStore j =>
    5 + 16 * rescale.toNat + 2 * j.val
  | .commit | .everyone | .exit => 11 + 16 * rescale.toNat
  | s => if pastRescale s then 3 + 16 * rescale.toNat else 3

/-- The rank of a WG0 site, excluding its preceding allocation and relinquishment on warp zero. -/
def rank (vote : Nat → Bool) (d : Wg0.D) : Nat :=
  match d.site with
  | .sink | .lenOrig | .lenExtra => 0
  | s => 3 * d.block + 16 * priorRescales vote d.block + blockOffset d.rescale s

/-- A local state remembers the observed decision and keeps its chosen branch through the block. -/
def Scheduled (vote : Nat → Bool) (d : Wg0.D) : Prop :=
  (Wg0VoteCount.afterVote d.site = true → d.voteTaken = vote d.block) ∧
  (d.site.inRescale = true ∨ pastRescale d.site = true →
    d.rescale = ((d.block != 0) && vote d.block))

private theorem peer_preserves_block {L : Launch} {d d' : Wg0.D} {v : Value}
    (h : Wg0.withPeerMax L d v = some d') : d'.block = d.block := by
  unfold Wg0.withPeerMax at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  rfl

private theorem probability_fields {L : Launch} {g : Nat} {d d' : Wg0.D}
    (h : Wg0.probabilityUpdate L g d = some d') :
    d' = { d with sumUpd := d'.sumUpd, lh := d'.lh, pw := d'.pw } := by
  unfold Wg0.probabilityUpdate at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  rfl

/-- A step preserves the block's schedule and advances its rank for a data event. -/
theorem step {P : Params} {L : Launch} {g : Nat} {vote : Nat → Bool}
    {d d' : Wg0.D} {e : Event} (h : Scheduled vote d)
    (ha : d.site.inRescale = true → d.rescale = true)
    (hn : Wg0.next P L g d e = some (some d'))
    (hVote : ∀ m mask p result, e.kind = .voteMode m mask p result → result = vote d.block) :
    Scheduled vote d' ∧ rank vote d' = rank vote d + (dataOperands d.site).isSome.toNat := by
  cases hd : d.site <;>
    simp only [Wg0.next, Wg0.nextSite, Wg0.writeStep, Wg0.waitStep, hd] at hn
  case scoreLoad a k =>
    fin_cases k
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals simp [Scheduled, rank, hd, Wg0VoteCount.afterVote, Wg0.Site.inRescale,
      dataOperands, blockOffset, pastRescale, Wg0.loadScores, Wg0.afterScoreSite]
    all_goals split_ifs <;> rfl
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, hpeer, rfl⟩ := Option.map_eq_some_iff.mp hmap
        simp [Scheduled, rank, blockOffset, pastRescale, Wg0VoteCount.afterVote,
          dataOperands, Wg0.Site.inRescale, hd, peer_preserves_block hpeer]
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · rename_i m mask p result he
      obtain ⟨voted, hv, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨updated, hp, rfl⟩ := Option.map_eq_some_iff.mp hmap
      have hv' := Wg0.afterReferenceVote_fields hv
      have hp' := probability_fields hp
      have hr := hVote m mask p result he
      rw [hp', hv']
      simp [Scheduled, rank, blockOffset, pastRescale, Wg0VoteCount.afterVote,
        dataOperands, Wg0.Site.inRescale, hd, hr]
    · cases hn
  case rescaleFenceB =>
    have hReady : d.site.inRescale = true := by rw [hd]; rfl
    have hFlag : ((d.block != 0) && vote d.block) = true :=
      (h.2 (.inl hReady)).symm.trans (ha hReady)
    have hRescale := ha hReady
    have hTaken := h.1 (by rw [hd]; rfl)
    split at hn
    · cases hn
      simp [Scheduled, rank, blockOffset, pastRescale, Wg0VoteCount.afterVote, dataOperands,
        Wg0.Site.inRescale, hd, hFlag, hRescale, hTaken]
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [Scheduled, rank, blockOffset, pastRescale, Wg0VoteCount.afterVote,
    dataOperands, Wg0.Site.inRescale, Wg0.afterLen, Wg0.afterSink,
    Wg0.epiAfterBar, Wg0.loadOutput, Wg0.init, Wg0.wantsRescale, priorRescales]
  all_goals try (split_ifs <;> simp_all)
  all_goals omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0TcRank
