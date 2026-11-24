-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0StateFields
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundEntry

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
open PTX PTX.Flow PTX.Proof Wg0

noncomputable section

/-- The order of event sites within one WG0 block and its optional epilogue. -/
def wg0Ordinal : Wg0.Site → Nat
  | .sink => 0
  | .lenOrig => 1
  | .lenExtra => 2
  | .bulkWait => 3
  | .lastStore => 4
  | .wg0Sync => 5
  | .maskReady => 6
  | .qkDone => 7
  | .fenceLoad => 8
  | .scoreLoad _ k => 9 + k.val
  | .scoreWait => 11
  | .fenceBefore => 12
  | .maskRead => 13
  | .exchStore i => 14 + i.val
  | .pairBar => 22
  | .peerRead i => 23 + i.val
  | .rowMax => 31
  | .wg0Sync2 => 32
  | .validFree => 33
  | .maxRead => 34
  | .rescaleVote => 35
  | .pStore k => 36 + k.val
  | .rescaleFence => 40
  | .rescaleLoad j => 41 + 4 * j.val
  | .rescaleWait j => 42 + 4 * j.val
  | .rescaleStore j => 43 + 4 * j.val
  | .rescaleWaitSt j => 44 + 4 * j.val
  | .rescaleFenceB => 57
  | .soFence => 58
  | .soReady => 59
  | .lseBar => 60
  | .lseStore0 => 61
  | .lseBar2 => 62
  | .lseRead => 63
  | .lseStore => 64
  | .svDone => 65
  | .fenceEpilogue => 66
  | .oLoad j => 100 + 15 * j.val
  | .oWait j => 101 + 15 * j.val
  | .oStage j k => 102 + 15 * j.val + k.val
  | .stageFence j => 110 + 15 * j.val
  | .epiBar j => 111 + 15 * j.val
  | .elect j => 112 + 15 * j.val
  | .tmaStore j => 113 + 15 * j.val
  | .commit => 160
  | .everyone => 161
  | .exit => 162

def wg0Block (d : Wg0.D) : Nat :=
  match d.site with
  | .sink | .lenOrig | .lenExtra | .bulkWait | .lastStore => 0
  | _ => d.block

/-- Four positions per instruction cover all vector elements, with room for the epilogue.
Each block costs a separate budget so the loop back-edge decreases the rank. -/
def wg0Rank (P : Params) (L : Launch) (g : Nat) (d : Wg0.D) : Nat :=
  720 * (Wg0.blocksOf P L g - wg0Block d) + (720 - (4 * wg0Ordinal d.site + d.sub))

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
/-- Every counted WG0 event strictly decreases its remaining work. A failed poll keeps it. -/
theorem wg0Rank_step {P : Params} {L : Launch} {g : Nat} {d d' : Wg0.D} {e : Event}
    (hi : Wg0.Inv P L g d) (hn : Wg0.next P L g d e = some (some d')) :
    wg0Rank P L g d' + (if e.counts then 1 else 0) ≤ wg0Rank P L g d := by
  have hc := eventCount_le e
  have hsub := hi.subLt
  cases hd : d.site <;>
    simp only [Wg0.next, Wg0.nextSite, Wg0.writeStep, Wg0.waitStep, hd] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, hpeer, rfl⟩ := Option.map_eq_some_iff.mp hmap
        obtain ⟨hb, hs⟩ := peer_preserves_sub hpeer
        simp only [wg0Rank, wg0Block, wg0Ordinal, hd, hb, hs]
        rw [hd] at hsub
        change d.sub < 1 at hsub
        omega
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, hv, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, hp, rfl⟩ := Option.map_eq_some_iff.mp hmap
      obtain ⟨hb₁, hs₁⟩ := vote_preserves_sub hv
      obtain ⟨hb₂, hs₂⟩ := probability_preserves_sub hp
      simp only [wg0Rank, wg0Block, wg0Ordinal, hd, hb₂, hb₁, hs₂, hs₁]
      rw [hd] at hsub
      change d.sub < 1 at hsub
      omega
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp only [wg0Rank, wg0Block, wg0Ordinal, hd, Wg0.afterScoreSite, Wg0.afterLen,
      Wg0.afterSink, Wg0.epiAfterBar, Wg0.loadScores, Wg0.loadOutput, Wg0.init]
    rw [hd] at hsub
    simp only [Wg0.Site.elems] at hsub
  all_goals (try split_ifs) <;> (try simp only [wg0Block, wg0Ordinal])
  all_goals first
    | omega
    | (rcases e with ⟨epc, kind⟩; simp_all [Event.counts])

/-- The entry follows one of four parameter paths, all within the same row budget. -/
theorem wg0Rank_init (P : Params) (L : Launch) (g : Nat) :
    wg0Rank P L g (Wg0.init P L g) ≤ 720 * Wg0.blocksOf P L g + 720 := by
  unfold wg0Rank wg0Block wg0Ordinal Wg0.init Wg0.firstSite Wg0.afterSink Wg0.afterLen
  split_ifs <;> simp

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
