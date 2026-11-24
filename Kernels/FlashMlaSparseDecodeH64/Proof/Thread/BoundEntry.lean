-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Prologue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Idle
public import Lemmas.Flow.Bound

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
open PTX PTX.Flow

noncomputable section

/-- At most one counted event occurs in one abstract transition. -/
theorem eventCount_le (e : Event) : (if e.counts then 1 else 0) ≤ 1 := by
  split <;> decide

/-- The remaining prologue work, including barrier initialization and the role hand-off. -/
def prologueRank : Proof.Site → Nat
  | .shfl0 => 34
  | .shfl1 => 33
  | .elect0 => 32
  | .elect1 => 31
  | .init j => 30 - j.val
  | .fence => 7
  | .alloc => 6
  | .allocStore => 5
  | .allocRead => 4
  | .relinquish => 3
  | .barrier => 2
  | .handoff _ => 1

theorem prologueRank_step {L : Launch} {g : Nat} {s s' : Proof.Site} {e : Event}
    (hn : Proof.next L g s e = some (some s')) :
    prologueRank s' + (if e.counts then 1 else 0) ≤ prologueRank s := by
  have hc := eventCount_le e
  cases s <;> simp only [Proof.next] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp only [prologueRank]
  all_goals omega

/-- The idle path reads up to two launch words and then joins the CTA barrier. -/
def idleRank : Thread.Site → Nat
  | .loadTopk => 4
  | .loadExtra => 3
  | .sync => 2
  | .exit => 1

theorem idleRank_step {L : Launch} {s s' : Thread.Site} {e : Event}
    (hn : Thread.next L s e = some (some s')) :
    idleRank s' + (if e.counts then 1 else 0) ≤ idleRank s := by
  have hc := eventCount_le e
  cases s <;> simp only [Thread.next] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp only [idleRank]
  all_goals omega

theorem idleRank_le (s : Thread.Site) : idleRank s ≤ 4 := by
  cases s <;> decide

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
