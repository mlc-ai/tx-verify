-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bound.Ranks

@[expose] public section

/-! # The store warp's rank

An item of the store warp is twelve counted events: per stage its poll, its two TMA stores and
its commit, then per stage a drain and the arrival freeing it (`storePos`, the events left in
the item). A failed poll stays at the poll. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Bound
open PTX PTX.Proof Store

noncomputable section

/-- The counted events left in the item from a store site. -/
def storePos : Store.Site → Nat
  | .wait st => 12 - 4 * st.val
  | .tma st h => 11 - 4 * st.val - h.val
  | .commit st => 9 - 4 * st.val
  | .drain r => 4 - 2 * r.val
  | .free st => 3 - 2 * st.val
  | .setMaxReg | .exit => 0

/-- The store warp's rank. -/
def storeRank (L : Launch) (g : Nat) (d : Store.D) : Nat :=
  match d.site with
  | .setMaxReg => perItem L * Work.T L g + perItem L + 63
  | .exit => 0
  | s => perItem L * (Work.T L g - d.i) + 64 + storePos s

theorem storeRank_entry (L : Launch) (g : Nat) {d : Store.D} (h : d.site = .setMaxReg) :
    storeRank L g d ≤ cap L := by
  simp only [storeRank, h]
  exact (Nat.add_assoc _ _ _).le.trans (entry_le (StaticSchedule.count_le _ _ _) (by omega))

/-- **Every store step lowers the rank by its count.** -/
theorem storeRank_step {L : Launch} {g : Nat} {d d' : Store.D} {e : Event}
    (h : Store.next L g d e = some (some d')) :
    storeRank L g d' + (if e.counts then 1 else 0) ≤ storeRank L g d := by
  have hc := counts_le e
  obtain ⟨s, i⟩ := d
  cases s <;> simp only [Store.next] at h
  case exit => cases h
  case setMaxReg =>
    simp only [Option.some.injEq] at h
    subst h
    rk_close [storeRank, storePos] (Work.T L g)
  all_goals (split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h)
  all_goals subst h
  all_goals (try simp only [itemEnd])
  all_goals rk_close [storeRank, storePos] (Work.T L g)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Bound
