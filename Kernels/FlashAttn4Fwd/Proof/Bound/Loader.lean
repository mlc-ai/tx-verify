-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bound.Ranks

@[expose] public section

/-! # The loader's rank

A use of the loader (a K, V or Q tile) is at most seven counted events: the empty-slot poll, the
leader's election and arrival, and two elections with their copies (`usePos`, the events left in
the use). An item is the rank broadcast, the item's first K tile, the two Q halves and the first
V tile (`useOff`), then `n - 1` trips of a K and a V tile (`14 (n - t)` for trip `t`). After the
items the loader drains the six KV slots and the Q slot and the leader arrives once more. A failed
poll stays at the poll. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Bound
open PTX PTX.Proof Loader

noncomputable section

/-- The events of the uses of an item after use `u`, within its part (before the trip loop, or
within a trip). -/
def useOff : UseK → Nat
  | .k0 => 21 | .q0 => 14 | .q1 => 7 | .v0 => 0 | .k => 7 | .v => 0

/-- The uses of a trip. -/
def useInTrip : UseK → Bool
  | .k | .v => true
  | _ => false

/-- The counted events left in its use from a loader site. -/
def usePos : Loader.Site → Nat
  | .wait _ => 7 | .elA _ => 6 | .arrive _ => 5
  | .elC _ 0 => 4 | .copy _ 0 => 3 | .elC _ 1 => 2 | .copy _ 1 => 1
  | _ => 0

/-- The rank of a site of a use in item `i`, trip `t`. -/
def useRank (L : Launch) (g : Nat) (d : Loader.D) (u : UseK) : Nat :=
  perItem L * (Work.T L g - d.i) + 64 + 3 + useOff u + usePos d.site +
    (if useInTrip u then 14 * (Work.n L - d.t) else 14 * (Work.n L + 1))

/-- The loader's rank: the entry, the item's broadcast, its uses, and the drain. -/
def loaderRank (L : Launch) (g : Nat) (d : Loader.D) : Nat :=
  match d.site with
  | .setMaxReg => perItem L * Work.T L g + perItem L + 63
  | .head => perItem L * (Work.T L g - d.i) + 64 + 14 * (Work.n L + 1) + 32
  | .wait u | .elA u | .arrive u | .elC u _ | .copy u _ => useRank L g d u
  | .drain k => 9 - k.val
  | .drainQ => 3 | .elTail => 2 | .arriveTail => 1 | .exit => 0

theorem loaderRank_entry (L : Launch) (g : Nat) {d : Loader.D} (h : d.site = .setMaxReg) :
    loaderRank L g d ≤ cap L := by
  simp only [loaderRank, h]
  exact (Nat.add_assoc _ _ _).le.trans (entry_le (StaticSchedule.count_le _ _ _) (by omega))

/-- **Every loader step lowers the rank by its count.** -/
theorem loaderRank_step {L : Launch} {g : Nat} {d d' : Loader.D} {e : Event}
    (h : Loader.next L g d e = some (some d')) :
    loaderRank L g d' + (if e.counts then 1 else 0) ≤ loaderRank L g d := by
  have hc := counts_le e
  have hQ : perItem L = 256 * (Work.n L + 1) := rfl
  obtain ⟨s, i, t, sl, ph, qp⟩ := d
  rcases s with _ | _ | u | u | u | ⟨u, j⟩ | ⟨u, j⟩ | k | _ | _ | _ | _
  all_goals (try cases u) <;> (try fin_cases j)
  all_goals simp only [Loader.next] at h
  all_goals (repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals subst h
  all_goals (try simp only [Loader.afterCopy, Loader.afterUse, Loader.afterUse.itemEndOf,
    UseK.copies])
  all_goals rk_close [loaderRank, useRank, useOff, usePos, useInTrip] (Work.T L g)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Bound
