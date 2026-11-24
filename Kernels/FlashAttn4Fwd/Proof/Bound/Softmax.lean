-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bound.Ranks

@[expose] public section

/-! # The softmax warps' rank

A tile of a softmax warp is at most 24 counted events: the score poll, four loads with their
implicit waits, the store of `α` (in a loop trip), the named-barrier arrival, four stores of
probabilities with their two waits, the P-ready arrival, the warp barrier, the election, the
elected lane's second arrival and the statistics poll (`tilePos`, the events left in the tile).
An item is its first tile, `n - 1` loop trips of `32` (`softmaxRank`: `32 (n - t)` for trip
`t`) and the store of `l` with the end of the item's named barrier. A failed poll stays at the
poll. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Bound
open PTX PTX.Proof Softmax

noncomputable section

/-- The counted events left in a tile from a softmax site. -/
def tilePos : Softmax.Site → Nat
  | .statsW 0 => 24 | .statsW _ => 2
  | .sW _ => 23
  | .ld _ 0 => 22 | .ldW _ 0 => 21 | .ld _ 1 => 20 | .ldW _ 1 => 19
  | .ld _ 2 => 18 | .ldW _ 2 => 17 | .ld _ 3 => 16 | .ldW _ 3 => 15
  | .alphaSt => 14 | .gen _ => 13
  | .pst _ 0 => 12 | .pst _ 1 => 11 | .pst _ 2 => 10 | .pwait _ 0 => 9 | .pArr _ => 8
  | .pst _ 3 => 7 | .pwait _ 1 => 6
  | .warpBar _ => 5 | .el _ => 4 | .p2Arr _ => 3
  | .setMaxReg | .bar0 | .lSt | .barEnd | .exit => 0

/-- The softmax warps' rank: the entry, the first tile, a loop trip, the end of an item and the
tail. -/
def softmaxRank (L : Launch) (g : Nat) (d : Softmax.D) : Nat :=
  let Q := perItem L
  let B := Softmax.items L g
  let n := Softmax.trips L
  match d.site with
  | .setMaxReg => Q * B + Q + 63
  | .bar0 => Q * B + Q + 62
  | .statsW 3 => 2
  | .barEnd => 1
  | .exit => 0
  | .lSt => Q * (B - d.i) + 64 + 2
  | .gen 2 => Q * (B - d.i) + 64 + 1
  | s => Q * (B - d.i) + 64 + 3 + tilePos s +
      (if s.inTrip then 32 * (n - d.t) else 32 * (n + 1))

theorem softmaxRank_entry (L : Launch) (g : Nat) {d : Softmax.D} (h : d.site = .setMaxReg) :
    softmaxRank L g d ≤ cap L := by
  simp only [softmaxRank, h]
  exact (Nat.add_assoc _ _ _).le.trans (entry_le (StaticSchedule.count_le _ _ _) (by omega))

set_option maxRecDepth 100000 in
/-- **Every softmax step lowers the rank by its count.** -/
theorem softmaxRank_step {L : Launch} {g : Nat} {d d' : Softmax.D} {e : Event}
    (h : Softmax.next L g d e = some (some d')) :
    softmaxRank L g d' + (if e.counts then 1 else 0) ≤ softmaxRank L g d := by
  have hc := counts_le e
  have hQ : perItem L = 256 * (Softmax.trips L + 1) := rfl
  obtain ⟨s, i, t, sc, m, l⟩ := d
  rcases s with _ | _ | w | lp | ⟨lp, c⟩ | ⟨lp, c⟩ | _ | j | ⟨lp, c⟩ | ⟨lp, k⟩ | lp | lp | lp | lp
    | _ | _ | _
  all_goals (try fin_cases w) <;> (try fin_cases c) <;> (try fin_cases j) <;>
    (try fin_cases k) <;> (try cases lp)
  all_goals simp only [Softmax.next] at h
  all_goals (repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals subst h
  all_goals (try simp only [Softmax.nextItem, Softmax.afterStats, Softmax.afterLoad])
  all_goals rk_close [softmaxRank, tilePos, Site.inTrip] (Softmax.items L g)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Bound
