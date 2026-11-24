-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bound.Ranks

@[expose] public section

/-! # The MMA warp's rank

An item of the MMA warp has three parts (`Mma.region`): before the KV loop (the Q and first K
polls, the two S blocks of the first K), `n - 1` loop trips (a V and a K poll, the P-ready
polls, two PV and two S blocks) and after the loop (the last V's PV blocks and the item's last
commits). Each asm block is its election, eight MMAs (spaced by two, so that the second P-ready
poll inside a PV block fits between its sixth and seventh MMA) and its commit election and
commit. The tables (`qWaitPos` … `elCPos`) count down the sites of a part: below `55` after the
loop, below `96` above the trip's band `mmaLoop` in a trip (a trip takes `96`), and above every
trip (`mmaPre`) before the loop. The item advance is guarded by the item's work index, which is
at least the item index when there is a cluster (`le_work`). A failed poll stays at the
poll. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Bound
open PTX PTX.Proof Mma

noncomputable section

/-- The band before the loop: above every trip. -/
abbrev mmaPre (L : Launch) : Nat := 96 * (Mma.trips L + 1) + 55

/-- The band of loop trip `t`. -/
abbrev mmaLoop (L : Launch) (t : Nat) : Nat := 96 * (Mma.trips L - t) + 55

/-- The position of a poll in the item, with its band. -/
def qWaitPos (L : Launch) : Fin 2 → Nat
  | 0 => mmaPre L + 48 | 1 => mmaPre L + 24

def kvWaitPos (L : Launch) (t : Nat) : Fin 4 → Nat
  | 0 => mmaPre L + 47 | 1 => mmaLoop L t + 90 | 2 => mmaLoop L t + 67 | 3 => 50

def pWaitPos (L : Launch) (t : Nat) : Fin 4 → Nat
  | 0 => mmaLoop L t + 89 | 1 => mmaLoop L t + 45 | 2 => 49 | 3 => 25

def p2WaitPos (L : Launch) (t : Nat) : Fin 4 → Nat
  | 0 => mmaLoop L t + 73 | 1 => mmaLoop L t + 30 | 2 => 33 | 3 => 10

/-- The position of a broadcast in the item, with its band. -/
def shflPos (L : Launch) (t : Nat) : Fin 14 → Nat
  | 0 => mmaPre L + 46 | 1 => mmaPre L + 45 | 2 => mmaPre L + 23
  | 3 => mmaLoop L t + 88 | 4 => mmaLoop L t + 87 | 5 => mmaLoop L t + 86
  | 6 => mmaLoop L t + 66 | 7 => mmaLoop L t + 44 | 8 => mmaLoop L t + 43
  | 9 => 48 | 10 => 47 | 11 => 46 | 12 => 24 | 13 => 23

/-- The position of asm block `b`'s election, with its band; its MMA `j` is `2 j + 1`
below it (so the second P-ready poll fits between MMAs `5` and `6`). -/
def elMPos (L : Launch) (t : Nat) : Fin 8 → Nat
  | 0 => mmaPre L + 44 | 1 => mmaPre L + 22 | 2 => mmaLoop L t + 85 | 3 => mmaLoop L t + 65
  | 4 => mmaLoop L t + 42 | 5 => mmaLoop L t + 22 | 6 => 45 | 7 => 22

/-- The position of commit election `c`, with its band; its commit is one below. -/
def elCPos (L : Launch) (t : Nat) : Fin 12 → Nat
  | 0 => mmaPre L + 26 | 1 => mmaPre L + 4 | 2 => mmaPre L + 2
  | 3 => mmaLoop L t + 47 | 4 => mmaLoop L t + 24 | 5 => mmaLoop L t + 4
  | 6 => mmaLoop L t + 2 | 7 => 54 | 8 => 52 | 9 => 27 | 10 => 4 | 11 => 2

/-- The MMA warp's rank: the entry, the item (below `55` after the loop, a trip of `96` in
the loop, above every trip before it) and the tail. -/
def mmaRank (L : Launch) (_g : Nat) (d : Mma.D) : Nat :=
  let Q := perItem L
  let T := totOf L
  let item := Q * (T - d.i) + 64
  match d.site with
  | .setMaxReg => Q * T + Q + 63
  | .alloc => Q * T + Q + 62
  | .allocWrite => Q * T + Q + 61
  | .bar0 => Q * T + Q + 60
  | .ldBase => Q * T + Q + 59
  | .shflQ => Q * T + Q + 58
  | .qWait k => item + qWaitPos L k
  | .kvWait k => item + kvWaitPos L d.t k
  | .pWait k => item + pWaitPos L d.t k
  | .p2Wait k _ => item + p2WaitPos L d.t k
  | .shfl k => item + shflPos L d.t k
  | .elM b => item + elMPos L d.t b
  | .mma b j => item + elMPos L d.t b - 1 - 2 * j.val
  | .elC c => item + elCPos L d.t c
  | .commit c => item + elCPos L d.t c - 1
  | .relinquish => 5
  | .bar1 => 4
  | .arrivePeer => 3
  | .waitDealloc => 2
  | .dealloc => 1
  | .exit => 0

theorem mmaRank_entry (L : Launch) (g : Nat) {d : Mma.D} (h : d.site = .setMaxReg) :
    mmaRank L g d ≤ cap L := by
  simp only [mmaRank, h]
  exact (Nat.add_assoc _ _ _).le.trans (entry_le (le_refl _) (by omega))

/-- The `k`-th work item is at least `k`. -/
theorem le_work {L : Launch} (g : Nat) {k : Nat} (hG : 0 < Mma.clusters L) :
    k ≤ Mma.work L g k := by
  have : k ≤ k * Mma.clusters L := Nat.le_mul_of_pos_right k hG
  unfold Mma.work
  omega

/-- **Every MMA step lowers the rank by its count.** -/
theorem mmaRank_step {L : Launch} {g : Nat} {d d' : Mma.D} {e : Event}
    (hG : 0 < Mma.clusters L) (h : Mma.next L g d e = some (some d')) :
    mmaRank L g d' + (if e.counts then 1 else 0) ≤ mmaRank L g d := by
  have hc := counts_le e
  have hQ : perItem L = 256 * (Mma.trips L + 1) := rfl
  obtain ⟨s, i, t, base, pro⟩ := d
  have hw := le_work g (k := i + 1) hG
  rcases s with _ | _ | _ | _ | _ | _ | k | k | k | ⟨k, lead⟩ | k | k | ⟨k, j⟩ | k | k
    | _ | _ | _ | _ | _ | _
  all_goals (try fin_cases k) <;> (try cases lead)
  all_goals simp only [Mma.next, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte,
    reduceCtorEq] at h
  all_goals (repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals subst h
  all_goals (try simp only [Mma.mmaNext, Mma.isPv, Mma.pvIdx, Mma.skipGrp, Mma.afterGrp,
    Mma.pvGrp, Mma.p2Next, Mma.kvNext, Mma.pNext, Mma.shflNext, Mma.afterCommit, Mma.start,
    Fin.reduceEq, Fin.isValue, decide_false, decide_true, Bool.or_false,
    Bool.or_true, Bool.false_eq_true, false_and, true_and, ↓reduceIte])
  all_goals (try generalize Mma.work L g (i + 1) = w at *)
  all_goals (try generalize Mma.work L g 0 = w at *)
  all_goals (try rw [counts_wait (by assumption)])
  all_goals (try generalize (if e.counts = true then 1 else 0) = cnt at *)
  all_goals ((try split_ifs) <;>
    simp only [mmaRank, qWaitPos, kvWaitPos, pWaitPos, p2WaitPos, shflPos, elMPos, elCPos,
      mmaPre, mmaLoop, Nat.sub_zero, Fin.isValue] <;>
    (try have := RankItems.mul_sub_succ (perItem L) (show i + 1 < totOf L by omega)) <;>
    omega)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Bound
