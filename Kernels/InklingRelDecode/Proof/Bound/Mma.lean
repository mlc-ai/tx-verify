-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Bound.Base
public import Kernels.InklingRelDecode.Proof.Interface.BoundThreads

@[expose] public section

/-!
# The MMA warp's rank

The MMA warp reads `num_iters` (`n`), then runs iterations `i = 0, …, n`: iteration `i` has a QK
half (for `i < n`) and a PV half (for `i ≥ 1`), both a straight line of at most 15 sites, and then
the loop's tail. A half that is skipped (the lane that is not elected, the PV half of iteration 0)
only shortens the iteration, so an iteration lowers the rank by `30` at least. The rank in the
loop is `30 (n + 1 - i)` plus the sites left in the iteration (`pos`); the invariant gives
`i < n` at the QK sites and `i ≤ n` at the PV sites, so the subtraction is exact. The tail's
sites (`finBar` to `setMaxRegInc`) have a rank below 30, so entering them from the last iteration
lowers it. Before the loop the counter read is a 32-bit number (`Raw.word32Of`), so the loop is at
most `2 ^ 32` iterations long. A failed poll stays and is not counted.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bound.Mma
open PTX PTX.Kernels.InklingRelDecode.Proof

noncomputable section

/-- The sites after a loop site within its iteration, on the longest path (the sites of the
tail count down from the tail's rank `fin`). -/
def pos : Mma.Site → Nat
  | .qkBar => 28 | .kvWait => 27 | .qkShfl => 26 | .qkBar2 => 25 | .qkElect => 24
  | .qk j => 23 - j.val | .qkCommit => 15 | .qkSkip => 25
  | .pvBar => 14 | .pWait => 13 | .pvShfl => 12 | .pvBar2 => 11 | .pvElect => 10
  | .pv j => 9 - j.val | .pvCommit1 => 1 | .pvCommit2 => 0 | .pvSkip => 11
  | .finBar => 4 | .finElect => 3 | .finCommit => 2 | .bar1 => 1 | .setMaxRegInc => 0
  | _ => 0

/-- The rank of the first site after the counter is read: a loop of at most `2 ^ 32`
iterations. -/
def readTop : Nat := 30 * 2 ^ 32 + 60

/-- The rank of an MMA state. -/
def rank (d : Mma.D) : Nat :=
  match d.site with
  | .setMaxReg => readTop + 1
  | .ldNum => readTop
  | .bar0 => 30 * (d.n + 1) + 29
  | .finBar => 4 | .finElect => 3 | .finCommit => 2 | .bar1 => 1 | .setMaxRegInc => 0
  | s => 30 * (d.n + 1 - d.i) + pos s

/-- The first state's rank. -/
theorem rank_start (tm : Nat) (pro : Nat → Value) :
    rank ⟨.setMaxReg, 0, 0, tm, pro⟩ = readTop + 1 := rfl

theorem word_lt (v : Value) : (Raw.word32Of v).getD 0 < 2 ^ 32 := by
  cases h : Raw.word32Of v with
  | none => simp
  | some x => simpa using Raw.word32Of_lt h

/-- The rank is bounded in any state with its invariant. -/
theorem rank_le {d : Mma.D} (hI : Mma.Inv d) : rank d ≤ readTop + 1 := by
  have hn := hI.n
  have hqk := hI.qk
  have hpv := hI.pv
  have hpre := hI.pre
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> simp only [Mma.QkSite, Mma.PvSite, Mma.PreSite, forall_const, rank, pos,
    readTop, false_implies] at hn hqk hpv hpre ⊢ <;> omega

/-- **Every MMA step lowers the rank by its count.** -/
theorem rank_step {L : Launch} {g : Nat} {d d' : Mma.D} {e : Event} (hI : Mma.Inv d)
    (hs : d.site ≠ .setMaxRegInc) (h : Mma.next L g d e = some (some d')) :
    rank d' + (if e.counts then 1 else 0) ≤ rank d := by
  have hc := counts_le e
  have hn := hI.n
  have hqk := hI.qk
  have hpv := hI.pv
  have hpre := hI.pre
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> first
    | (exact absurd rfl hs)
    | (simp only [Mma.QkSite, Mma.PvSite, Mma.PreSite, forall_const, false_implies]
        at hqk hpv hpre
       simp only [Mma.next, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext, Mma.start] at h
       (repeat' split at h)
       all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
       all_goals (try subst h)
       all_goals (try rw [counts_wait (by assumption)])
       all_goals (try have := word_lt ‹Value›)
       all_goals (try simp only [rank, pos, readTop] at *)
       all_goals (try split_ifs)
       all_goals omega)

end

end PTX.Kernels.InklingRelDecode.Proof.Bound.Mma
