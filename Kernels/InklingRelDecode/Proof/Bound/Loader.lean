-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Bound.Base
public import Kernels.InklingRelDecode.Proof.Interface.BoundThreads

@[expose] public section

/-!
# The loader warp's rank

The loader reads `(num_pre, num_iters)`, waits at the named barrier, and then runs the iteration
loop `i = num_pre, …, num_iters - 1` (`Loader.Site.inLoop`). An iteration visits at most 21 sites
(`pos`: the `kv_empty` poll, the warp barrier, the arrival, the block-table loads, the elections
and the eight tensor copies), so while the loop is running the rank is `22 (n - i)` plus the
remaining sites of the iteration; the last site of an iteration either goes to the next
iteration (`i + 1`, one block of 22 lower) or, after the last, to the exit barrier. The counter
register is a 32-bit word and its increment wraps around, so the iterations left are `dist i n`,
the distance from `i` to `n` modulo `2 ^ 32`; the loop's invariant gives `i % 2 ^ 32 ≠ n` at the
loop's sites, so it drops by one per iteration. Before the loop the rank is a constant: the loop
that follows is at most `2 ^ 32` iterations long. A failed poll stays and is not counted.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bound.Loader
open PTX PTX.Kernels.InklingRelDecode.Proof

noncomputable section

/-- The sites after a loop site within its iteration, on the longest path. -/
def pos : Loader.Site → Nat
  | .wait => 21 | .wb0 => 20 | .arrive => 19 | .ldb0 => 18 | .wb1 => 17 | .el0 => 16
  | .cp0a => 15 | .cp0b => 14 | .wb2 => 13 | .el1 => 12 | .cp1a => 11 | .cp1b => 10
  | .ldb1 => 9 | .wb3 => 8 | .el2 => 7 | .cp2a => 6 | .cp2b => 5 | .wb4 => 4 | .el3 => 3
  | .cp3a => 2 | .cp3b => 1
  | _ => 0

/-- The iterations left from counter `i` to `num_iters` `n`, as 32-bit words: the loop's
increment wraps around, and it stops when the counter is `n`. -/
def dist (i n : Nat) : Nat := (n + 2 ^ 32 - i % 2 ^ 32) % 2 ^ 32

/-- The rank of the first site after the counters are read: the loop of at most `2 ^ 32`
iterations. -/
def readTop : Nat := 22 * 2 ^ 32 + 24

/-- The rank of a loader state. -/
def rank (d : Loader.D) : Nat :=
  match d.site with
  | .setMaxDec => readTop + 2
  | .ld0 => readTop + 1
  | .ld1 => readTop
  | .bar0 => 22 * dist d.i d.n + 23
  | .bar1 => 1
  | .setMaxInc => 0
  | s => 22 * dist d.i d.n + pos s

/-- The first state's rank. -/
theorem rank_start (L : Launch) (g : Nat) (P : Loader.Pro) :
    rank (Loader.D.start L g P) = readTop + 2 := rfl

theorem dist_lt (i n : Nat) : dist i n < 2 ^ 32 := Nat.mod_lt _ (by norm_num)

/-- The rank is bounded in every state. -/
theorem rank_le (d : Loader.D) : rank d ≤ readTop + 2 := by
  have hd := dist_lt d.i d.n
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> simp only [rank, pos, readTop] at hd ⊢ <;> omega

/-- The getD of a word is below `2 ^ 32`. -/
theorem getD_lt (v : Value) : (Raw.word32Of v).getD 0 < 2 ^ 32 := by
  cases h : Raw.word32Of v with
  | none => simp
  | some x => exact Raw.word32Of_lt h

/-- **Every loader step lowers the rank by its count.** -/
theorem rank_step {L : Launch} {g : Nat} {d d' : Loader.D} {e : Event}
    (hI : Loader.Inv L g d) (hs : d.site ≠ .setMaxInc)
    (h : Loader.next L g d e = some (some d')) :
    rank d' + (if e.counts then 1 else 0) ≤ rank d := by
  have hc := counts_le e
  have hloop := hI.loop
  have hbits := hI.bits
  have hwi := hI.wi
  have hwn := hI.wn
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  have hil : s.inLoop = true → n < 2 ^ 32 := fun hl => Raw.word32Of_lt (hbits hl).2
  have hb0 : s = .bar0 → i < 2 ^ 32 ∧ n < 2 ^ 32 := fun hb => by
    subst hb
    have h1 := hwi (.inr rfl)
    have h2 := hwn rfl
    simp only at h1 h2
    exact ⟨by rw [← h1]; exact getD_lt _, by rw [← h2]; exact getD_lt _⟩
  cases s <;> first
    | (exact absurd rfl hs)
    | (simp only [Loader.Site.inLoop, Bool.false_eq_true, false_implies,
         forall_const] at hloop hil hb0
       simp only [Loader.next, Loader.afterIter, Loader.readI, Loader.readN] at h
       (repeat' split at h)
       all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
       all_goals (try subst h)
       all_goals (try rw [counts_wait (by assumption)])
       all_goals (try simp only [rank, pos, readTop, dist] at *)
       all_goals (try split_ifs)
       all_goals omega)

end

end PTX.Kernels.InklingRelDecode.Proof.Bound.Loader
