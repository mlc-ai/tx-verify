-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Bound.Base
public import Kernels.InklingRelDecode.Proof.Interface.BoundThreads

@[expose] public section

/-!
# The softmax region's rank

The softmax region (`Sm.Site`: 157 sites in all) first loads the bias words of block 0 (the 64
`pre` sites), then runs the loop `i = 0, …, num_iters - 1` (`D.e.r26` is `num_iters`). An iteration
is, from its first site, the 64 loads of the next block's bias words (`nxt`, skipped where masked),
the `s_ready` poll, the broadcast, the S tile's load and wait, the score stage (the shuffles, the
`o_done` poll of every iteration after the first, the shuffles of the minimum of `alpha`, the row
sum's shared store and the O rescale, which the lazy rescale skips), the P store and the arrival on
`p_ready`. The rank of a state is `91 (num_iters - i)` plus the sites left
in the iteration on the longest path (`pos`, at most 90 after the loop's first site `nxt 0`); the
state `i + 1` after an iteration is one block of 91 lower. The first block's setup sites (`pre`,
the barrier and `setmaxnreg`) rank above every site of the loop at the same `i`. The loop's
invariant gives `i < num_iters` from the S tile's poll on and at the loop's own bias loads and
`i ≤ num_iters` everywhere, so the subtraction is exact where the rank has to fall; and
`num_iters < 2 ^ 31` (`Ent.Ok`) bounds the rank.

The rank is defined by the site's constructor and the loop counters only: it does not depend on
which sites have step lemmas. A failed poll stays and is not counted.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bound.Sm
open PTX PTX.Kernels.InklingRelDecode.Proof

noncomputable section

/-- The sites after a site on the longest path of its iteration (the first block's setup sites
count above the loop's). -/
def pos : Sm.Site → Nat
  | .arrive => 0 | .bar21 => 1 | .tmemWait => 2 | .tmemSt => 3 | .bar20 => 4
  | .waitStO => 5 | .stO => 6 | .bar24 => 7 | .waitLdO => 8 | .ldO => 9 | .shfl12 => 10
  | .shfl11 => 11 | .ldL => 12 | .bar23 => 13 | .store10 => 14 | .shfl10 => 15
  | .shfl9 => 16 | .shfl8 => 17 | .shfl7 => 18 | .bar22 => 19 | .waitO => 20
  | .shfl6 => 21 | .shfl5 => 22 | .waitLd => 23 | .ldS => 24 | .shfl4 => 25 | .waitS => 26
  | .nxt j => 90 - j.val
  | .pre j => 154 - j.val
  | .bar0 => 155 | .setMaxReg => 156

/-- The rank of a softmax state. -/
def rank (d : Sm.D) : Nat := 91 * (d.e.r26 - d.i) + pos d.site

/-- The largest rank. -/
def top : Nat := 91 * 2 ^ 31 + 156

theorem r26_lt {e : Sm.Ent} (h : e.Ok) : e.r26 < 2 ^ 31 := by
  have h1 := h.r26
  split_ifs at h1 <;> omega

theorem pos_le (s : Sm.Site) : pos s ≤ 156 := by
  cases s <;> simp only [pos] <;> omega

/-- The rank is bounded in any state with its invariant. -/
theorem rank_le {L : Launch} {g : Nat} {d : Sm.D} (hI : Sm.Inv L g d) : rank d ≤ top := by
  have := r26_lt hI.ok
  have := pos_le d.site
  unfold rank top
  omega

/-- The edge into the P store succeeds for the barrier of the P store, with the updated numbers. -/
theorem toBar20_eq_some {d d' : Sm.D} :
    Sm.toBar20 d = some (some d') ↔ (d.updOk = true ∧ d' = { d.upd with site := .bar20 }) := by
  unfold Sm.toBar20
  split
  · simp [eq_comm, *]
  · simp [*]

/-- **Every softmax step lowers the rank by its count.** -/
theorem rank_step {L : Launch} {g : Nat} {d d' : Sm.D} {e : Event} (hI : Sm.Inv L g d)
    (h : Sm.next L g d e = some (some d')) :
    rank d' + (if e.counts then 1 else 0) ≤ rank d := by
  have hc := counts_le e
  have hi := hI.i
  have hlate := hI.late
  have hnxt := hI.cwNxt
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> first
    | (simp only [Sm.LateSite, forall_const, false_implies] at hlate
       (try have hn1 := hnxt _ rfl)
       simp only [Sm.next, Sm.afterSetup, Sm.afterArrive, Sm.D.afterSum, Sm.D.afterMax,
         Sm.D.afterMaxT] at h
       (repeat' split at h)
       all_goals (try simp only [toBar20_eq_some] at h)
       all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
       all_goals (try obtain ⟨-, rfl⟩ := h)
       all_goals (try rw [counts_wait (by assumption)])
       all_goals (try simp only [rank, pos, Sm.D.upd] at *)
       all_goals (try split_ifs)
       all_goals omega)

end

end PTX.Kernels.InklingRelDecode.Proof.Bound.Sm
