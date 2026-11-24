-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Bound.Base
public import Kernels.InklingRelDecode.Proof.Interface.BoundThreads

@[expose] public section

/-!
# The workers' prologue, dispatch loop and idle role: rank

A worker thread (warps 4 to 7) runs its prologue (`bar.sync 0`, the load of the Tensor Memory
base, `bar.sync 0`, the broadcast of the warp index) to the head of the dispatch loop, then goes
around the loop: `setmaxnreg.inc`, `barrier.sync 1`, the load of the role byte, and the role the
byte names. A round of the loop is not counted down by the machine's states: the role ends at the
loop's head again. The rank of a state of the loop's own sites counts down to the load of the role
byte (`siteRank`), and the load is the one event at which the composed machine's rank rises
(`Bound/WComp.lean`: the budget of a dispatch). The two barriers of the branch for a role byte above
3 (`bad0`, `bad1`) are ranked as a role of two sites above the loop's head.

The idle role is a straight line of four sites (`Idle.siteRank`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bound.Worker
open PTX PTX.Kernels.InklingRelDecode.Proof

noncomputable section

/-- The sites after a site of the worker's own on the longest path, to the load of the role
byte. -/
def siteRank : Worker.Site → Nat
  | .bar0 => 7 | .ld0 => 6 | .bar1 => 5 | .shfl => 4 | .loop => 3 | .bar2 => 2
  | .ldRole => 1 | .toIdle => 0 | .toLoader => 0 | .toMma => 0 | .toExit => 0
  | .bad0 => 5 | .bad1 => 4

/-- The rank of a worker state. -/
def rank (d : Worker.D) : Nat := siteRank d.site

/-- **Every step of the worker's own sites that is not the dispatch lowers the rank by its
count.** -/
theorem rank_step {L : Launch} {g : Nat} {d d' : Worker.D} {e : Event}
    (hs : d.site ≠ .ldRole) (h : Worker.next L g d e = some (some d')) :
    rank d' + (if e.counts then 1 else 0) ≤ rank d := by
  have hc := counts_le e
  obtain ⟨s, P⟩ := d
  cases s <;> first
    | (exact absurd rfl hs)
    | (simp only [Worker.next] at h; (repeat' split at h)
       all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
       all_goals (subst h; simp only [rank, siteRank]; omega))

/-- The sites after an idle site. -/
def idleRank : Worker.Idle.Site → Nat
  | .dec => 3 | .bar0 => 2 | .bar1 => 1 | .inc => 0

/-- **Every step of the idle role lowers the rank by its count.** -/
theorem idle_step {d d' : Worker.Idle.D} {e : Event}
    (h : Worker.Idle.next d e = some (some d')) :
    idleRank d'.site + (if e.counts then 1 else 0) ≤ idleRank d.site := by
  have hc := counts_le e
  obtain ⟨s, P⟩ := d
  cases s <;> simp only [Worker.Idle.next, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> simp only [idleRank] <;> omega

end

end PTX.Kernels.InklingRelDecode.Proof.Bound.Worker
