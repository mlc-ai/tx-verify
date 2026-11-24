-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Bound.Base
public import Kernels.InklingRelDecode.Proof.Interface.BoundThreads

@[expose] public section

/-!
# The default partition's common start: rank

The common start is a straight line: the allocation (warp 0, two sub-steps), `bar.sync 0`, the
load of the Tensor Memory base word, `bar.sync 0`, the release of the allocation permit (warp 0)
and the broadcast of the warp index. The rank of a site is the number of sites after it on the
longest path.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bound.DStart
open PTX PTX.Kernels.InklingRelDecode.Proof

noncomputable section

/-- The sites after a site on the longest path. -/
def siteRank : DStart.Site → Nat
  | .alloc => 7 | .allocWr => 6 | .bar0 => 5 | .ld0 => 4 | .bar1 => 3 | .relinq => 2
  | .shfl => 1 | .toProA => 0

/-- The rank of a common-start state. -/
def rank (d : DStart.D) : Nat := siteRank d.site

/-- The largest rank. -/
def top : Nat := 7

theorem rank_le (d : DStart.D) : rank d ≤ top := by
  obtain ⟨s, tm⟩ := d
  cases s <;> simp only [rank, siteRank, top] <;> omega

/-- **Every common-start step lowers the rank by its count.** -/
theorem rank_step {L : Launch} {g : Nat} {d d' : DStart.D} {e : Event}
    (h : DStart.next L g d e = some (some d')) :
    rank d' + (if e.counts then 1 else 0) ≤ rank d := by
  have hc := counts_le e
  obtain ⟨s, tm⟩ := d
  cases s <;> simp only [DStart.next] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [rank, siteRank] <;> omega

end

end PTX.Kernels.InklingRelDecode.Proof.Bound.DStart
