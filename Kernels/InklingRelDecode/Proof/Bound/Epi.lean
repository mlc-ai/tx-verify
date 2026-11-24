-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Bound.Base
public import Kernels.InklingRelDecode.Proof.Interface.BoundThreads

@[expose] public section

/-!
# The epilogue's rank

The epilogue (warps 0 to 3, after the softmax loop) is a straight line of sites: the poll of
`o_final`, the broadcast, the load of the `O` tile and its wait, the store of `LsePart`, the 64
stores of `OPart`, the barriers and the release of the Tensor Memory. The rank of a state is the
number of sites after its own on the longest path; a store that is skipped, a lane that does not
store, and the release that the other warps skip only shorten the path. A failed poll stays at
the poll and is not counted.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bound.Epi
open PTX PTX.Kernels.InklingRelDecode.Proof

noncomputable section

/-- The sites after a site on the longest path. -/
def siteRank : Epi.Site → Nat
  | .wait => 75 | .shfl => 74 | .ld => 73 | .waitLd => 72 | .stLse => 71
  | .stO k => 70 - k.val
  | .bar1 => 6 | .setMaxInc => 5 | .stTab => 4 | .bar2 => 3 | .bar3 => 2
  | .dealloc => 1 | .exit => 0

/-- The rank of an epilogue state. -/
def rank (d : Epi.D) : Nat := siteRank d.site

/-- The largest rank. -/
def top : Nat := 75

theorem siteRank_le (s : Epi.Site) : siteRank s ≤ top := by
  cases s <;> simp only [siteRank, top] <;> omega

theorem rank_le (d : Epi.D) : rank d ≤ top := siteRank_le d.site

/-- **Every epilogue step lowers the rank by its count.** -/
theorem rank_step {d d' : Epi.D} {e : Event} (h : Epi.next d e = some (some d')) :
    rank d' + (if e.counts then 1 else 0) ≤ rank d := by
  have hc := counts_le e
  obtain ⟨s, pr, o, sk⟩ := d
  cases s <;> simp only [Epi.next] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    (try rw [counts_wait (by assumption)]) <;>
    (simp only [rank, Epi.D.stores, Epi.stNext]; (try split_ifs) <;> simp only [siteRank] <;> omega)

end

end PTX.Kernels.InklingRelDecode.Proof.Bound.Epi
