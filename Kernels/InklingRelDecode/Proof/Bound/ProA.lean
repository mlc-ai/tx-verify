-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Bound.Base
public import Kernels.InklingRelDecode.Proof.Interface.BoundThreads

@[expose] public section

/-!
# The default partition's prologue rank

The prologue's sites (`ProA.Site`) are declared in the order of the code, and every successor of
`ProA.next` is a later site: the loads and elections are followed by their guarded blocks, and a
guarded block that is skipped (a lane that was not elected, a masked group of query loads) jumps
forward to the next one. The rank of a state is therefore the number of sites declared after its
own up to the last one (`barrier.sync 1`), which every step lowers by at least one.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bound.ProA
open PTX PTX.Kernels.InklingRelDecode.Proof

noncomputable section
set_option maxRecDepth 100000

/-- The position of the last site (`barrier.sync 1`). -/
def top : Nat := ProA.Site.bar18.ctorIdx

/-- The rank of a prologue state: the sites declared after it. -/
def rank (d : ProA.D) : Nat := top - d.site.ctorIdx

theorem ctorIdx_le_top (s : ProA.Site) : s.ctorIdx ≤ top := by
  cases s <;> decide

theorem rank_le (d : ProA.D) : rank d ≤ top := Nat.sub_le _ _

/-- The last site has rank zero. -/
theorem rank_bar18 (dt : ProA.Dat) : rank ⟨.bar18, dt⟩ = 0 := by
  simp only [rank, top, Nat.sub_self]

/-- **Every successor of the prologue is a later site.** -/
theorem next_lt {L : Launch} {g : Nat} {d d' : ProA.D} {e : Event}
    (h : ProA.next L g d e = some (some d')) : d.site.ctorIdx < d'.site.ctorIdx := by
  obtain ⟨s, dt⟩ := d
  cases s <;> simp only [ProA.next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; (try simp only [ProA.qSite])
       (repeat' split) <;> decide)

/-- **Every prologue step lowers the rank by one**, which is at least its count. -/
theorem rank_step {L : Launch} {g : Nat} {d d' : ProA.D} {e : Event}
    (h : ProA.next L g d e = some (some d')) :
    rank d' + (if e.counts then 1 else 0) ≤ rank d := by
  have hc := counts_le e
  have h1 := next_lt h
  have h2 := ctorIdx_le_top d'.site
  unfold rank
  omega

end

end PTX.Kernels.InklingRelDecode.Proof.Bound.ProA
