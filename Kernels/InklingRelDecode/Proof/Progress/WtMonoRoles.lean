-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WtMonoSm

@[expose] public section

/-!
# The virtual time rises along the steps of the other roles

The loader, the MMA warp, the epilogue, the common start, the worker's own sites and the idle role.
A counted step raises the time; a failed poll (not counted) stays where it is.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000
open Classical

/-- **Every counted step of the loader raises the time** (not the last event, which returns to the
dispatch loop). -/
theorem loaderT_lt {L : Launch} {g : Nat} {d d' : Loader.D} {e : Event}
    (hI : Loader.Inv L g d) (hs : d.site ≠ .setMaxInc)
    (h : Loader.next L g d e = some (some d')) (hc : e.counts = true) :
    loaderT d < loaderT d' := by
  have hb : d.site.inLoop = true → d.i < 2 ^ 33 := fun hl => by
    have h1 := (hI.loop hl).2
    have h2 := Raw.word32Of_lt (hI.bits hl).2
    omega
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> first
    | (exact absurd rfl hs)
    | (simp only [Loader.Site.inLoop, Bool.false_eq_true, false_implies, forall_const] at hb
       simp only [Loader.next, Loader.afterIter, Loader.readI, Loader.readN] at h
       (repeat' split at h)
       all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
       all_goals (try subst h)
       all_goals (try (rw [Bound.counts_wait (by assumption)] at hc; contradiction))
       all_goals (try simp only [loaderT, Bound.Loader.pos] at *)
       all_goals wt_omega)

/-- **Every counted step of the MMA warp raises the time** (not the last event, which returns to the
dispatch loop). -/
theorem mmaT_lt {L : Launch} {g : Nat} {d d' : Mma.D} {e : Event}
    (hI : Mma.Inv d) (hs : d.site ≠ .setMaxRegInc)
    (h : Mma.next L g d e = some (some d')) (hc : e.counts = true) : mmaT d < mmaT d' := by
  have hn := hI.n
  have hqk := hI.qk
  have hpv := hI.pv
  have hpre := hI.pre
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> first
    | (exact absurd rfl hs)
    | (simp only [Mma.QkSite, Mma.PvSite, Mma.PreSite, forall_const, false_implies] at hqk hpv hpre
       simp only [Mma.next, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext, Mma.start] at h
       (repeat' split at h)
       all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
       all_goals (try subst h)
       all_goals (try (rw [Bound.counts_wait (by assumption)] at hc; contradiction))
       all_goals (try simp only [mmaT, Bound.Mma.pos] at *)
       all_goals wt_omega)

/-- **Every counted step of the epilogue raises the time.** -/
theorem epiT_lt {d d' : Epi.D} {e : Event} (h : Epi.next d e = some (some d'))
    (hc : e.counts = true) : epiT d < epiT d' := by
  have h1 := Bound.Epi.rank_step h
  have h2 := Bound.Epi.rank_le d
  have h3 := Bound.Epi.rank_le d'
  simp only [hc, ↓reduceIte] at h1
  unfold epiT
  unfold Bound.Epi.rank at h1 h2 h3
  unfold Bound.Epi.top at h2 h3
  wt_omega

/-- **Every counted step of the common start raises the time.** -/
theorem dstartT_lt {L : Launch} {g : Nat} {d d' : DStart.D} {e : Event}
    (h : DStart.next L g d e = some (some d')) (hc : e.counts = true) :
    dstartT d < dstartT d' := by
  have h1 := Bound.DStart.rank_step h
  simp only [hc, ↓reduceIte] at h1
  obtain ⟨s, tm⟩ := d
  obtain ⟨s', tm'⟩ := d'
  unfold Bound.DStart.rank at h1
  cases s <;> cases s' <;> simp_all [Bound.DStart.siteRank, dstartT]

/-- **Every time of the common start is at most 26**, below the prologue's. -/
theorem dstartT_le (d : DStart.D) : dstartT d ≤ 26 := by
  obtain ⟨s, tm⟩ := d
  cases s <;> simp [dstartT]

/-- **Every step of the worker's own sites (not the dispatch, not the second barrier of the
bad-role path) raises the time.** The bad-role path (`bad0`, `bad1`) returns to the loop's head
in the same round, so no time rises along it: it is excluded by the role byte protocol. -/
theorem workerT_lt {L : Launch} {g : Nat} {d d' : Worker.D} {e : Event}
    (hs : d.site ≠ .ldRole) (hb : d.site ≠ .bad1) (h : Worker.next L g d e = some (some d')) :
    workerT d < workerT d' := by
  obtain ⟨s, P⟩ := d
  cases s <;> first
    | (exact absurd rfl hs)
    | (exact absurd rfl hb)
    | (simp only [Worker.next] at h
       (repeat' split at h)
       all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
       all_goals (try subst h)
       all_goals (try simp only [workerT] at *)
       all_goals (try split_ifs)
       all_goals wt_omega)

/-- **Every step of the idle role raises the time.** -/
theorem idleT_lt {d d' : Worker.Idle.D} {e : Event} (h : Worker.Idle.next d e = some (some d')) :
    idleT d < idleT d' := by
  obtain ⟨s, P⟩ := d
  cases s <;> simp only [Worker.Idle.next, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [idleT] <;> wt_omega

end

end PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
