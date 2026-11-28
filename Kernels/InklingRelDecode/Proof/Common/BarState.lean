-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.EndTime
public import Kernels.InklingRelDecode.Proof.Common.PublicationPrefix
public import Kernels.InklingRelDecode.Proof.Common.WorkerBar
public import Kernels.InklingRelDecode.Proof.Lib.BarClock
import all Kernels.InklingRelDecode.Proof.Common.EndTime
import all Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Softmax.Export.BarCap
import Kernels.InklingRelDecode.Proof.Epilogue.Export.BarCap
import Kernels.InklingRelDecode.Proof.Prologue.Export.BarCap
import Kernels.InklingRelDecode.Proof.Loader.Export.BarCap
import Kernels.InklingRelDecode.Proof.Mma.Export.BarCap

@[expose] public section

/-! # The clock of every state against the generations of barrier 1

At a state of any role of the thread reached with no earlier undefined behaviour, the clock is at
most the clock of the generation numbered by the barrier-1 count (`publication`), strictly
unless the state stands at a rendezvous of the barrier, where it is exactly at it. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem start_clear (s : Startup.Site) : s.pc ∉ Lib.barOneSites := by
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

private theorem start_cap (st : Startup.D) (n : Cls → Nat) :
    Lib.BarCapAt (siteTime (Q := Q) (L := L) (g := g) (.inl st, n)) st.site.pc 0 := by
  unfold Lib.BarCapAt
  have t := (siteTime_startup (Q := Q) (L := L) (g := g) st n).1
  have c0 : Lib.barCap 0 = 281 := by simp [Lib.barCap, Lib.Slots.publish]
  rw [c0]
  exact ⟨fun e => absurd e (start_clear st.site), fun _ =>
    ⟨by omega, fun e => absurd e (start_clear st.site), fun _ => by omega⟩⟩

private theorem dispatch_cap (d : Dispatch.D) (al : Dispatch.Allowed d) (n : Cls → Nat) (w x) :
    Lib.BarCapAt (siteTime (Q := Q) (L := L) (g := g) (.inr ⟨.inl (.dispatch w x), .inl d⟩, n))
      d.site.pc (Dispatch.publicationPhase d) := by
  unfold Lib.BarCapAt
  obtain ⟨st, r⟩ := d
  rcases al with ⟨hr, hm⟩ | ⟨hr, hm⟩ <;> simp only at hr <;> subst hr <;>
    simp [Dispatch.round0, Dispatch.round1] at hm <;>
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [siteTime, siteClock, workerClock, dispatchClock, Dispatch.publicationPhase,
      Dispatch.publicationOffset, Lib.barCap, Lib.Slots.publish, Lib.Slots.reuse,
      Lib.Slots.enter, Lib.Slots.finish, Dispatch.Site.pc, Lib.barOneSites]
  all_goals omega

theorem bar_cap_state {k s} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (hs : stateAt (thread Q L) X g k = some (some s))
    (nub : NoUbBefore X g k) :
    Lib.BarCapAt (siteTime s) ((thread Q L g).pc s) (publication s) := by
  have tbl := reached_table hf hg nub hs
  obtain ⟨rd, rl, rm⟩ := worker_rounds hp hX words hk hs nub
  obtain ⟨s, n⟩ := s
  rcases s with st | ⟨r, d⟩
  · exact start_cap st n
  rcases r with r | r
  swap
  · have c0 : Lib.barCap 0 = 281 := by simp [Lib.barCap, Lib.Slots.publish]
    have : ∀ e : Startup.Entry, Startup.Entry.pc e ∉ Lib.barOneSites := by
      intro e; cases e <;> decide
    unfold Lib.BarCapAt
    simp only [publication, c0]
    exact ⟨fun h => absurd h (this r), fun _ => ⟨by simp [siteTime, siteClock],
      fun h => absurd h (this r), fun _ => by simp [siteTime, siteClock]⟩⟩
  cases r with
  | dispatch w x =>
    rcases d with d | ⟨i, d⟩
    · exact dispatch_cap d (rd w x d n rfl) n w x
    · cases i with
      | loader r0 =>
        obtain rfl := rl w x r0 d n rfl
        have := Loader.Export.bar_cap d
        simpa [publication, workerPublication, siteTime, siteClock, workerClock] using this
      | mma r0 =>
        obtain rfl := rm w x r0 d n rfl
        have := Mma.Export.bar_cap (show Mma.Inv d from tbl.1.1)
        simpa [publication, workerPublication, siteTime, siteClock, workerClock] using this
  | prologue w =>
    rcases d with d | ⟨ent, d | ⟨u, d⟩⟩
    · exact Prologue.Export.bar_cap d
    · exact Softmax.Export.bar_cap tbl.1.1
    · exact Epilogue.Export.bar_cap d

private theorem dispatch_low (d : Dispatch.D) (al : Dispatch.Allowed d) (n : Cls → Nat) (w x) :
    Lib.BarLow (siteTime (Q := Q) (L := L) (g := g) (.inr ⟨.inl (.dispatch w x), .inl d⟩, n))
      (Dispatch.publicationPhase d) := by
  unfold Lib.BarLow
  obtain ⟨st, r⟩ := d
  rcases al with ⟨hr, hm⟩ | ⟨hr, hm⟩ <;> simp only at hr <;> subst hr <;>
    simp [Dispatch.round0, Dispatch.round1] at hm <;>
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [siteTime, siteClock, workerClock, dispatchClock, Dispatch.publicationPhase,
      Dispatch.publicationOffset, Lib.barCap, Lib.Slots.publish, Lib.Slots.reuse,
      Lib.Slots.enter, Lib.Slots.finish, Lib.Slots.frame, Lib.Slots.stride]

/-- **A state's clock is later than the generation of barrier 1 it has passed.** -/
theorem bar_low_state {k s} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (words : RoleBytes L X) (hk : k ≤ (X.tr g).length)
    (hs : stateAt (thread Q L) X g k = some (some s)) (nub : NoUbBefore X g k) :
    Lib.BarLow (siteTime s) (publication s) := by
  obtain ⟨rd, rl, rm⟩ := worker_rounds hp hX words hk hs nub
  obtain ⟨s, n⟩ := s
  rcases s with st | ⟨r, d⟩
  · exact fun h => absurd h (by simp [publication])
  rcases r with r | r
  swap
  · exact fun h => absurd h (by simp [publication])
  cases r with
  | dispatch w x =>
    rcases d with d | ⟨i, d⟩
    · exact dispatch_low d (rd w x d n rfl) n w x
    · cases i with
      | loader r0 =>
        obtain rfl := rl w x r0 d n rfl
        have := Loader.Export.bar_low d
        simpa [publication, workerPublication, siteTime, siteClock, workerClock] using this
      | mma r0 =>
        obtain rfl := rm w x r0 d n rfl
        have := Mma.Export.bar_low d
        simpa [publication, workerPublication, siteTime, siteClock, workerClock] using this
  | prologue w =>
    rcases d with d | ⟨ent, d | ⟨u, d⟩⟩
    · exact Prologue.Export.bar_low d
    · exact Softmax.Export.bar_low d
    · exact Epilogue.Export.bar_low d

private theorem pc_2855 (s : Startup.Site) : s.pc ≠ 2855 := by
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

private theorem loader_2855 (s : Loader.Site) : s.pc ≠ 2855 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem mma_2855 (s : Mma.Site) : s.pc ≠ 2855 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **A state at the exit has seen all four generations of barrier 1.** -/
theorem bar_exit_phase {k s} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (words : RoleBytes L X) (hk : k ≤ (X.tr g).length)
    (hs : stateAt (thread Q L) X g k = some (some s))
    (nub : NoUbBefore X g k) (h : (thread Q L g).pc s = 2855) : 4 ≤ publication s := by
  obtain ⟨rd, rl, rm⟩ := worker_rounds hp hX words hk hs nub
  obtain ⟨s, n⟩ := s
  rcases s with st | ⟨r, d⟩
  · exact absurd h (pc_2855 st.site)
  rcases r with r | r
  swap
  · change Startup.Entry.pc r = 2855 at h
    exact absurd h (by cases r <;> decide)
  cases r with
  | dispatch w x =>
    rcases d with d | ⟨i, d⟩
    · have al := rd w x d n rfl
      obtain ⟨st, r⟩ := d
      rcases al with ⟨hr, hm⟩ | ⟨hr, hm⟩ <;> simp only at hr <;> subst hr <;>
        simp [Dispatch.round0, Dispatch.round1] at hm <;>
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [publication, workerPublication, Dispatch.publicationPhase,
          Dispatch.publicationOffset, Dispatch.Site.pc]
    · cases i with
      | loader r0 => exact absurd h (loader_2855 d.site)
      | mma r0 => exact absurd h (mma_2855 d.site)
  | prologue w =>
    rcases d with d | ⟨ent, d | ⟨u, d⟩⟩
    · have := Prologue.Site.pc_range d.site
      change d.site.pc = 2855 at h
      omega
    · change d.site.pc = 2855 at h
      rcases Softmax.Site.pc_range d.site with r | e
      · omega
      · rw [e] at h
        exact absurd h (by decide)
    · change d.site.pc = 2855 at h
      have : d.site = .exit := by
        generalize d.site = t at h
        cases t <;> first | rfl | (exfalso; revert h; decide) |
          (rename_i j; exfalso; revert h; revert j; decide +kernel)
      simp [publication, dataPublication, softPublication, this, Epilogue.publicationPhase]

end

end PTX.Kernels.InklingRelDecode.Proof
