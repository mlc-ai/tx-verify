-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Common.UbPrefix
import Kernels.InklingRelDecode.Proof.Common.Staged.Early
public import Kernels.InklingRelDecode.Proof.Common.BarCount0
import Kernels.InklingRelDecode.Proof.Common.Export.TcLag
import Kernels.InklingRelDecode.Proof.Common.Staged.Bar0
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import all Kernels.InklingRelDecode.Proof.Common.EndTime
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section

/-! # The first two rendezvous of barrier 0

A lane of the CTA with fewer barrier-0 events than precede a startup rendezvous is in the
startup, and no later than the rendezvous: the startup's clocks are 2, 4, 10 (first rendezvous), 12,
20 (second). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Sched

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private def startT : Startup.Site → Nat
  | .alloc => 2 | .allocWr => 4 | .bar0 => 10 | .ld0 => 12 | _ => 20

private theorem start_time (st : Startup.D) (n : Cls → Nat) (hs : st.site = .alloc ∨
    st.site = .allocWr ∨ st.site = .bar0 ∨ st.site = .ld0 ∨ st.site = .bar1) :
    siteTime (Q := Q) (L := L) (g := g) (.inl st, n) = startT st.site := by
  obtain ⟨s, tm, x, w⟩ := st
  simp only at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp [siteTime, siteClock, startupClock, startT]

private theorem alive_bound (st : Startup.D) (nn : Cls → Nat) (hP : EarlyPos (Q := Q) (L := L)
    (g := g) (.inl st, nn)) (h1 : nn (.bar 0) ≤ 1) :
    siteTime (Q := Q) (L := L) (g := g) (.inl st, nn) ≤ 10 + 10 * nn (.bar 0) := by
  obtain ⟨site, tm, x, w⟩ := st
  cases site
  case' enter r => cases r
  all_goals simp [EarlyPos, siteTime, siteClock, startupClock] at hP h1 ⊢
  all_goals omega

/-- **The clock of a lane at a startup rendezvous** is 10 at the first, 20 at the second. -/
private theorem start_rendezvous {j pc md} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g, j) = some ⟨pc, .bar 0 none md⟩) (hlt : c0 X g j < 2) :
    timeAt (schedule Q L) X g j = 10 + 10 * c0 X g j := by
  have nu : ∀ f, (⟨pc, .bar 0 none md⟩ : Event).kind ≠ .ub f := by simp
  obtain ⟨st, n, hs, five, hn, ev⟩ := early_at hp hX he nu (by omega)
  have hP : EarlyPos (Q := Q) (L := L) (g := g) (.inl st, n) := by
    rcases early hp hX j (noUb_before hX he) with h0 | ⟨h0, -⟩ | ⟨σ, hσ, hP⟩
    · rw [hs] at h0; cases h0
    · rw [hs] at h0; cases h0
    · rw [hs] at hσ; cases hσ; exact hP
  rw [time_at hs, ← hn]
  rw [start_time _ _ five]
  obtain ⟨s, tm, x, w⟩ := st
  simp only at five
  rcases five with rfl | rfl | rfl | rfl | rfl <;> simp [Startup.Ev] at ev <;>
    simp [EarlyPos] at hP <;> simp [startT, hP]

/-- **A lane with fewer barrier-0 events than precede a startup rendezvous has not exited and is
no later than it.** -/
public theorem bar0_early_lag {j pc md y} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, j) = some ⟨pc, .bar 0 none md⟩) (hlt : c0 X g j < 2)
    (hy : y < L.threads) (nuy : NoUbLane X y)
    (hle : (X.tr y).countP (Execution.isBarId 0) ≤ c0 X g j) :
    (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧
      threadTime (schedule Q L) X y ≤ timeAt (schedule Q L) X g j := by
  rw [start_rendezvous hp hX he hlt]
  have tot : c0 X y (X.tr y).length = (X.tr y).countP (Execution.isBarId 0) := by
    unfold c0; rw [List.take_length]
  have noub (k : Nat) : ∀ j < k, ∀ pc f, X.get (y, j) ≠ some ⟨pc, .ub f⟩ :=
    fun j hj pc f h => nuy.before k j hj _ h f rfl
  refine ⟨fun k pc' hx => ?_, ?_⟩
  · have a := bar0_exit hp hX hx
    have hk : k ≤ (X.tr y).length := (List.getElem?_eq_some_iff.mp hx).1.le
    have b := c0_mono (X := X) (g := y) hk
    omega
  · rw [threadTime_eq_timeAt]
    rcases tc_time_cases hf hy (X.tr y).length with hal | h0 | ⟨hpos, hal, hteq⟩
    · obtain ⟨s, hs⟩ := alive_iff.1 hal
      rw [time_at hs]
      rcases early hp hX (X.tr y).length (noub _) with h0 | ⟨h0, -⟩ | ⟨σ, hσ, hP⟩
      · rw [hs] at h0; cases h0
      · rw [hs] at h0; cases h0
      · rw [hs] at hσ; cases hσ
        obtain ⟨st, nn⟩ := s
        have cnt : nn (.bar 0) = c0 X y (X.tr y).length := by
          have := fcount hs (.bar 0)
          simpa only [cls_bar0] using this
        rcases st with st | r
        · have := alive_bound st nn hP (by omega)
          omega
        · simp only [EarlyPos] at hP
          omega
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨s', hs'⟩ := alive_iff.1 hal
      have hu : (X.tr y).length - 1 < (X.tr y).length := by omega
      obtain ⟨e, ge⟩ : ∃ e, X.get (y, (X.tr y).length - 1) = some e :=
        ⟨_, List.getElem?_eq_getElem hu⟩
      have nu := nuy.kind ge
      have mono := c0_mono (X := X) (g := y) (show (X.tr y).length - 1 ≤ (X.tr y).length by omega)
      have succ := c0_succ (X := X) (g := y) (k := (X.tr y).length - 1) (e := e) ge
      rw [Nat.sub_add_cancel hpos] at succ
      obtain ⟨st, n', hs2, five, hn', ev⟩ := early_at hp hX ge nu (by omega)
      have hP : EarlyPos (Q := Q) (L := L) (g := y) (.inl st, n') := by
        rcases early hp hX ((X.tr y).length - 1) (noub _) with h0 | ⟨h0, -⟩ | ⟨σ, hσ, hP⟩
        · rw [hs2] at h0; cases h0
        · rw [hs2] at h0; cases h0
        · rw [hs2] at hσ; cases hσ; exact hP
      rw [hteq, time_at hs2, start_time _ _ five]
      obtain ⟨site, tm, x, w⟩ := st
      simp only at five
      rcases five with rfl | rfl | rfl | rfl | rfl <;> simp [Startup.Ev] at ev <;>
        simp [EarlyPos] at hP <;> simp [Execution.isBarId, ev, startT] at succ ⊢ <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Export
