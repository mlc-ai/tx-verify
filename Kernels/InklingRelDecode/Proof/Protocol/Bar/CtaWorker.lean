-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Protocol.Bar.AlignedKind
import Kernels.InklingRelDecode.Proof.Protocol.Bar.AlignedExit
import Kernels.InklingRelDecode.Proof.Protocol.Bar.One
import Kernels.InklingRelDecode.Proof.Common.Export.BarZero
import Kernels.InklingRelDecode.Proof.Common.Export.BarHalf
import Kernels.InklingRelDecode.Proof.Common.Export.FinalSync
import Kernels.InklingRelDecode.Proof.Common.Export.WorkerBarPc
import Kernels.InklingRelDecode.Proof.Common.Export.RegLedger
import Kernels.InklingRelDecode.Proof.Lib.WorkerBarSchedule
import Lemmas.Flow.NthEv
import Lemmas.Kernel.Frame

@[expose] public section

/-! # The workers' final rendezvous follows the loop's half-CTA rendezvous

A worker lane's barrier-0 events are the full aligned ones, so its final one (`2853`) is its third
and follows four barrier-1 events. The third of them (ordinal 2) was passed, so every lane of the
CTA has a barrier-1 event of ordinal 2; a half-CTA rendezvous of a data lane follows at most two
barrier-1 events, so it is not the last event of its lane. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem one_shape' (hX : Consistent L kernel Assumptions.all m X) (hb : L.block = 256)
    {i pc c md} (he : X.get i = some ⟨pc,.bar 1 c md⟩) : c = none ∧ md = .sync := by
  obtain ⟨hm, r⟩ := Lib.recorded_bar hX hb he
  rcases r with ⟨-, hc, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨hc, hm⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)

private theorem worker_full (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g n pc c md} (hw : 128 ≤ g % L.block) (he : X.get (g,n) = some ⟨pc,.bar 0 c md⟩) :
    c = none ∧ pc ∈ BarRow.fullZeroSites ∧ md = .sync := by
  obtain ⟨hm, r⟩ := Lib.recorded_bar hX hp.block he
  rcases r with ⟨h, -⟩ | ⟨-, hc, hs⟩ | ⟨-, hc, hs⟩
  · exact absurd h (by decide)
  · exact ⟨hc, hs, hm⟩
  · exfalso
    have src := Export.barZeroSources hp hX ⟨g,n⟩ pc c ⟨md,he⟩ (Frame.lt_of_get hX he)
    have halfCnt : BarRow.recCnt L.block 128 = some 128 := by rw [hp.block]; decide
    rw [halfCnt] at hc
    rcases src with h | ⟨-, hwarp, -⟩
    · rw [hc] at h; cases h
    · simp only [Finset.mem_range] at hwarp
      rw [hp.block] at hw hwarp
      omega

private theorem worker_aligned_count (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k} (hw : 128 ≤ g % L.block) :
    ((X.tr g).take k).countP (Execution.isBarId 0) ≤
      ((X.tr g).take k).countP kernel.isAlignedCtaBar := by
  apply List.countP_mono_left
  intro ev mem h0
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take mem)
  obtain ⟨pcx, cx, mx, rfl⟩ := NamedBar.isBarId_form h0
  obtain ⟨hc, f, hmd⟩ := worker_full hp hX hw (show X.get (g,n) = _ from hn)
  subst hc hmd
  exact aligned_of_site f

private theorem workerBar_final (w t : Nat) (h : Lib.finalSync (Lib.workerBar w t) = true) :
    t = 6 := by
  have key : ∀ mid : List Nat, (mid = [2334,2335] ∨ mid = [2346,2419] ∨ mid = [2424,2554]) →
      Lib.finalSync (([12,14,2338] ++ mid ++ [2338,2853]).getD t 0) = true → t = 6 := by
    intro mid hm h
    rcases Nat.lt_or_ge t 7 with lt | ge
    · rcases hm with rfl | rfl | rfl <;> interval_cases t <;> simp_all [Lib.finalSync]
    · rcases hm with rfl | rfl | rfl <;>
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at h <;>
        simp [Lib.finalSync] at h
  unfold Lib.workerBar Lib.workerMid at h
  by_cases h1 : w < 6
  · simp only [h1, ↓reduceIte] at h
    exact key _ (.inl rfl) h
  · by_cases h2 : w = 6
    · simp only [h2, ↓reduceIte] at h
      exact key _ (.inr (.inl rfl)) h
    · simp only [h1, h2, ↓reduceIte] at h
      exact key _ (.inr (.inr rfl)) h

/-- **A worker's final rendezvous follows at least three barrier-1 events.** -/
theorem worker_final_b1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (words : RoleBytes L X) {g k pc cnt md} (hw : 128 ≤ g % L.block)
    (he : X.get (g,k) = some ⟨pc,.bar 0 cnt md⟩)
    (hord : 2 ≤ ((X.tr g).take k).countP (Execution.isBarId 0)) :
    3 ≤ ((X.tr g).take k).countP (Execution.isBarId 1) := by
  have hb : L.block = 256 := hp.block
  obtain ⟨hc, f, hmd⟩ := worker_full hp hX hw he
  subst hc hmd
  have fin : Lib.finalSync pc = true := (Export.final_late hp hX he).mpr hord
  have wp := Export.worker_bar_pc hp hX words he hw
  dsimp only at wp
  have split := bar_count_split (g := g) (k := k) hX hb
  have le2 := aligned_prior_le hp hX he (aligned_of_site f)
  have c0le := worker_aligned_count hp hX (g := g) (k := k) hw
  rw [wp] at fin
  have six := workerBar_final _ _ fin
  omega

/-- **The workers' final rendezvous follows every half-CTA rendezvous of the data lanes of its
CTA.** -/
theorem worker_late (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (words : RoleBytes L X) {g k pc cnt md} (hw : 128 ≤ g % L.block)
    (he : X.get (g,k) = some ⟨pc,.bar 0 cnt md⟩)
    (hord : 2 ≤ ((X.tr g).take k).countP (Execution.isBarId 0)) {g' k' pc'}
    (cta : g' / L.block = g / L.block)
    (he' : X.get (g',k') = some ⟨pc',.bar 0 (some 128) .sync⟩) :
    k' + 1 < (X.tr g').length := by
  have hb : L.block = 256 := hp.block
  have b1 := worker_final_b1 hp hX words hw he hord
  obtain ⟨j, ev, hj, gj, bj, cj⟩ := exists_nthEv (X := X) (p := Execution.isBarId 1)
    (g := g) (k := k) (n := 2) (by omega)
  obtain ⟨pcx, cx, mx, rfl⟩ := NamedBar.isBarId_form bj
  obtain ⟨rfl, rfl⟩ := one_shape' hX hb gj
  have hpassed : (g,j).2 + 1 < (X.tr (g,j).1).length := by
    have : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    show j + 1 < (X.tr g).length
    omega
  obtain ⟨i, pci, hi, hiord⟩ := one_member hp hX (f := (g,j)) gj hpassed (g := g') cta (by
    rintro ⟨jx, pcx', hjx⟩
    have big := Export.exit_barriers hp hX words hjx
    obtain ⟨i, ev2, -, gi, bi, ci⟩ := exists_nthEv (X := X) (p := Execution.isBarId 1)
      (g := g') (k := jx) (n := 2) (by omega)
    obtain ⟨pcy, cy, my, rfl⟩ := NamedBar.isBarId_form bi
    obtain ⟨rfl, rfl⟩ := one_shape' hX hb gi
    exact ⟨i, pcy, gi, ci.trans cj.symm⟩)
  have hc1 := Export.half_publication hp hX he'
  have hil : i < (X.tr g').length := (List.getElem?_eq_some_iff.mp hi).1
  have hik : k' < i := by
    by_contra hge
    have hne : i ≠ k' := by
      rintro rfl
      have h1 : X.get (g', i) = some ⟨pc', .bar 0 (some 128) .sync⟩ := he'
      have h2 : X.get (g', i) = some ⟨pci, .bar 1 none .sync⟩ := hi
      rw [h1] at h2
      simp at h2
    have hsucc := countP_take_succ (p := Execution.isBarId 1) hi (by simp [Execution.isBarId])
    have hmono := countP_take_mono (Execution.isBarId 1) (X.tr g') (show i + 1 ≤ k' by omega)
    simp only at hiord
    omega
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
