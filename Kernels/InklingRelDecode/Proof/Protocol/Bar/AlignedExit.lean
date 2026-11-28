-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Protocol.Bar.AlignedKind
import Kernels.InklingRelDecode.Proof.Common.Export.FinalSync
import Kernels.InklingRelDecode.Proof.Common.Export.BarPc
import Kernels.InklingRelDecode.Proof.Common.Export.WorkerBarPc
import Kernels.InklingRelDecode.Proof.Lib.BarSchedule
import Kernels.InklingRelDecode.Proof.Lib.WorkerBarSchedule
import Lemmas.Flow.NthEv

@[expose] public section

/-! # ERR-ALIGNED, early exit at `barrier{.cta}`

The aligned whole-CTA barriers are the full rendezvous at pcs 12, 14, 2850 and 2853. A lane makes
at most two before any of them (its first two, and the final one comes after both), and an exit
follows three (the first two events of a lane are at pcs 12 and 14, and the final one precedes
every exit). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem aligned_le_bar0 (hX : Consistent L kernel Assumptions.all m X) (hb : L.block = 256)
    (g k : Nat) : ((X.tr g).take k).countP kernel.isAlignedCtaBar ≤
      ((X.tr g).take k).countP (Execution.isBarId 0) := by
  apply List.countP_mono_left
  intro ev mem al
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take mem)
  obtain ⟨pc, rfl, -⟩ := aligned_event hX hb (show X.get (g, n) = _ from hn) al
  rfl

/-- **At most two aligned barriers before an aligned barrier.** -/
theorem aligned_prior_le (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {g k ev}
    (he : X.get (g,k) = some ev) (h : kernel.isAlignedCtaBar ev = true) :
    ((X.tr g).take k).countP kernel.isAlignedCtaBar ≤ 2 := by
  have hb : L.block = 256 := hp.block
  by_contra big
  obtain ⟨j, e2, hj, g2, al2, c2⟩ := exists_nthEv (X := X) (p := kernel.isAlignedCtaBar)
    (g := g) (k := k) (n := 2) (by omega)
  obtain ⟨pc2, rfl, -⟩ := aligned_event hX hb g2 al2
  obtain ⟨pc, rfl, -⟩ := aligned_event hX hb he h
  have two : 2 ≤ ((X.tr g).take j).countP (Execution.isBarId 0) :=
    c2 ▸ aligned_le_bar0 hX hb g j
  have fin2 : Lib.finalSync pc2 = true := (Export.final_late hp hX g2).mpr two
  have step := countP_take_succ (p := Execution.isBarId 0) g2 (by simp [Execution.isBarId])
  have mono := countP_take_mono (Execution.isBarId 0) (X.tr g) (show j + 1 ≤ k from hj)
  by_cases fin : Lib.finalSync pc = true
  · have zero := Export.final_first hp hX he fin
    have mem : (⟨pc2, .bar 0 none .sync⟩ : Event) ∈ (X.tr g).take k :=
      List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact g2)
    exact List.countP_eq_zero.mp zero _ mem fin2
  · have lt : ¬ 2 ≤ ((X.tr g).take k).countP (Execution.isBarId 0) :=
      fun h2 => fin ((Export.final_late hp hX he).mpr h2)
    omega

private theorem dataBar_early (p lim t : Nat) (h : t < 2) :
    Lib.dataBar p lim t = 12 ∨ Lib.dataBar p lim t = 14 := by
  interval_cases t <;> simp [Lib.dataBar]

private theorem early_pc (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) {g i pc id cnt md}
    (he : X.get (g,i) = some ⟨pc, .bar id cnt md⟩)
    (lt : ((X.tr g).take i).countP Execution.isBar < 2) : pc = 12 ∨ pc = 14 := by
  have hb : L.block = 256 := hp.block
  have split := bar_count_split (g := g) (k := i) hX hb
  by_cases lg : g % L.block < 128
  · have key := Export.data_bar_pc hp hX hf he lg
    dsimp only at key
    have small : ((X.tr g).take i).countP (Execution.isBarId 0) +
        ((X.tr g).take i).countP (Execution.isBarId 1) -
        ((X.tr g).take i).countP (fun e => e.pc == 2326) < 2 := by omega
    rcases key with h | ⟨-, h2⟩
    · rw [h]
      exact dataBar_early _ _ _ small
    · rcases dataBar_early (Iface.preloadCount Q L (g / L.block))
        (Lib.blocksOf Q L (g / L.block)) _ small with h | h <;> omega
  · have key := Export.worker_bar_pc hp hX words he (by omega)
    dsimp only at key
    generalize hn : ((X.tr g).take i).countP (Execution.isBarId 0) +
      ((X.tr g).take i).countP (Execution.isBarId 1) = n at key
    rw [key]
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · exact .inl (Lib.workerBar_fixed _).1
    · exact .inr (Lib.workerBar_fixed _).2.1

/-- **An exit follows at least three aligned barriers.** -/
theorem exit_aligned_ge (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) {g j pc} (he : X.get (g,j) = some ⟨pc, .exit⟩) :
    3 ≤ (X.tr g).countP kernel.isAlignedCtaBar := by
  have hb : L.block = 256 := hp.block
  obtain ⟨u, p, uj, gu, two⟩ := Export.exit_final_bar hp hX he
  have fin := (Export.final_late hp hX gu).mpr two
  have site : p ∈ BarRow.fullZeroSites := by
    simp only [Lib.finalSync, Bool.or_eq_true, beq_iff_eq] at fin
    rcases fin with rfl | rfl <;> decide
  have alu := aligned_of_site site
  have bars : 2 ≤ ((X.tr g).take u).countP Execution.isBar :=
    two.trans (List.countP_mono_left fun ev _ h => by
      obtain ⟨pc, k⟩ := ev
      cases k <;> simp_all [Execution.isBarId, Execution.isBar])
  obtain ⟨i0, ⟨q0, k0⟩, hi0, g0, b0, c0⟩ := exists_nthEv (X := X) (p := Execution.isBar) (g := g)
    (k := u) (n := 0) (by omega)
  obtain ⟨i1, ⟨q1, k1⟩, hi1, g1, b1, c1⟩ := exists_nthEv (X := X) (p := Execution.isBar) (g := g)
    (k := u) (n := 1) (by omega)
  obtain ⟨a0, n0, d0, rfl⟩ := bar_shape b0
  obtain ⟨a1, n1, d1, rfl⟩ := bar_shape b1
  have al0 := early_aligned hX hb g0 (early_pc hp hX hf words g0 (by omega))
  have al1 := early_aligned hX hb g1 (early_pc hp hX hf words g1 (by omega))
  have o01 : i0 < i1 := by
    by_contra bad
    have := countP_take_mono Execution.isBar (X.tr g) (show i1 ≤ i0 by omega)
    omega
  have o1u : i1 < u := by
    by_contra bad
    have := countP_take_mono Execution.isBar (X.tr g) (show u ≤ i1 by omega)
    omega
  have s0 := countP_take_succ (p := kernel.isAlignedCtaBar) g0 al0
  have m1 := countP_take_mono kernel.isAlignedCtaBar (X.tr g) (show i0 + 1 ≤ i1 by omega)
  have s1 := countP_take_succ (p := kernel.isAlignedCtaBar) g1 al1
  have m2 := countP_take_mono kernel.isAlignedCtaBar (X.tr g) (show i1 + 1 ≤ u by omega)
  have su := countP_take_succ (p := kernel.isAlignedCtaBar) gu alu
  have mend := countP_take_mono kernel.isAlignedCtaBar (X.tr g)
    (show u + 1 ≤ (X.tr g).length from (List.getElem?_eq_some_iff.mp gu).1)
  rw [List.take_length] at mend
  omega

/-- **No participant of an aligned `barrier{.cta}` exits early.** -/
theorem not_exited (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) : ¬ AlignedClass.bar.Exited L kernel X := by
  rintro ⟨e, f, ev, -, he, hm, -, ⟨pcx, hx⟩, hle⟩
  have a := aligned_prior_le hp hX he hm
  have b := exit_aligned_ge hp hX hf words hx
  have hle' : (X.tr f.1).countP kernel.isAlignedCtaBar ≤
      ((X.tr e.1).take e.2).countP kernel.isAlignedCtaBar := hle
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
