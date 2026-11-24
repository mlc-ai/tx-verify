-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.Registers
public import Lemmas.Execution.NoBarArrive

@[expose] public section

/-!
# The `.aligned` branch of `Unsafe`

`AlignedMismatch` is checked class by class: the `tcgen05` collectives, the `barrier{.cta}`
instructions, the cluster barrier, `setmaxnreg` and the warp matrix instructions. Two lanes of a
warp diverge at an aligned instruction when they execute their `k`-th event of the class at
different positions or with different operands, and a participant exits when it has executed fewer
events of the class than another participant's `k`-th aligned one.

The cluster class and the matrix class are empty: the kernel has no cluster barrier and no warp
matrix instruction (`NoEvents`). The other three classes need the lanes of a warp to run the
collectives in lockstep, and the participants not to exit early; they are the three fields
`tcAligned`, `barAligned` and `regAligned` of `Protocol`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Barrier divergence -/

set_option maxRecDepth 100000 in
/-- **The kernel has no `bar.arrive`**: its barriers are `bar.sync` and `barrier.sync`. -/
theorem kernel_noBarArrive : kernel.NoBarArrive := by
  unfold Kernel.NoBarArrive
  decide +kernel

/-- Two lanes of a warp at their `k`-th barrier instruction disagree on the barrier or the thread
count (the first clause of `BarMismatch`). -/
def BarLaneMismatch (L : Launch) (X : Execution) : Prop :=
  ∃ g h i j id id' count count' pc pc', SameWarp L g h ∧
    X.IsBarrier (g, i) id count pc ∧ X.IsBarrier (h, j) id' count' pc' ∧
    ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar ∧
    (id ≠ id' ∨ count ≠ count')

/-- **The barrier divergence check holds** when the lanes of a warp agree at each barrier
ordinal: the kernel has no `bar.arrive`, so the second clause is empty. -/
theorem no_barMismatch (hX : Consistent L kernel asms mem0 X) (hl : ¬ BarLaneMismatch L X) :
    ¬ BarMismatch L X := by
  rintro (h | h)
  · exact hl h
  · exact Consistent.not_barArriveMismatch kernel_noBarArrive hX h

/-- **No lane divergence and no early exit in the cluster class.** -/
theorem cluster_aligned (hX : Consistent L kernel asms mem0 X) :
    ¬ AlignedClass.cluster.Divergent L kernel X ∧ ¬ AlignedClass.cluster.Exited L kernel X := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨e, f, pe, pf, ke, kf, -, he, -, hme, -⟩ := h
    obtain ⟨op, rfl⟩ := isCluster_kind hme
    exact no_cluster hX he
  · obtain ⟨e, f, ⟨pc, k⟩, -, he, hm, -⟩ := h
    obtain ⟨op, rfl⟩ := isCluster_kind hm
    exact no_cluster hX he

/-- **No lane divergence and no early exit in the matrix class.** -/
theorem matrix_aligned (hX : Consistent L kernel asms mem0 X) :
    ¬ AlignedClass.matrix.Divergent L kernel X ∧ ¬ AlignedClass.matrix.Exited L kernel X := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨e, f, pe, pf, ke, kf, -, he, -, hme, -⟩ := h
    have := no_matrix_ev hX he
    simp only [AlignedClass.member] at hme
    rw [hme] at this
    cases this
  · obtain ⟨e, f, ev, -, he, hm, -⟩ := h
    have := no_matrix_ev hX he
    simp only [AlignedClass.exitMember, AlignedClass.member] at hm
    rw [hm] at this
    cases this

/-- **No aligned instruction is executed differently by the lanes of a warp or skipped by an
exited participant**, given the three classes the kernel has. -/
theorem no_alignedMismatch (hX : Consistent L kernel asms mem0 X)
    (htc : ¬ AlignedClass.tc.Divergent L kernel X ∧ ¬ AlignedClass.tc.Exited L kernel X)
    (hbar : ¬ AlignedClass.bar.Divergent L kernel X ∧ ¬ AlignedClass.bar.Exited L kernel X)
    (hreg : ¬ AlignedClass.setMaxReg.Divergent L kernel X ∧
      ¬ AlignedClass.setMaxReg.Exited L kernel X) : ¬ AlignedMismatch L kernel X := by
  intro h
  rcases (alignedMismatch_iff L).mp h with (h | h) | (h | h) | (h | h) | (h | h) | (h | h)
  · exact htc.1 h
  · exact htc.2 h
  · exact hbar.1 h
  · exact hbar.2 h
  · exact (cluster_aligned hX).1 h
  · exact (cluster_aligned hX).2 h
  · exact hreg.1 h
  · exact hreg.2 h
  · exact (matrix_aligned hX).1 h
  · exact (matrix_aligned hX).2 h

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
