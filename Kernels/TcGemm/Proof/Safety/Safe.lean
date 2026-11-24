-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Safety.Tc
public import Kernels.TcGemm.Proof.Safety.Bar
public import Lemmas.Flow.WarpUniform

@[expose] public section

/-! # No consistent execution is unsafe

Every event is of the Tensor Core/mbarrier/bulk class (`Wit.tcBulk`), so
`Execution.TcBulk.not_unsafe` leaves the branches the kernel's own events decide: no undefined
behaviour (`u_nil`), every access allocated and every conflict ordered (`Safety/Memory.lean`), the
barriers matched and fault-free (`Safety/Bar.lean`), the mbarrier, copy and collective branches
and the lifetime of every shared-memory use (`Safety/Objects.lean`), the loaded words' sources,
the accesses' lifetimes and the MMA (`Safety/Tc.lean`), and the allocator's resources and
releases and the Tensor Memory conflicts (`Safety/Tmem.lean`). -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow
noncomputable section
variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

/-- No event is a cluster barrier, register request or warp matrix instruction. -/
theorem not_member_other (hW : Wit A B D L.sharedBase X P m u) {c : AlignedClass}
    (hc : c ≠ .tc ∧ c ≠ .bar) {e : EvId} {ev : Event} (he : X.get e = some ev) :
    c.member ev = false := by
  obtain ⟨pc, k⟩ := ev
  have hk := hW.tcBulk _ _ _ he
  cases c <;> simp at hc <;> cases k <;>
    simp_all [Kind.isTcBulk, AlignedClass.member, isCluster, SetMaxNReg.isRequest, isMatrix]

/-- **No aligned instruction diverges or is left by an exit**: the warp-collective `tcgen05`
events and the barriers by `Safety/Tmem.lean` and `Safety/Bar.lean`, and no other aligned class
occurs. -/
theorem no_alignedMismatch (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
    (hW : Wit A B D L.sharedBase X P m u) : ¬ AlignedMismatch L kernel X := by
  have other : ∀ c : AlignedClass, c ≠ .tc ∧ c ≠ .bar →
      ¬ (c.Divergent L kernel X ∨ c.Exited L kernel X) := by
    rintro c hc (⟨e, f, pe, pf, ke, kf, -, he, -, hm, -⟩ | ⟨e, f, ev, -, he, hm, -⟩)
    · rw [not_member_other hW hc he] at hm
      cases hm
    · cases c <;> simp at hc <;> simp only [AlignedClass.exitMember] at hm <;>
        rw [not_member_other hW (by simp) he] at hm <;> cases hm
  rw [alignedMismatch_iff]
  rintro ((h | h) | (h | h) | h | h | h)
  · exact no_tcDivergent hpre hX hW h
  · exact no_tcExited hpre hX hW h
  · exact no_barDivergent hX hW h
  · exact no_barExited hX hW h
  · exact other .cluster (by simp) h
  · exact other .setMaxReg (by simp) h
  · exact other .matrix (by simp) h

/-- **No consistent execution is unsafe.** -/
theorem safe (hpre : Pre L A B D a b mem0) (ht : ThreadFacts L A B D X)
    (hX : Consistent L kernel [] mem0 X) : ¬ Unsafe L kernel [] mem0 X := by
  obtain ⟨P, m, u, hW⟩ := wit hpre ht hX
  exact hW.tcBulk.not_unsafe hX (hW.no_ub fun g hg => u_nil hpre hX hW hg) (no_unalloc hpre hW)
    (fun _ _ _ _ _ hc ha hb _ => conflict_order hpre hX hW hc ha hb) (no_barMismatch hX hW)
    (no_ctaBarFault hX hW) (no_tma_unsafe hpre hX hW) (fun h => h (sourceSafe hpre hX hW))
    (by simp) (no_alignedMismatch hpre hX hW) (not_warpDivergent (by decide +kernel))
    (no_sharedLifetimeUnsafe hpre hX hW) (no_pollShapeUnsafe hW) (no_mbarUninit hpre hX hW)
    (TensorStore.not_copyReduceNoRule_of_none fun _ _ hc r hr => by
      rw [(hW.copy_spec hc).2.1] at hr
      cases hr)
    (no_resourceUnsafe hpre hX hW) (no_releaseUnsafe hpre hX hW)
    (no_accessUnsafe hpre hX hW)
    (no_commit_unsafe hpre hW) (no_writesUnsafe hW) (no_instructionUnsafe hpre hX hW)
    (no_readsUnsafe hW)

end
end PTX.Kernels.TcGemm.Proof
