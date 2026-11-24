-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Proof.Safety.Memory
public import Kernels.RowSum.Proof.Safety.ThreadUb
public import Lemmas.Kernel.PlainSafety
public import Kernels.RowSum.Proof.NoBarArrive

@[expose] public section

/-! # `row_sum`: safety

No possible execution is unsafe: no undefined behaviour, only allocated bytes, no conflicting
accesses, no barrier, no shared memory. -/

namespace PTX.Kernels.RowSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0} {X : Execution}

/-- No event of the kernel is of an aligned class: it is a read, a write, the exit or the
undefined behaviour. -/
theorem not_member (htf : ThreadFacts L A B M K x X) (hX : Consistent L kernel Prod mem0 X)
    (c : AlignedClass) {e : EvId} {ev : Event} (he : X.get e = some ev) :
    c.member ev = false ∧ c.exitMember kernel ev = false := by
  obtain ⟨pc, k⟩ := ev
  obtain ⟨-, hc⟩ := event_cases htf hX he
  rcases hc with ⟨-, -, bs, hk⟩ | ⟨-, -, d, -, -, hk⟩ | hk | ⟨_, f, hk, _, _, _, _⟩
  · rw [hk]
    cases c <;>
      simp [rdE, AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar, isTcColl,
        Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix]
  · rw [hk]
    cases c <;>
      simp [wrE, AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar, isTcColl,
        Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix]
  · rw [exE] at hk
    rw [hk]
    cases c <;>
      simp [AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar, isTcColl,
        Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix]
  · rw [hk]
    cases c <;>
      simp [AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar, isTcColl,
        Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix]

/-- **No aligned instruction diverges or is left by an exit.** -/
theorem no_alignedMismatch (htf : ThreadFacts L A B M K x X)
    (hX : Consistent L kernel Prod mem0 X) : ¬ AlignedMismatch L kernel X := by
  intro h
  rcases h with ⟨c, ⟨e, f, pe, pf, ke, kf, -, he, -, hm, -⟩ | ⟨e, f, ev, -, he, hm, -⟩⟩
  · rw [(not_member htf hX c he).1] at hm
    cases hm
  · rw [(not_member htf hX c he).2] at hm
    cases hm

/-- **No possible execution is unsafe.** -/
theorem safe (hpre : Pre L A B M K x mem0) (htf : ThreadFacts L A B M K x X)
    (hX : Consistent L kernel Prod mem0 X) : ¬ Unsafe L kernel Prod mem0 X := by
  have hnb : ∀ e id count pc, ¬ X.IsBarrier e id count pc := fun _ _ _ _ => no_bar htf hX
  refine Execution.NoTma.not_unsafe (noTma_of_consistent noTma hX) hX (no_ub hpre htf hX)
    (no_unalloc hpre htf hX)
    (ConflictsOrdered.of_none fun _ _ _ _ _ hc _ _ _ => no_conflict hpre htf hX hc)
    (Execution.NoTma.no_barMismatch_of (noTma_of_consistent noTma hX) hnb)
    (Execution.NoTma.no_ctaBarFault_of hX hnb) ?_ (no_alignedMismatch htf hX)
    (not_warpDivergent (by decide +kernel)) ?_
  · rintro ⟨a, ha, hu⟩
    obtain rfl := List.mem_singleton.mp ha
    exact hu
  · intro e a w ha hs
    have := access_global htf hX ha
    rw [hs] at this
    cases this

end
end PTX.Kernels.RowSum.Proof
