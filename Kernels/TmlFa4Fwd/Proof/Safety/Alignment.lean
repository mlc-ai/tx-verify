-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.StartupAlignment
public import Kernels.TmlFa4Fwd.Proof.Thread.AlignedBarrierCases
import Kernels.TmlFa4Fwd.Proof.RegisterSafety
import Kernels.TmlFa4Fwd.Proof.StaticSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX

/-- Startup precedes every exit, so no lane skips an aligned full-CTA rendezvous. -/
theorem noAlignedBarrierExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    ¬ AlignedClass.bar.Exited l kernel X := by
  rintro ⟨_, _, _, _, he, hClass, _, ⟨_, hExit⟩, hCount⟩
  have hFirst := Thread.Startup.alignedRendezvousOrdinal hp hX he hClass
  have hSeen := Thread.Startup.alignedRendezvousOfExit hp hX ⟨_, hExit, rfl⟩
  simp only [AlignedClass.exitMember, hFirst] at hCount
  omega

/-- The only possible alignment mismatches are Tensor Core collectives or disagreeing CTA
barrier events. The cluster and matrix classes are absent and the register adjustment is uniform. -/
theorem alignmentCases {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (h : AlignedMismatch l kernel X) :
    (AlignedClass.tc.Divergent l kernel X ∨ AlignedClass.tc.Exited l kernel X) ∨
      Thread.AlignedWorkBarrierMismatch l X := by
  have absent {c : AlignedClass}
      (hClass : ∀ i e, X.get i = some e →
        c.member e = false ∧ c.exitMember kernel e = false) :
      ¬ (c.Divergent l kernel X ∨ c.Exited l kernel X) := by
    rintro (⟨i, _, _, _, _, _, _, hi, _, hm, _⟩ | ⟨i, _, e, _, hi, hm, _⟩)
    · rw [(hClass i _ hi).1] at hm
      cases hm
    · rw [(hClass i e hi).2] at hm
      cases hm
  have hCluster : ¬ (AlignedClass.cluster.Divergent l kernel X ∨
      AlignedClass.cluster.Exited l kernel X) := by
    apply absent
    rintro i ⟨_, kind⟩ hi
    cases kind <;> try exact ⟨rfl,rfl⟩
    exact (noClusterEvent hX hi).elim
  have hMatrix : ¬ (AlignedClass.matrix.Divergent l kernel X ∨
      AlignedClass.matrix.Exited l kernel X) := by
    apply absent
    intro i e hi
    have hNone := noMatrixEvent hX hi
    exact ⟨hNone,hNone⟩
  rcases (alignedMismatch_iff l).mp h with hTc | hBar | hOther
  · exact .inl hTc
  · exact .inr (Thread.alignedBarrierDivergenceIsWork hp hX
      (hBar.resolve_right (noAlignedBarrierExit hp hX)))
  · rcases hOther with h | h | h
    · exact (hCluster h).elim
    · exact (noRegisterAlignmentMismatch hp hX h).elim
    · exact (hMatrix h).elim

end PTX.Kernels.TmlFa4Fwd.Safety
