-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryReturnCommit
public import Kernels.TmlFa4Fwd.Proof.Thread.Mma
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitActors
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread

/-- A physical notification frees one of the issuing CTA's paged K/V slots. -/
def CacheRelease (l : Launch) (X : Execution) (i : EvId) (slot : Fin 3)
    (spec : TcCommit.Spec) (rank : Fin 16) : Prop :=
  X.Commit i spec ∧ TcCommit.target spec rank = some (Mma.Observation.emptyObject l i.1 slot)

/-- Every actual MMA notification targets an output, query-return, score, or cache object. -/
theorem commitDestination {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {spec : TcCommit.Spec} {rank : Fin 16} {object : Loc}
    (hi : X.Commit i spec) (ht : TcCommit.target spec rank = some object) :
    (FirstOutputCommit X i spec ∨ SecondOutputCommit X i spec) ∨
    (∃ stage, Mma.QueryReturn l X i stage spec rank) ∨
    (∃ stage, Scores.ScoreCommit l X i (i.1 / l.block) stage spec rank) ∨
    ∃ slot, CacheRelease l X i slot spec rank := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨offset, ho, hLoc⟩ := actualCommitOffsetIn hp hX he ht
  rw [hLoc] at ht
  have issued : X.Commit i spec := ⟨pc, he⟩
  have cache (slot : Fin 3)
      (hEq : TcCommit.target spec rank =
        some ⟨.shared, i.1 / l.block, l.sharedBase + (56 + 8 * slot.val)⟩) :
      CacheRelease l X i slot spec rank := by
    refine ⟨issued, ?_⟩
    rw [Mma.Observation.emptyObject, TmlFa4Fwd.Loader.emptySlot_address]
    simpa only [Nat.add_assoc, Nat.add_comm 56] using hEq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr (.inl ⟨0, issued, ht⟩)
  · exact .inr (.inl ⟨1, issued, ht⟩)
  · exact .inr (.inr (.inr ⟨0, cache 0 ht⟩))
  · exact .inr (.inr (.inr ⟨1, cache 1 ht⟩))
  · exact .inr (.inr (.inr ⟨2, cache 2 ht⟩))
  · exact .inr (.inr (.inl ⟨0, issued, ht⟩))
  · exact .inr (.inr (.inl ⟨1, issued, ht⟩))
  · exact .inl (outputCommitOfTarget hp hX 0 issued ht)
  · exact .inl (outputCommitOfTarget hp hX 1 issued ht)

end PTX.Kernels.TmlFa4Fwd.Thread
