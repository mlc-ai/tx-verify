-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.Tensor

@[expose] public section

/-!
# The commit branch of `Unsafe`

Every `tcgen05.commit` of the kernel is the MMA warp's, to one of four barriers of its own CTA
(`Interface.mma_event_state`, `EvW.MmShape`), with the specification `commitSpec`: one CTA group,
the thread's own CTA as the cluster base, cluster size one. A thread is alone in its cluster
(`Pre`), so the spec resolves from the thread's rank mask and the issuing CTA group exists.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A commit event's specification is the `commitSpec` of its CTA for a shared byte of it. -/
theorem commit_shape {g : Nat} {d : Mma.D} {pc : Nat} {s : TcCommit.Spec}
    (hsh : MmShape L g d ⟨pc, .tc (.commit s)⟩) :
    ∃ a, s = commitSpec (g / L.block) ⟨.shared, g / L.block, a⟩ := by
  unfold MmShape at hsh
  cases hs : d.site <;> simp only [hs] at hsh
  all_goals first
    | (simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
       exact ⟨_, hsh.2⟩)
    | (exfalso; simp [QkIssue, PvIssue] at hsh)

/-- **No commit is unsafe**: the issuing CTA group of every commit exists, since the issuing CTA
is alone in its cluster. -/
theorem no_tcCommitUnsafe (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) : ¬ TcCommitUnsafe L X := by
  rintro ⟨⟨g, k⟩, s, ⟨pc, he⟩, hn⟩
  apply hn
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, P, -, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he (.inr ⟨s, rfl⟩)
  obtain ⟨a, rfl⟩ := commit_shape hsh
  have hu := unitCta_of_pre hpre hg
  have hc : g / L.block < L.nclusters := by rw [hu.nclusters]; exact hu.cta
  have hrank := Launch.rankOfCta_unit hu.places hc
  refine ⟨hg, ?_, ?_⟩
  · have := resolve_unit hu a
    rw [hrank] at this
    simpa [commitSpec] using this
  · show L.ctaGroup (g / L.block) CtaGroup.one ≠ none
    rw [Launch.ctaGroup_one, peer_self hu]
    simp

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
