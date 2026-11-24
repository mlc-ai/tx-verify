-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeUse
public import Kernels.InklingRelDecode.Proof.Interface.ScRead
public import Kernels.InklingRelDecode.Proof.Interface.FootClass

@[expose] public section

/-!
# The placement of the kernel's shared uses

`Life.Own L X` (`IpLifeUse`): every shared use of the kernel is of its issuer's CTA. Its five
fields, from the program text and the thread layer's event classification:

* `mbar` (`mbar_own_of`): the operand of every mbarrier instruction is one of the twelve of the
  instruction's own CTA (the same case split as `Safety.mbarPlaced_of`, which keeps the CTA);
* `access` (`access_own_of`): a read or write fires from a load or store of a fixed space, and a
  shared one is of the thread's CTA (`fires_read_loc`, `fires_write_loc`); the kernel has no
  dynamic access (`kernel_noDynamic`) and no atomic;
* `tensor` (`tensor_own_of`): the prologue's and the loader's copies have `sharedBase` in the
  thread's CTA;
* `mma` (`mma_own_of`): the MMA specifications carry the thread's CTA as both operand CTAs;
* `group` (`group_own_of`): the commit specification has CTA group one, and a thread is alone in
  its cluster.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Life
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX.Kernels.InklingRelDecode.Proof.EvW

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Mbarrier operands -/

/-- **Every mbarrier an instruction names is one of the twelve of the instruction's CTA**, given
the barrier of the `o_done` poll. -/
theorem mbar_own_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (ho : OdoneWait Q L X) :
    ∀ {e : EvId} {m : Loc}, X.UsesMbar e m → m.cta = e.1 / L.block := by
  intro e m hu
  obtain ⟨g, k⟩ := e
  suffices h : ∃ b : EvD.Bar, m = b.loc L (g / L.block) by
    obtain ⟨b, rfl⟩ := h
    rfl
  rcases hu with ⟨tx, count, rel, sc, pc, he⟩ | ⟨s, ⟨pc, he⟩, -⟩ | ⟨noinc, pc, he⟩ |
    ⟨s, rank, hcm, htg⟩ | ⟨pc, q, ok, acq, sc, he⟩ | ⟨pc, he⟩ |
    ⟨address, s, ⟨pc, he⟩, rfl⟩ | ⟨s, targets, c, ⟨pc, he⟩, -⟩ | ⟨count, pc, he⟩
  · have hg := Frame.lt_of_get hX he
    rcases arrive_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he
        ⟨m, tx, count, rel, sc, rfl⟩ with
      ⟨d, -, j, -, -, hev⟩ | ⟨d, -, -, -, hev⟩ | ⟨d, P, -, -, hsh⟩
    · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
      exact ⟨_, hev.2.1⟩
    · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
      exact ⟨_, hev.2.1⟩
    · exact ld_arrive_bar hsh
  · exact absurd he (no_copy hX)
  · exact absurd he (no_asyncArrive hX)
  · obtain ⟨pc, he⟩ := hcm
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, P, -, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he
      (.inr ⟨s, rfl⟩)
    exact commit_target_bar hsh htg
  · have hg := Frame.lt_of_get hX he
    rcases wait_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨m, q, ok, acq, sc, rfl⟩ with
      ⟨d, hσ, ⟨hs, ok', hev⟩ | hs⟩ | ⟨d, P, -, -, hsh⟩ | ⟨d, P, -, hs, hsh⟩ |
        ⟨d, -, -, ok', hev⟩
    · simp only [Event.mk.injEq, Kind.wait.injEq] at hev
      exact ⟨_, hev.2.1⟩
    · exact ⟨.oDone, ho hσ hs he⟩
    · exact ld_wait_bar hsh
    · exact mm_wait_bar hs hsh
    · simp only [Event.mk.injEq, Kind.wait.injEq] at hev
      exact ⟨_, hev.2.1⟩
  · exact absurd he (no_inval hX)
  · have hg := Frame.lt_of_get hX he
    rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨address, s, rfl⟩ with
      ⟨d, -, i, -, -, a', s', hev, -, -, h3, -⟩ | ⟨d, P, -, hsh⟩
    · simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
      obtain ⟨-, -, rfl⟩ := hev
      exact ⟨_, h3⟩
    · exact ld_copy_bar hsh
  · exact absurd he (no_clc hX)
  · have hg := Frame.lt_of_get hX he
    obtain ⟨d, -, i, -, -, hev⟩ := init_event_state hpre hX hf.sound hf.tracked hg he
      ⟨m, count, rfl⟩
    simp only [Event.mk.injEq, Kind.mbInit.injEq] at hev
    exact ⟨_, hev.2.1⟩

/-! ### Thread accesses -/

/-- **A thread's shared accesses are of its own CTA.** -/
theorem access_own_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) :
    ∀ {g k : Nat} {a : Acc} {w : Bool}, X.Access (g, k) a w → a.loc.space = .shared →
      a.loc.cta = g / L.block := by
  intro g k a w ha hsp
  rcases ha with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
  · have hg := Frame.lt_of_get hX he
    obtain ⟨s, hσ⟩ := Frame.event_state hf.sound hX hf.tracked he
      (fun pc' f h => by cases h)
    cases thread_read_class hpre hX hf.sound hT hg he hσ hsp <;>
      rw [‹a.loc = _›]
  · have hg := Frame.lt_of_get hX he
    obtain ⟨s, hσ⟩ := Frame.event_state hf.sound hX hf.tracked he
      (fun pc' f h => by cases h)
    cases thread_write_class hpre hX hf.sound hg he hσ hsp <;>
      first | rw [‹a.loc = _›] | (rw [‹a = _›]; try rfl)
  · exact (no_rmw hX he).elim

/-! ### Tensor copies, MMAs, commits -/

/-- **A tensor copy writes the shared memory of its own CTA.** -/
theorem tensor_own_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) :
    ∀ {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec},
      X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.sharedBase.cta = i.1 / L.block := by
  intro i pc a sp he
  obtain ⟨g, k⟩ := i
  have hg := Frame.lt_of_get hX he
  rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨a, sp, rfl⟩ with
    ⟨d, -, i', -, -, a', s', hev, -, -, -, h4, -⟩ | ⟨d, P, -, hsh⟩
  · simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, -, rfl⟩ := hev
    rw [h4]
  · unfold LdShape at hsh
    cases hs : d.site <;> simp only [hs] at hsh
    all_goals first
      | (simp at hsh; done)
      | (obtain ⟨b, -, hev⟩ := hsh
         simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
         obtain ⟨-, -, rfl⟩ := hev
         rfl)

/-- **An MMA's operands are in its own CTA.** -/
theorem mma_own_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) :
    ∀ {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat},
      X.MmaIssue i d s acc mask → s.lowCta = i.1 / L.block ∧ s.highCta = i.1 / L.block := by
  intro i d s acc mask hm
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hm
  have hg := Frame.lt_of_get hX he
  obtain ⟨dd, P, -, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he
    (.inl ⟨d, s, acc, mask, rfl⟩)
  unfold MmShape at hsh
  cases hs : dd.site <;> simp only [hs] at hsh
  all_goals first
    | (obtain ⟨da, db, dsc, -, -, -, hev⟩ := hsh
       simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hev
       obtain ⟨-, -, rfl, -⟩ := hev
       exact ⟨rfl, rfl⟩)
    | (obtain ⟨db, dsc, -, -, hev⟩ := hsh
       simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hev
       obtain ⟨-, -, rfl, -⟩ := hev
       exact ⟨rfl, rfl⟩)
    | (exfalso; simp at hsh)

/-- **The CTA group of a commit is its own CTA**: the cluster of a CTA is the CTA itself. -/
theorem group_own_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {s : TcCommit.Spec} {c : Nat},
      (∃ pc, X.get i = some ⟨pc, .tc (.commit s)⟩) →
        SameCtaGroup L s.group (i.1 / L.block) c → c = i.1 / L.block := by
  intro i s c ⟨pc, he⟩ hgrp
  have hg := Frame.lt_of_get hX he
  have hu := unitCta_of_pre hpre hg
  obtain ⟨⟨-, hc, hcl⟩, -⟩ := hgrp
  have h1 := Launch.clusterOfCta_unit hu.places (cta := c) (by rw [hu.nclusters]; exact hc)
  have h2 := Launch.clusterOfCta_unit hu.places (cta := i.1 / L.block)
    (by rw [hu.nclusters]; exact hu.cta)
  rw [h1, h2] at hcl
  exact hcl.symm

/-- **Placement of every shared use.** -/
theorem own_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (ho : OdoneWait Q L X)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) : Own L X where
  mbar := mbar_own_of hpre hX hf ho
  access := access_own_of hpre hX hf hT
  tensor := tensor_own_of hpre hX hf
  mma := mma_own_of hpre hX hf
  group := group_own_of hpre hX

end
end PTX.Kernels.InklingRelDecode.Proof.Life
