-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyDynamic.Proof.Values
public import Lemmas.Kernel.PlainSafety
public import Kernels.CopyDynamic.Proof.NoBarArrive

@[expose] public section

/-! # `SafeGoal`

The kernel has no asynchronous instruction, so `Execution.NoTma.not_unsafe` leaves the branches its
events decide. No undefined behaviour: it would follow a read whose bytes are not one 4-byte value,
but the read returns `x g` (`read_value`). Every byte touched is in `A` or `B`, allocated by the
precondition. The reads are of `A`, the writes of distinct elements of `B`, so no two conflicting
accesses touch one byte. There is no barrier and no shared access, and the kernel has no uniform
guard. -/

namespace PTX.Kernels.CopyDynamic.Proof
open PTX

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} {X : Execution}

/-- No event of the kernel is of an aligned class: it is a read, a write, the exit or the
undefined behaviour. -/
theorem not_member (ht : ThreadFacts L A B N X) (c : AlignedClass) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : c.member ev = false ∧ c.exitMember kernel ev = false := by
  obtain ⟨pc, k⟩ := ev
  rcases ht.kinds he with ⟨a, bs, hk⟩ | ⟨a, bs, hk⟩ | hk | ⟨f, hk⟩
  · have hev : (⟨pc, k⟩ : Event) = ⟨pc, .rd a bs⟩ := by rw [← hk]
    rw [hev]
    cases c <;>
      simp [AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar, isTcColl,
        Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix]
  · have hev : (⟨pc, k⟩ : Event) = ⟨pc, .wr a bs⟩ := by rw [← hk]
    rw [hev]
    cases c <;>
      simp [AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar, isTcColl,
        Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix]
  · have hev : (⟨pc, k⟩ : Event) = ⟨pc, .exit⟩ := by rw [← hk]
    rw [hev]
    cases c <;>
      simp [AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar, isTcColl,
        Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix]
  · have hev : (⟨pc, k⟩ : Event) = ⟨pc, .ub f⟩ := by rw [← hk]
    rw [hev]
    cases c <;>
      simp [AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar, isTcColl,
        Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix]

/-- **No aligned instruction diverges or is left by an exit.** -/
theorem no_alignedMismatch (ht : ThreadFacts L A B N X) : ¬ AlignedMismatch L kernel X := by
  intro h
  rcases h with ⟨c, ⟨e, f, pe, pf, ke, kf, -, he, -, hm, -⟩ | ⟨e, f, ev, -, he, hm, -⟩⟩
  · rw [(not_member ht c he).1] at hm
    cases hm
  · rw [(not_member ht c he).2] at hm
    cases hm

/-- An access is thread `g`'s read of `A[g]` or its write of `B[g]`, for `g < N`. -/
theorem access_cases (ht : ThreadFacts L A B N X) {i : EvId} {a : Acc} {w : Bool}
    (h : X.Access i a w) :
    (w = false ∧ i.1 < N ∧ a = accA A i.1) ∨ (w = true ∧ i.1 < N ∧ i.2 = 1 ∧ a = accB B i.1) := by
  obtain ⟨g, k⟩ := i
  rcases h with ⟨bs, ⟨pc, hr⟩, rfl⟩ | ⟨bs, ⟨pc, hw⟩, rfl⟩ | ⟨old, new, hrmw⟩
  · obtain ⟨-, hgN, rfl⟩ := ht.reads hr
    exact .inl ⟨rfl, hgN, rfl⟩
  · obtain ⟨rfl, hgN, rfl, -⟩ := ht.writes hw
    exact .inr ⟨rfl, hgN, rfl, rfl⟩
  · exact absurd hrmw (no_rmw ht)

/-- No undefined behaviour. -/
theorem no_ub (hpre : Pre L A B N x mem0) (hX : Consistent L kernel [] mem0 X)
    (ht : ThreadFacts L A B N X) : ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, he⟩
  obtain ⟨-, rb, h0, hbad⟩ := ht.ub he
  obtain ⟨hv, hb⟩ := read_value hpre hX ht h0
  exact hbad _ hv hb

/-- Every touched byte is allocated. -/
theorem no_unalloc (hpre : Pre L A B N x mem0) (hX : Consistent L kernel [] mem0 X)
    (ht : ThreadFacts L A B N X) : ¬ Unalloc mem0 X := by
  rintro (⟨e, a, l, htouch, hc, hn⟩ | ⟨e, m, l, hu, hc, hn⟩)
  · obtain ⟨i, -, h⟩ :=
      Execution.NoTma.memTouches_thread (noTma_of_consistent noTma hX) htouch
    obtain ⟨l1, l2, l3⟩ := l
    rcases h with ⟨bs, pc, hr⟩ | ⟨bs, pc, hnc⟩ | ⟨bs, pc, hw⟩ | ⟨old, new, hrmw⟩
    · obtain ⟨-, hgN, rfl⟩ := ht.reads hr
      simp only [Acc.Covers, Loc.InRange, accA] at hc
      obtain ⟨rfl, rfl, h1, h2⟩ := hc
      have := hpre.input i.1 hgN (l3 - (A + 4 * i.1)) (by omega)
      rw [show A + 4 * i.1 + (l3 - (A + 4 * i.1)) = l3 by omega, hn] at this
      cases this
    · rcases ht.kinds hnc with ⟨_, _, h⟩ | ⟨_, _, h⟩ | h | ⟨_, h⟩ <;> simp at h
    · obtain ⟨-, hgN, rfl, -⟩ := ht.writes hw
      simp only [Acc.Covers, Loc.InRange, accB] at hc
      obtain ⟨rfl, rfl, h1, h2⟩ := hc
      have := hpre.output (l3 - B) (by omega)
      rw [show B + (l3 - B) = l3 by omega] at this
      exact this hn
    · exact absurd hrmw (no_rmw ht)
  · exact absurd hu (noTma_of_consistent noTma hX).not_usesMbar

/-- No two conflicting accesses touch one byte. -/
theorem ordered (hpre : Pre L A B N x mem0) (hX : Consistent L kernel [] mem0 X)
    (ht : ThreadFacts L A B N X) : ConflictsOrdered L X fun _ => True := by
  refine ConflictsOrdered.of_none fun e f a b l hc h1 h2 _ => ?_
  obtain ⟨hne, we, wf, hae, haf, hw, -⟩ := hc
  have hn := noTma_of_consistent noTma hX
  obtain ⟨e, rfl, hae⟩ := Execution.NoTma.intent_thread hn hae
  obtain ⟨f, rfl, haf⟩ := Execution.NoTma.intent_thread hn haf
  rcases access_cases ht hae with ⟨rfl, he, rfl⟩ | ⟨rfl, he, he1, rfl⟩ <;>
    rcases access_cases ht haf with ⟨rfl, hf, rfl⟩ | ⟨rfl, hf, hf1, rfl⟩
  · simp at hw
  · exact covers_A_B hpre he hf h1 h2
  · exact covers_A_B hpre hf he h2 h1
  · exact hne (congrArg AsyncCopy.Ref.thread (Prod.ext (covers_B_B h1 h2) (by omega)))

/-- **No consistent execution is unsafe.** -/
theorem safe_goal (hpre : Pre L A B N x mem0)
    (hT : ∀ X, Consistent L kernel [] mem0 X → ThreadFacts L A B N X) :
    SafeGoal kernel [] L mem0 := by
  refine ⟨rfl, fun X hX => ?_⟩
  have ht := hT X hX
  have hnb := no_bar ht
  refine (noTma_of_consistent noTma hX).not_unsafe hX (no_ub hpre hX ht) (no_unalloc hpre hX ht)
    (ordered hpre hX ht) (Execution.NoTma.no_barMismatch_of (noTma_of_consistent noTma hX) hnb)
    (Execution.NoTma.no_ctaBarFault_of hX hnb) (by simp) (no_alignedMismatch ht)
    (not_warpDivergent (by decide +kernel)) fun e a w h hs => ?_
  rcases access_cases ht h with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> simp [accA, accB] at hs

end

end PTX.Kernels.CopyDynamic.Proof
