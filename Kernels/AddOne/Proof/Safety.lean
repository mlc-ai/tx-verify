-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.AddOne.Proof.Values
public import Lemmas.Kernel.PlainSafety
public import Kernels.AddOne.Proof.NoBarArrive

@[expose] public section

/-! # `SafeGoal`

The kernel has no asynchronous instruction, so `Execution.NoTma.not_unsafe` leaves the branches its
events decide. No undefined behaviour: it would follow a read whose bytes give no 4-byte sum, but
the read returns `word (x g)` (`read_value`) and its sum is `word (x g + 1)` (`incr_word`). Every
byte touched is in `A`, allocated by the precondition. Two conflicting accesses that share a byte
are thread `g`'s read and write of `A[g]`, ordered by program order (`read_before_write`). There
is no barrier and no shared access, and the kernel has no uniform guard. -/

namespace PTX.Kernels.AddOne.Proof
open PTX

noncomputable section

variable {L : Launch} {A : Nat} {x : Nat → BitVec 32} {mem0 : Mem0} {X : Execution}

/-- An access is thread `g`'s read or its write of `A[g]`. -/
theorem access_cases (ht : ThreadFacts L A X) {i : EvId} {a : Acc} {w : Bool}
    (h : X.Access i a w) :
    (w = false ∧ i.2 = 0 ∧ a = accA A i.1) ∨ (w = true ∧ i.2 = 1 ∧ a = accA A i.1) := by
  obtain ⟨g, k⟩ := i
  rcases h with ⟨bs, ⟨pc, hr⟩, rfl⟩ | ⟨bs, ⟨pc, hw⟩, rfl⟩ | ⟨old, new, hrmw⟩
  · obtain ⟨rfl, rfl⟩ := ht.reads hr
    exact .inl ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, -⟩ := ht.writes hw
    exact .inr ⟨rfl, rfl, rfl⟩
  · exact absurd hrmw (no_rmw ht)

/-- No event of the kernel is of an aligned class: it is a read, a write, the exit or the
undefined behaviour. -/
theorem not_member (ht : ThreadFacts L A X) (c : AlignedClass) {e : EvId} {ev : Event}
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
theorem no_alignedMismatch (ht : ThreadFacts L A X) : ¬ AlignedMismatch L kernel X := by
  intro h
  rcases h with ⟨c, ⟨e, f, pe, pf, ke, kf, -, he, -, hm, -⟩ | ⟨e, f, ev, -, he, hm, -⟩⟩
  · rw [(not_member ht c he).1] at hm
    cases hm
  · rw [(not_member ht c he).2] at hm
    cases hm

/-- No undefined behaviour. -/
theorem no_ub (hpre : Pre L A x mem0) (hX : Consistent L kernel [] mem0 X)
    (ht : ThreadFacts L A X) : ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, he⟩
  obtain ⟨rb, h0, hbad⟩ := ht.ub he
  exact hbad _ _ (read_value hpre hX ht h0) (incr_word L g (x g)) rfl

/-- Every touched byte is allocated. -/
theorem no_unalloc (hpre : Pre L A x mem0) (hX : Consistent L kernel [] mem0 X)
    (ht : ThreadFacts L A X) : ¬ Unalloc mem0 X := by
  rintro (⟨e, a, l, htouch, hc, hn⟩ | ⟨e, m, l, hu, hc, hn⟩)
  · obtain ⟨i, -, h⟩ :=
      Execution.NoTma.memTouches_thread (noTma_of_consistent noTma hX) htouch
    obtain ⟨l1, l2, l3⟩ := l
    have hacc : ∀ {pc kd}, X.get i = some ⟨pc, kd⟩ → a = accA A i.1 → False := by
      intro pc kd hget ha
      subst ha
      have hgB := lt_block hpre (Frame.lt_of_get hX hget)
      simp only [Acc.Covers, Loc.InRange, accA] at hc
      obtain ⟨rfl, rfl, h1, h2⟩ := hc
      have := hpre.input i.1 hgB (l3 - (A + 4 * i.1)) (by omega)
      rw [show A + 4 * i.1 + (l3 - (A + 4 * i.1)) = l3 by omega, hn] at this
      cases this
    rcases h with ⟨bs, pc, hr⟩ | ⟨bs, pc, hnc⟩ | ⟨bs, pc, hw⟩ | ⟨old, new, hrmw⟩
    · exact hacc hr (ht.reads hr).2
    · rcases ht.kinds hnc with ⟨_, _, h⟩ | ⟨_, _, h⟩ | h | ⟨_, h⟩ <;> simp at h
    · exact hacc hw (ht.writes hw).2.1
    · exact absurd hrmw (no_rmw ht)
  · exact absurd hu (noTma_of_consistent noTma hX).not_usesMbar

/-- **Conflicting accesses are ordered**: they are one thread's read and write of its element. -/
theorem ordered (ht : ThreadFacts L A X) (hX : Consistent L kernel [] mem0 X) :
    ConflictsOrdered L X fun _ => True := by
  intro e f a b l hc h1 h2 _
  obtain ⟨hne, we, wf, hae, haf, hw, -⟩ := hc
  have hn := noTma_of_consistent noTma hX
  obtain ⟨⟨g, k⟩, rfl, hae⟩ := Execution.NoTma.intent_thread hn hae
  obtain ⟨⟨h, k'⟩, rfl, haf⟩ := Execution.NoTma.intent_thread hn haf
  have hacc := fun {i a w} (hi : X.Access i a w) => access_cases ht hi
  rcases hacc hae with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases hacc haf with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    obtain rfl := covers_A_A h1 h2
  · simp at hw
  · rcases haf with ⟨_, -, hb⟩ | ⟨bs, ⟨pc, h1'⟩, -⟩ | ⟨old, new, hrmw⟩
    · cases hb
    · obtain ⟨-, ha, _, _, _, _, h0, -⟩ := ht.writes h1'
      exact .inl (read_before_write h0 h1' ha l)
    · exact absurd hrmw (no_rmw ht)
  · rcases hae with ⟨_, -, hb⟩ | ⟨bs, ⟨pc, h1'⟩, -⟩ | ⟨old, new, hrmw⟩
    · cases hb
    · obtain ⟨-, ha, _, _, _, _, h0, -⟩ := ht.writes h1'
      exact .inr (read_before_write h0 h1' ha l)
    · exact absurd hrmw (no_rmw ht)
  · exact absurd rfl hne

/-- **No consistent execution is unsafe.** -/
theorem safe_goal (hpre : Pre L A x mem0)
    (hT : ∀ X, Consistent L kernel [] mem0 X → ThreadFacts L A X) :
    SafeGoal kernel [] L mem0 := by
  refine ⟨rfl, fun X hX => ?_⟩
  have ht := hT X hX
  have hnb := no_bar ht
  refine (noTma_of_consistent noTma hX).not_unsafe hX (no_ub hpre hX ht) (no_unalloc hpre hX ht)
    (ordered ht hX) (Execution.NoTma.no_barMismatch_of (noTma_of_consistent noTma hX) hnb)
    (Execution.NoTma.no_ctaBarFault_of hX hnb) (by simp) (no_alignedMismatch ht)
    (not_warpDivergent (by decide +kernel)) fun e a w h hs => ?_
  rcases access_cases ht h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [accA] at hs

end

end PTX.Kernels.AddOne.Proof
