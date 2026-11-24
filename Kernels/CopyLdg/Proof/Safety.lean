-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Proof.Values
public import Lemmas.Kernel.PlainSafety
public import Lemmas.Kernel.Goals
public import Kernels.CopyLdg.Proof.NoBarArrive

@[expose] public section

/-! # `copy_ldg`: no possible execution is unsafe

The kernel has no asynchronous, barrier or shuffle instruction, so the branches of `Unsafe`
that need such events are empty (`Execution.NoTma.not_unsafe`). The branches its own events
decide: no undefined behaviour (`no_ub`), every byte accessed is allocated, no two accesses
conflict (writes are to distinct elements of `B`, reads are `nc`), and no write reaches a byte an
`nc` read reads (`A` and `B` are disjoint). -/

namespace PTX.Kernels.CopyLdg.Proof

open PTX PTX.Proof PTX.Flow

local notation "Nc" => [Assumptions.ncInput]

noncomputable section

theorem noTma : kernel.NoTma := rfl

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} {X : Execution}

/-- No two accesses conflict: the only accesses are the writes of distinct threads to distinct
elements of `B`. -/
theorem no_conflict (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {e f : AsyncCopy.Ref} {a b : Acc} : ¬ Conflict X e f a b := by
  rintro ⟨hne, we, wf, hae, haf, -, l, hl1, hl2⟩
  have hn := noTma_of_consistent noTma hX
  obtain ⟨e, rfl, hae⟩ := Execution.NoTma.intent_thread hn hae
  obtain ⟨f, rfl, haf⟩ := Execution.NoTma.intent_thread hn haf
  have acc : ∀ {v c w}, X.Access v c w → v.1 < N ∧ v.2 = 1 ∧ c = { loc := gB B v.1, size := 4 } :=
    by
    intro v c w h
    rcases h with ⟨bs, hr, -⟩ | ⟨bs, hw, -⟩ | ⟨old, new, hrmw⟩
    · exact absurd hr (no_rd hpre hX ht)
    · obtain ⟨-, h1, h2, h3, -⟩ := written_value hpre hX ht hw; exact ⟨h1, h2, h3⟩
    · exact absurd hrmw (no_rmw hpre hX ht)
  obtain ⟨-, h1, rfl⟩ := acc hae
  obtain ⟨-, h2, rfl⟩ := acc haf
  exact hne (congrArg AsyncCopy.Ref.thread (Prod.ext (covers_gB_gB hl1 hl2) (by omega)))

/-- No event of the kernel is of an aligned class: it is an `nc` read, a write, the exit or the
undefined behaviour. -/
theorem not_member (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) (c : AlignedClass) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : c.member ev = false ∧ c.exitMember kernel ev = false := by
  obtain ⟨pc, k⟩ := ev
  rcases (event_cases hpre hX ht he).2 with ⟨-, -, bs, -, hev⟩ | ⟨-, -, bs, v, -, -, -, -, hev⟩ |
    ⟨hev, -⟩ | ⟨-, ⟨f, hk⟩, -⟩
  · rw [hev]
    cases c <;>
      simp [AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar, isTcColl,
        Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix, ncE]
  · rw [hev]
    cases c <;>
      simp [AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar, isTcColl,
        Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix, wrE]
  · rw [hev]
    cases c <;>
      simp [AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar, isTcColl,
        Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix, exE]
  · have hev : (⟨pc, k⟩ : Event) = ⟨pc, .ub f⟩ := by rw [← hk]
    rw [hev]
    cases c <;>
      simp [AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar, isTcColl,
        Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix]

/-- **No aligned instruction diverges or is left by an exit.** -/
theorem no_alignedMismatch (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) : ¬ AlignedMismatch L kernel X := by
  rintro ⟨c, ⟨e, f, pe, pf, ke, kf, -, he, -, hm, -⟩ | ⟨e, f, ev, -, he, hm, -⟩⟩
  · rw [(not_member hpre hX ht c he).1] at hm
    cases hm
  · rw [(not_member hpre hX ht c he).2] at hm
    cases hm

/-- **`SafeGoal`.** -/
theorem safe_goal (hpre : Pre L A B N x mem0)
    (hthr : ∀ X, Consistent L kernel Nc mem0 X → ThreadFacts L A B N X) :
    SafeGoal kernel Nc L mem0 := by
  refine ⟨rfl, fun X hX => ?_⟩
  have ht := hthr X hX
  have hn := noTma_of_consistent noTma hX
  have hnb : ∀ e id count pc, ¬ X.IsBarrier e id count pc :=
    fun _ _ _ _ h => no_bar hpre hX ht h
  refine hn.not_unsafe hX ?_ ?_ ?_ (Execution.NoTma.no_barMismatch_of hn hnb)
    (Execution.NoTma.no_ctaBarFault_of hX hnb) ?_ (no_alignedMismatch hpre hX ht)
    (not_warpDivergent (by decide +kernel)) ?_
  · rintro ⟨e, pc, f, he⟩
    exact no_ub hpre hX ht he f rfl
  · rintro (⟨e, a, l, htouch, hc, hnone⟩ | ⟨e, m, l, hu, hc, hnone⟩)
    · obtain ⟨e, heRef, htThread⟩ := Execution.NoTma.memTouches_thread hn htouch
      subst heRef
      rcases htThread with ⟨bs, hr⟩ | ⟨bs, hnc⟩ | ⟨bs, hw⟩ | ⟨old, new, hrmw⟩
      · exact no_rd hpre hX ht hr
      · obtain ⟨-, hgN, -, rfl⟩ := ncreads_cases hpre hX ht hnc
        simp only [Acc.Covers, Loc.InRange, gA] at hc
        obtain ⟨l1, l2, l3⟩ := l
        simp only at hc
        obtain ⟨rfl, rfl, h1, h2⟩ := hc
        have := hpre.input e.1 hgN (l3 - (A + 4 * e.1)) (by omega)
        rw [show A + 4 * e.1 + (l3 - (A + 4 * e.1)) = l3 by omega] at this
        rw [hnone] at this; simp at this
      · obtain ⟨-, hgN, -, rfl, -⟩ := written_value hpre hX ht hw
        simp only [Acc.Covers, Loc.InRange, gB] at hc
        obtain ⟨l1, l2, l3⟩ := l
        simp only at hc
        obtain ⟨rfl, rfl, h1, h2⟩ := hc
        have := hpre.output (l3 - B) (by omega)
        rw [show B + (l3 - B) = l3 by omega] at this
        exact this hnone
      · exact absurd hrmw (no_rmw hpre hX ht)
    · exact absurd hu hn.not_usesMbar
  · exact ConflictsOrdered.of_none fun e f a b l hc _ _ _ => no_conflict hpre hX ht hc
  · rintro ⟨a, ha, hub⟩
    simp only [List.mem_singleton] at ha
    subst ha
    obtain ⟨e, pc, a, bs, w, a', l, hnc, -, hc1, hw, hc2⟩ := hub
    obtain ⟨w, heRef, hwThread⟩ := Execution.NoTma.intent_thread hn hw
    subst heRef
    obtain ⟨bs', hw, _⟩ : ∃ bs', X.Writes w a' bs' ∧ true = true := by
      rcases hwThread with ⟨_, _, hf⟩ | hw | hrmw
      · cases hf
      · exact hw
      · obtain ⟨old, new, hrmw⟩ := hrmw
        exact absurd hrmw (no_rmw hpre hX ht)
    obtain ⟨-, hgN, -, rfl⟩ := ncreads_cases hpre hX ht ⟨pc, hnc⟩
    obtain ⟨-, hwN, -, rfl, -⟩ := written_value hpre hX ht hw
    exact covers_gA_gB hpre hgN hwN hc1 hc2
  · intro e a w ha hs
    rcases ha with ⟨bs, hr, -⟩ | ⟨bs, hw, -⟩ | ⟨old, new, hrmw⟩
    · exact (no_rd hpre hX ht hr).elim
    · obtain ⟨-, -, -, rfl, -⟩ := written_value hpre hX ht hw
      simp [gB] at hs
    · exact absurd hrmw (no_rmw hpre hX ht)

end
end PTX.Kernels.CopyLdg.Proof
