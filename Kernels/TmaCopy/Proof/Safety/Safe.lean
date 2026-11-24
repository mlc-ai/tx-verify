-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Proof.MemoryFacts
public import Kernels.TmaCopy.Proof.NoBarArrive

@[expose] public section

/-! # No consistent execution is unsafe

The mbarrier branch (`no_tma_unsafe`): no record faults and every record follows the published
initialization (`Protocol/Mbar.lean`), no access touches the mbarrier, and the copy is neither a
`cp.async` nor a masked copy. Every mbarrier operand is an event of thread 0 after the
initialization, which happens before it (`no_mbarUninit`). Every shared-memory use is in CTA 0,
its issuer's CTA, and completes before an exit of a thread of CTA 0; the copy's notification is
observed by thread 0's acquire poll before its exit (`notify_finished`, `no_sharedLifetimeUnsafe`).
The poll is the canonical spin (`spin`, `no_pollShapeUnsafe`) and no event is of an aligned class
(`no_alignedMismatch`). Conflicting accesses are ordered and allocated (`MemoryFacts.lean`). Every
event is of the mbarrier/bulk class, so `Execution.MbarBulk.not_unsafe` dispatches every other
branch (`safe`). -/

namespace PTX.Kernels.TmaCopy.Proof
open PTX PTX.Proof AsyncCopy MBarrier
noncomputable section

variable {L : Launch} {A B : Nat} {x : Value} {mem0 : Mem0} {X : Execution}
variable (hpre : Pre L A B x mem0) (ht : ThreadFacts L A B X) (hX : Consistent L kernel [] mem0 X)
include hpre ht hX
omit hpre in
/-- Every mbarrier operand other than an initialization is an event of thread 0 after its
first event. -/
theorem uses_after_init {e : EvId} {m : Loc} (hu : X.UsesMbar e m)
    (hni : ∀ c, ¬ X.MbInit e m c) : e.1 = 0 ∧ 0 < e.2 ∧ ∃ ev, X.get e = some ev := by
  rcases hu with ⟨tx, count, release, scope, pc, hp⟩ | ⟨s, ⟨pc, hp⟩, -⟩ | ⟨noinc, ha⟩ |
    ⟨_, _, hc, _⟩ | ⟨pc, q, ok, acquire, scope, hp⟩ | hv | ⟨_, _, ⟨pc, hi⟩, _⟩ |
    ⟨_, _, _, ⟨pc, hi⟩, _⟩ | ⟨c, hi⟩
  · obtain ⟨rfl, -⟩ := arrive_cases ht hX ⟨pc, hp⟩
    exact ⟨rfl, by decide, _, hp⟩
  · obtain ⟨rfl, -⟩ := bulk_cases ht hX ⟨pc, hp⟩
    exact ⟨rfl, by decide, _, hp⟩
  · exact (no_asyncArrive ht hX ha).elim
  · exact ((noTc ht hX).not_commit hc).elim
  · obtain ⟨h0, h4, -⟩ := wait_cases ht hX hp
    exact ⟨h0, by omega, _, hp⟩
  · exact (no_inval ht hX hv).elim
  · exact (not_class ht hX hi rfl).elim
  · exact (not_class ht hX hi rfl).elim
  · exact (hni c hi).elim

omit hpre in
/-- **Every mbarrier operand follows the initialization** of `mbar` in program order. -/
theorem no_mbarUninit : ¬ MbarUninit L X := by
  rintro ⟨e, m, hu, hni, hnp⟩
  obtain ⟨h0, hpos, ev, he⟩ := uses_after_init ht hX hu hni
  obtain rfl := uses_cases ht hX hu
  obtain ⟨g, j⟩ := e
  simp only at h0 hpos
  subst h0
  exact hnp ⟨(0, 0), 1, ⟨_, init_get ht hX he⟩,
    .inl (po_zero (init_get ht hX he) (by simp [initE, Event.acc]) hpos he)⟩

omit hpre in
theorem exit_has_wait {j pc : Nat} (he : X.get (0, j) = some ⟨pc, .exit⟩) :
    ∃ w, X.AcquireWait w (mbar L.sharedBase) := by
  rcases (event_cases ht hX he).2 with ⟨hn, _⟩ | ⟨_, _, hh⟩ | ⟨_, _, hh⟩ |
    ⟨_, _, hh⟩ | ⟨_, _, hh⟩ | ⟨_, _, _, ⟨ok, hh⟩ | ⟨i, _, _, hw, _⟩⟩
  · exact (hn rfl).elim
  all_goals try (simp [initE, fenceE, arriveE, bulkE, waitE] at hh)
  exact ⟨(0, i), 13, 0, .cta, hw⟩

omit hpre in
theorem exit_copy_notified {j pc : Nat} (he : X.get (0, j) = some ⟨pc, .exit⟩) :
    (X.async.copies (0, 3)).notified = true := by
  obtain ⟨w, hw⟩ := exit_has_wait ht hX he
  obtain ⟨ws, ho⟩ := wait_observes_copy ht hX hw
  obtain ⟨m, bytes, ⟨spec, _, hn, _⟩, _⟩ := ho.copy
  exact hn

/-- Once CTA 0 has exited, the copy's notification completed before thread 0's exit: the
release complete-tx is observed by thread 0's successful acquire poll. -/
theorem notify_finished (hx : CtaExited L X 0) :
    SharedFinished L kernel [] X (.async (0, 3) (.notify .copy)) 0 := by
  obtain ⟨pc, hl⟩ := hx 0 (threads_pos hpre) (by simp)
  rw [List.getLast?_eq_getElem?] at hl
  have he : X.get (0, (X.tr 0).length - 1) = some ⟨pc, .exit⟩ := hl
  have hlen := get_lt he
  rcases (event_cases ht hX he).2 with ⟨hn, _⟩ | ⟨_, _, hh⟩ | ⟨_, _, hh⟩ |
    ⟨_, _, hh⟩ | ⟨_, _, hh⟩ | ⟨_, _, _, ⟨ok, hh⟩ | ⟨i, -, hil, hw, _⟩⟩
  · exact (hn rfl).elim
  all_goals try (simp [initE, fenceE, arriveE, bulkE, waitE] at hh)
  obtain ⟨ws, ho⟩ := wait_observes_copy ht hX (w := (0, i)) ⟨13, 0, .cta, hw⟩
  obtain ⟨-, -, ⟨-, -, hn, -⟩, -⟩ := ho.copy
  refine ⟨hn, (0, (X.tr 0).length - 1), pc, threads_pos hpre, by simp, he,
    CompletedBefore.of_copyRelease (.inl rfl) ho ?_ ⟨rfl, hil, by simp only; omega, ?_⟩⟩
  · have h0 := threads_pos hpre
    cases ws <;> simp [ScopesMeet, MbarScopeIncludes, SameCluster, SameCta, h0]
  · rintro ⟨hs, -⟩
    simp [he, Event.acc] at hs

/-- **Every shared-memory use completes in time**: every use is in CTA 0, its issuer's CTA,
and once CTA 0 has exited, a thread instruction finished before its thread's exit, and the
copy's write and notification before thread 0's exit (`notify_finished`). -/
theorem no_sharedLifetimeUnsafe : ¬ SharedLifetimeUnsafe L kernel [] X := by
  have hn := mbarBulk ht hX
  have bad : ∀ {v pc k}, X.get v = some ⟨pc, k⟩ → k.isMbarBulk = false → False :=
    fun he hk => by rw [hn _ _ _ he] at hk; cases hk
  rintro ⟨e, owner, hu, hbad⟩
  suffices h : owner = e.issuer.1 / L.block ∧
      (CtaExited L X owner → SharedFinished L kernel [] X e owner) by
    rcases hbad with ⟨hne, -⟩ | ⟨hx, hfin⟩
    · exact hne h.1
    · exact hfin (h.2 hx)
  rcases hu with ⟨hp, ⟨a, w, ha, hs, hcta⟩ | ⟨addr, action, ha⟩⟩ | ⟨i, s, -, ⟨pc, hi⟩, -⟩ |
    ⟨i, address, s, x, y, k, -, ⟨pc, hi⟩, -⟩ | ⟨i, address, s, -, ⟨pc, hi⟩, -⟩ |
    ⟨i, p, rfl, hfs, hst⟩
  · have hown : owner = e.issuer.1 / L.block := hcta.symm.trans (intent_local ht hX ha hs)
    refine ⟨hown, fun hx => ?_⟩
    rcases intent_cases ht hX ha with ⟨i, rfl, hi⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩
    · exact SharedFinished.of_access hX.outside hi hown.symm hx
    · simp [gA] at hs
    · simp only [Ref.issuer, Nat.zero_div] at hown
      subst hown
      have hf := notify_finished hpre ht hX hx
      exact SharedFinished.of_stage (j := (0, 3)) (q := .notify .copy) hp
        (.inr ⟨rfl, rfl, rfl, rfl, hp, hf.1⟩) hf
  · have hown : owner = e.issuer.1 / L.block := object_local ht hX ha
    refine ⟨hown, fun hx => ?_⟩
    obtain ⟨-, h⟩ := object_action_cases ht hX ha
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -, -⟩ | ⟨j, ok, -, rfl, -, -⟩
    all_goals simp only [Ref.issuer, Nat.zero_div] at hown; subst hown
    · obtain ⟨ev, he, hne⟩ := objectAction_thread ha
      exact SharedFinished.of_thread hX.outside he hne (Nat.zero_div _) hx
    · obtain ⟨ev, he, hne⟩ := objectAction_thread ha
      exact SharedFinished.of_thread hX.outside he hne (Nat.zero_div _) hx
    · exact notify_finished hpre ht hX hx
    · obtain ⟨ev, he, hne⟩ := objectAction_thread ha
      exact SharedFinished.of_thread hX.outside he hne (Nat.zero_div _) hx
  · exact (bad hi rfl).elim
  · exact (bad hi rfl).elim
  · exact (bad hi rfl).elim
  · rcases hfs with ⟨s, m, hb, -, rfl⟩ | ⟨s, hb, hm, rfl⟩ | ⟨m, noinc, ha, rfl⟩ |
      ⟨⟨d, s, accum, mask, pc, hi⟩ | ⟨c, pc, hi⟩ | ⟨s, pc, hi⟩, rfl⟩ |
      ⟨s, targets, c, ⟨pc, hi⟩, -, rfl⟩ | ⟨a, s, ⟨pc, hi⟩, rfl⟩ | ⟨a, s, ⟨pc, hi⟩, rfl⟩ |
      ⟨s, rank, m, ⟨pc, hi⟩, -, rfl⟩
    · obtain ⟨rfl, rfl⟩ := bulk_cases ht hX hb
      obtain ⟨s', m', hb', hm', hor⟩ := hst
      obtain ⟨-, rfl⟩ := bulk_cases ht hX hb'
      have hm'' : m' = mbar L.sharedBase := by simpa [copySpec, bulkSpec] using hm'.symm
      subst hm''
      have hown : owner = 0 := by
        rcases hor with ⟨-, h⟩ | ⟨h, -⟩ | h
        · simpa [copySpec, bulkSpec, buf] using h.symm
        · simp [copySpec, bulkSpec, gA] at h
        · simpa [mbar] using h.symm
      subst hown
      exact ⟨by simp [Ref.issuer], notify_finished hpre ht hX⟩
    · obtain ⟨-, rfl⟩ := bulk_cases ht hX hb
      exact (hm _ rfl).elim
    · exact (no_asyncArrive ht hX ha).elim
    all_goals exact (bad hi rfl).elim

omit hpre in
theorem no_tma_unsafe : ¬ TmaUnsafe L mem0 X := by
  rintro (⟨m, r, hr, hf⟩ | ⟨m, r, hr, hn⟩ | ⟨e, a, w, i, m, c, l, he, hi, ha, hm, -⟩ | h | h)
  · rw [object_fault_free ht hX hr] at hf
    cases hf
  · exact hn (object_published ht hX hr)
  · have hml := (mbInit_cases ht hX hi).2.1
    rw [hml] at hm
    exact intent_mbar_disjoint ht hX he ha hm
  · refine not_cpAsyncOverlap_of_none (fun i s hb => ?_) h
    obtain ⟨-, rfl⟩ := bulk_cases ht hX hb
    simp [copySpec, bulkSpec]
  · refine not_maskedRangeUnalloc_of_none (fun i s m hb => ?_) h
    obtain ⟨-, rfl⟩ := bulk_cases ht hX hb
    simp [copySpec, bulkSpec]

omit hpre in
/-- Every poll is the canonical spin. -/
theorem no_pollShapeUnsafe : ¬ PollShapeUnsafe kernel X := by
  rintro ⟨e, pc, m, q, ok, acq, sc, he, hs, -⟩
  rw [wait_pc ht hX he] at hs
  exact hs spin

omit hpre in
/-- No event is of an aligned class: no barrier, `tcgen05`, cluster barrier, register request
or warp matrix instruction. -/
theorem not_member (c : AlignedClass) {e : EvId} {ev : Event} (he : X.get e = some ev) :
    c.member ev = false ∧ c.exitMember kernel ev = false := by
  rcases (event_cases ht hX he).2 with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ |
    ⟨-, -, rfl⟩ | ⟨-, -, -, ⟨ok, rfl⟩ | ⟨i, -, -, -, ⟨bs, rfl⟩ | ⟨_, v, -, -, -, rfl⟩ | rfl |
      ⟨pc, f, rfl, -⟩⟩⟩ <;>
    cases c <;> simp [AlignedClass.member, AlignedClass.exitMember, Kernel.isAlignedCtaBar,
      isTcColl, Execution.isBar, isCluster, SetMaxNReg.isRequest, isMatrix, initE, fenceE, arriveE,
      bulkE, waitE, rdE, wrE, exE]

omit hpre in
/-- **No aligned instruction diverges or is left by an exit.** -/
theorem no_alignedMismatch : ¬ AlignedMismatch L kernel X := by
  rintro ⟨c, ⟨e, f, pe, pf, ke, kf, -, he, -, hm, -⟩ | ⟨e, f, ev, -, he, hm, -⟩⟩
  · rw [(not_member ht hX c he).1] at hm
    cases hm
  · rw [(not_member ht hX c he).2] at hm
    cases hm

/-- **No consistent execution is unsafe.** -/
theorem safe : ¬ Unsafe L kernel [] mem0 X :=
  (mbarBulk ht hX).not_unsafe hX (no_local_ub hpre ht hX) (no_unalloc hpre ht hX)
    (conflicts_ordered hpre ht hX)
    (by
      rintro (⟨g, h, i, j, id, id', count, count', pc, pc', -, hi, -⟩ | h)
      · exact no_barrier ht hX hi
      · exact hX.not_barArriveMismatch Fact.out h)
    (not_ctaBarFault hX fun _ _ _ _ _ _ _ _ h _ => (no_barrier ht hX h).elim)
    (no_tma_unsafe ht hX) (by simp) (no_alignedMismatch ht hX)
    (not_warpDivergent (by decide +kernel)) (no_sharedLifetimeUnsafe hpre ht hX)
    (no_pollShapeUnsafe ht hX) (no_mbarUninit ht hX)
    (TensorStore.not_copyReduceNoRule_of_none fun i s hb r => by
      obtain ⟨-, rfl⟩ := bulk_cases ht hX hb
      simp [copySpec, bulkSpec])

end

end PTX.Kernels.TmaCopy.Proof
