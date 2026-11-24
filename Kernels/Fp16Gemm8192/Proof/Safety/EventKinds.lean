-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # Event kinds the kernel never issues

An event at a followed state fires the template of its site's instruction, which is of the site's
kind or the allocation's request or address store (`event_tmpl`). No such template fires an atomic
read-modify-write (`no_rmw`), a bulk prefetch (`no_bulkPrefetch`), a `tcgen05.shift`
(`no_shift`), a `cp.async.mbarrier.arrive` (`no_asyncArrive`), a thread fence
(`no_threadFence`) or a warp-level matrix instruction (`no_matrix`); no event is a linear copy
(`RingEvent.copy`, `no_copy`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An event at a followed state fires a template of its state's kind, the allocation's request or
address store, or undefined behaviour. -/
theorem event_tmpl (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g k : Nat}
    {e : Event} {d : ThreadD} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) :
    ∃ pc m o, Fires pc m e o ∧ ((∃ f, m = .ub f) ∨ KindTmpl L g (nextKind d) m ∨
      (∃ grp dst n t, m = .tc (.resource grp (some dst) (.alloc n)) t) ∨
      ∃ dst t, m = .tcAllocStore dst t) := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site ht.sound hX he hσ
  refine ⟨_, _, o, hf, ?_⟩
  rcases Flow.eventTmpl_opTmpl (A := Prod) (L := L) (g := g) (t := t) ins.op with hub | hev
  · exact .inl hub
  by_cases ha : ∃ grp b o nc, ins.op = .tcAlloc grp b o nc
  · obtain ⟨grp, b, o, nc, hop⟩ := ha
    rw [hop] at hev ⊢
    rcases hev with ⟨grp', dst, n, t, h⟩ | ⟨dst, t, h⟩
    · exact .inr (.inr (.inl ⟨grp', dst, n, t, h⟩))
    · exact .inr (.inr (.inr ⟨dst, t, h⟩))
  · exact .inr (.inl (kindTmpl_of (site_kindOp d hc) hev
      fun grp b o nc hop => absurd ⟨grp, b, o, nc, hop⟩ ha))

/-- The kernel issues no atomic read-modify-write. -/
theorem no_rmw (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {e : EvId} {pc : Nat}
    {a : Acc} {o : List (Option Byte)} {n : Option (List Byte)} :
    X.get e ≠ some ⟨pc, .rmw a o n⟩ := by
  intro he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨pc', m, o', hf, h⟩ := event_tmpl hX ht he hσ
  cases m <;> simp only [Fires, Event.mk.injEq, reduceCtorEq, and_false, false_and,
    exists_false] at hf
  rcases h with ⟨f, h⟩ | h | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ <;> try cases h
  cases hn : nextKind d <;> rw [hn] at h <;> simp [KindTmpl] at h

/-- The kernel issues no `cp.async.bulk.prefetch`. -/
theorem no_bulkPrefetch (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {e : EvId}
    {a : Acc} : ¬ X.BulkPrefetch e a := by
  rintro ⟨pc, he⟩
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨pc', m, o', hf, h⟩ := event_tmpl hX ht he hσ
  cases m <;> simp only [Fires, Event.mk.injEq, reduceCtorEq, and_false, false_and,
    exists_false] at hf
  rcases h with ⟨f, h⟩ | h | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ <;> try cases h
  cases hn : nextKind d <;> rw [hn] at h <;> simp [KindTmpl] at h

/-- The kernel issues no `tcgen05.shift`. -/
theorem no_shift (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {e : EvId}
    {s : TcShift.Spec} : ¬ X.ShiftIssue e s := by
  rintro ⟨pc, he⟩
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨pc', m, o', hf, h⟩ := event_tmpl hX ht he hσ
  cases m <;> simp only [Fires, Event.mk.injEq, reduceCtorEq, and_false, false_and,
    exists_false, Kind.tc.injEq] at hf
  obtain ⟨⟨-, hk⟩, -⟩ := hf
  cases hk
  rcases h with ⟨f, h⟩ | h | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ <;> try cases h
  cases hn : nextKind d <;> rw [hn] at h <;> simp [KindTmpl] at h

/-- The kernel issues no `cp.async.mbarrier.arrive`. -/
theorem no_asyncArrive (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {e : EvId}
    {m : Loc} {noinc : Bool} : ¬ X.AsyncArrive e m noinc := by
  rintro ⟨pc, he⟩
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨pc', m', o', hf, h⟩ := event_tmpl hX ht he hσ
  cases m' <;> simp only [Fires, Event.mk.injEq, reduceCtorEq, and_false, false_and,
    exists_false] at hf
  rcases h with ⟨f, h⟩ | h | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ <;> try cases h
  cases hn : nextKind d <;> rw [hn] at h <;> simp [KindTmpl] at h

/-- The kernel issues no thread fence (`fence.sc`, `fence.acq_rel`). -/
theorem no_threadFence (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {e : EvId}
    {sem : FenceSem} {sc : MbarScope} : ¬ X.ThreadFence e sem sc := by
  rintro ⟨pc, he⟩
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨pc', m', o', hf, h⟩ := event_tmpl hX ht he hσ
  cases m' <;> simp only [Fires, Event.mk.injEq, reduceCtorEq, and_false, false_and,
    exists_false] at hf
  rcases h with ⟨f, h⟩ | h | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ <;> try cases h
  cases hn : nextKind d <;> rw [hn] at h <;> simp [KindTmpl] at h

/-- The kernel issues no warp-level matrix instruction (`ldmatrix`, `stmatrix`, `movmatrix`,
`mma.sync`). -/
theorem no_matrix (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {e : EvId}
    {ev : Event} (he : X.get e = some ev) : isMatrix ev = false := by
  obtain ⟨pc, k⟩ := ev
  cases k <;> try rfl
  rename_i op own recv
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨pc', m', o', hf, h⟩ := event_tmpl hX ht he hσ
  cases m' <;> simp only [Fires, Event.mk.injEq, reduceCtorEq, and_false, false_and,
    exists_false] at hf
  rcases h with ⟨f, h⟩ | h | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ <;> try cases h
  cases hn : nextKind d <;> rw [hn] at h <;> simp [KindTmpl] at h

/-- The kernel issues no linear copy (`RingEvent.copy`). -/
theorem no_copy (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {i : EvId}
    {s : AsyncCopy.Spec} : ¬ X.Copy i s := by
  rintro ⟨pc, he⟩
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  exact (ht.ring_event (Frame.lt_of_get hX he) he hσ).copy s rfl

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
