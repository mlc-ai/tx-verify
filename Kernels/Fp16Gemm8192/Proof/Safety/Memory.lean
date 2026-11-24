-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.MemoryAccess
public import Kernels.Fp16Gemm8192.Proof.Safety.Tma

@[expose] public section

/-! # The memory branches of `Unsafe`, from the interface

Every byte an access touches is in a region whose protocol orders its conflicting accesses
(`conflicts_ordered`), so there is no race and no mixed-size conflict (`no_race`, `no_mixed`):

* a shared byte is in a launched CTA's window, in one region (`SharedWindow`): the Tensor Memory
  base word (`BaseOrdered`), the CLC response buffer (`ResponseOrdered`), the input stages
  (`InputOrdered`) or the staging buffers (`StagingOrdered`);
* a global byte is read only from the `A` and `B` matrices and written only to the disjoint `D`
  matrix, by the tensor stores of distinct output tiles (`global_ordered`, `OutputUnique`).

Every touched byte is allocated (`no_unalloc`): a shared byte is in the window of a launched CTA,
allocated by `Pre.sharedAllocated`; a global byte is in one of the three matrices, allocated by
`Pre.inputA`, `Pre.inputB` and `Pre.outputAllocated`; the kernel makes no non-coherent read
(`ThreadFacts.no_nc`). Every mbarrier operand is allocated (`usesMbar_allocated`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety.Memory

open PTX AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The shared bytes are ordered**, region by region. -/
theorem shared_ordered (hwin : SharedWindow L X) (hb : BaseOrdered L X)
    (hr : ResponseOrdered L X) (hin : InputOrdered L X) (hst : StagingOrdered L X) :
    ConflictsOrdered L X fun l => l.space = .shared := by
  intro e f a b l hc ha hb' hs
  obtain ⟨-, we, -, he, -⟩ := id hc
  rcases (hwin e a we l he ha hs).2 with h | h | h | h
  · exact hb e f a b l hc ha hb' h
  · exact hr e f a b l hc ha hb' h
  · exact hin e f a b l hc ha hb' h
  · exact hst e f a b l hc ha hb' h

/-- **Every byte is ordered**: conflicting accesses of a byte are ordered at it. -/
theorem conflicts_ordered (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hwin : SharedWindow L X) (hb : BaseOrdered L X)
    (hr : ResponseOrdered L X) (hin : InputOrdered L X) (hst : StagingOrdered L X)
    (hout : OutputUnique X) : ConflictsOrdered L X fun _ => True :=
  ((shared_ordered hwin hb hr hin hst).or (global_ordered hpre hX ht hout)).mono fun l _ =>
    Classical.em (l.space = .shared)

/-- **No race.** -/
theorem no_race (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hwin : SharedWindow L X) (hb : BaseOrdered L X)
    (hr : ResponseOrdered L X) (hin : InputOrdered L X) (hst : StagingOrdered L X)
    (hout : OutputUnique X) : ¬ Race L X :=
  (conflicts_ordered hpre hX ht hwin hb hr hin hst hout).no_race

/-- A byte of an input matrix holds its element's byte at launch. -/
theorem input_allocated (hpre : Pre P L mem0) {l : Loc}
    (h : InMatrix P.aBase l ∨ InMatrix P.bBase l) : mem0 l ≠ none := by
  have key : ∀ base, InMatrix base l → ∃ row < 8192, ∃ col < 8192, ∃ byte < 2,
      (elementLoc base row col).at byte = l := by
    rintro base ⟨hs, hc, hlo, hhi⟩
    unfold matrixBytes at hhi
    refine ⟨(l.addr - base) / 16384, by omega, (l.addr - base) % 16384 / 2, by omega,
      (l.addr - base) % 2, by omega, ?_⟩
    obtain ⟨sp, cta, addr⟩ := l
    simp only at hs hc hlo hhi
    subst hs hc
    simp only [elementLoc, Loc.at, Loc.mk.injEq, true_and]
    omega
  rcases h with h | h
  · obtain ⟨row, hr, col, hc, byte, hb, rfl⟩ := key _ h
    rw [hpre.inputA row hr col hc byte hb]
    simp
  · obtain ⟨row, hr, col, hc, byte, hb, rfl⟩ := key _ h
    rw [hpre.inputB row hr col hc byte hb]
    simp

/-- A byte of the output matrix is allocated. -/
theorem output_allocated (hpre : Pre P L mem0) {l : Loc} (h : InMatrix P.dBase l) :
    mem0 l ≠ none := by
  obtain ⟨hs, hc, hlo, hhi⟩ := h
  have hh := hpre.outputAllocated (l.addr - P.dBase) (by omega)
  obtain ⟨sp, cta, addr⟩ := l
  simp only at hs hc hlo hhi
  subst hs hc
  rwa [show P.dBase + (addr - P.dBase) = addr by omega] at hh

/-- A byte of a launched CTA's shared window is allocated. -/
theorem window_allocated (hpre : Pre P L mem0) {l : Loc} (hs : l.space = .shared)
    (hc : l.cta < L.grid) (hlo : L.sharedBase ≤ l.addr)
    (hhi : l.addr < L.sharedBase + sharedBytes) : mem0 l ≠ none := by
  have hh := hpre.sharedAllocated l.cta hc (l.addr - L.sharedBase) (by omega)
  obtain ⟨sp, cta, addr⟩ := l
  simp only at hs hc hlo hhi
  subst hs
  rwa [show L.sharedBase + (addr - L.sharedBase) = addr by omega] at hh

/-- **Every touched byte is allocated.** -/
theorem no_unalloc (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hwin : SharedWindow L X) : ¬ Unalloc mem0 X := by
  rintro (⟨e, a, l, htouch, hc, hnone⟩ | ⟨e, m, l, hu, hcov, hnone⟩)
  swap
  · exact usesMbar_allocated hpre hX ht hu hcov hnone
  rcases htouch with ⟨w, hi⟩ | ⟨i, bs, rfl, pc, hget⟩
  · by_cases hsp : l.space = .shared
    · obtain ⟨hcta, hreg⟩ := hwin e a w l hi hc hsp
      have hb : L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + sharedBytes := by
        unfold sharedBytes
        rcases hreg with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
      exact window_allocated hpre hsp hcta hb.1 hb.2 hnone
    · rcases global_access hpre hX ht hi hc hsp with ⟨-, h⟩ | ⟨-, h, -⟩
      · exact input_allocated hpre h hnone
      · exact output_allocated hpre h hnone
  · obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    exact ht.no_nc (Frame.lt_of_get hX hget) hget hσ rfl

end PTX.Kernels.Fp16Gemm8192.Proof.Safety.Memory
