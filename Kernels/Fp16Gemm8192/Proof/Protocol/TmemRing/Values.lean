-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.RingRecords
public import Lemmas.Tcgen05.TcMmaSource
public import Lemmas.Tcgen05.TcMmaResultLayout
public import Lemmas.Assumption.Facts

@[expose] public section

/-! # The values of the accumulator ring

The only Tensor Memory writers of the kernel are its MMAs, of the operands `InputRing.mmaSpec`
(no Tensor Memory store or copy is issued). Their output layout is the full-datapath layout of a
CTA pair, rows `0..127` in the low CTA and `128..255` in the high one, so it is injective in the
matrix coordinate (`layout_injective`), and the value they leave in a cell is a single-precision
float (`wrote_f32`, FP16 inputs with FP32 accumulation under the ideal-real profile): the export
`TmemWords` (`tmemWords`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof TcMma

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An MMA of the kernel is an MMA thread's, of the operands `mmaSpec` of its CTA and warp. -/
theorem mma_spec (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {i : EvId}
    {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i d s acc mask) :
    ∃ sl j : Nat, s = InputRing.mmaSpec L (i.1 / L.block) (i.1 % L.block / 32) sl j := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨g, k⟩ := i
  have hg := Frame.lt_of_get hX he
  obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨-, sl, j, -, -, -, hs, -⟩ := ht.mma_issue hg he hσ rfl
  exact ⟨sl.val, j.val, hs⟩

/-- The pair layout is injective in the matrix coordinate. -/
theorem resultCell_inj {L : Launch} {cta w sl j base r c r' c' : Nat} {cell : Cell}
    (h1 : resultCell (InputRing.mmaSpec L cta w sl j) base r c = some cell)
    (h2 : resultCell (InputRing.mmaSpec L cta w sl j) base r' c' = some cell) :
    r = r' ∧ c = c' := by
  have hm : (InputRing.mmaSpec L cta w sl j).descriptor.m =
      128 * (InputRing.mmaSpec L cta w sl j).descriptor.group.size := rfl
  have hlo : (InputRing.mmaSpec L cta w sl j).lowCta ≠
      (InputRing.mmaSpec L cta w sl j).highCta := by
    simp [InputRing.mmaSpec]
  unfold resultCell at h1 h2
  simp only [hm, ↓reduceIte] at h1 h2
  split_ifs at h1 h2
  all_goals
    simp only [Option.some.injEq] at h1 h2
    subst h1
    simp only [InputRing.mmaSpec, InputRing.mmaDescriptor, CtaGroup.size, Cell.mk.injEq] at *
    obtain ⟨h3, h4, h5⟩ := h2
    constructor <;> omega

/-- **The kernel's MMA output layouts are injective.** -/
theorem layout_injective (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    LayoutInjective X := by
  intro i d s acc mask hi row col row' col' cell h1 h2
  obtain ⟨sl, j, rfl⟩ := mma_spec hX ht hi
  exact resultCell_inj (writeCell_resultCell h1) (writeCell_resultCell h2)

/-- **An MMA result of the kernel is a single-precision float.** -/
theorem result_f32 (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {i : EvId}
    {cell : Cell} {v : Value} (h : Result L Prod X i cell v) : ∃ r, v = .float .f32 r := by
  cases h with
  | overwrite hi _ _ ha =>
    obtain ⟨sl, j, rfl⟩ := mma_spec hX ht hi
    exact eval_f16 rfl (List.mem_singleton.mpr rfl) ha
  | accumulate hi _ _ _ _ ha =>
    obtain ⟨sl, j, rfl⟩ := mma_spec hX ht hi
    exact eval_f16 rfl (List.mem_singleton.mpr rfl) ha
  | accumulateStored hi _ _ _ _ ha =>
    obtain ⟨sl, j, rfl⟩ := mma_spec hX ht hi
    exact eval_f16 rfl (List.mem_singleton.mpr rfl) ha

/-- **Every value a Tensor Memory write of the kernel leaves is a single-precision float**: the
writes are MMAs, and a shift moves the value of a write. -/
theorem wrote_f32 (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {s : EvId}
    {cell : Cell} {v : Value} (h : Wrote L Prod X s cell v) : ∃ r, v = .float .f32 r := by
  have base : ∀ {s : EvId} {cell : Cell} {v : Value}, (Result L Prod X s cell v ∨
      StoreValue L X s cell v ∨ CpValue X s cell v) → ∃ r, v = .float .f32 r := by
    rintro s cell v (h | ⟨a, vals, sh, j, ⟨pc, he⟩, -⟩ |
      ⟨c, k, cta, ops, row, col, lane, ⟨pc, he⟩, -⟩)
    · exact result_f32 hX ht h
    · have hg := Frame.lt_of_get hX he
      obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
      exact absurd rfl (ht.no_tc_st hg he hσ)
    · have hg := Frame.lt_of_get hX he
      obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
      exact absurd rfl (ht.no_tc_cp hg he hσ)
  rcases h with h | h | h | ⟨src, fr, -, h⟩
  · exact base (.inl h)
  · exact base (.inr (.inl h))
  · exact base (.inr (.inr h))
  · exact base h

/-- **The accumulator ring's values** (`TmemWords`). -/
theorem tmemWords (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    TmemWords L X :=
  ⟨layout_injective hX ht, fun _ _ _ h => wrote_f32 hX ht h⟩

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
