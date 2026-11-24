-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaAccessWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources

public section

/-! # All Tensor Memory writers leave whole 32-bit words -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow TcMma Wg1Mma MmaDataTrace

private theorem copied_word_bytes {c : TcCopy.Spec} {bs : List (Option Byte)}
    {row col : Nat} {v : Value} (h : TcCopy.cpWord c bs row col = some v) : v.bytes = 4 := by
  cases hc : c.fmt
  · rw [TcCopy.cpWord_none hc] at h
    unfold TcCopy.word at h
    cases h0 : bs.getD (row * c.shape.rowBytes + 4 * col) none <;>
      simp only [h0, bind, Option.bind, reduceCtorEq] at h
    cases h1 : bs.getD (row * c.shape.rowBytes + 4 * col + 1) none <;>
      simp only [h1, reduceCtorEq] at h
    cases h2 : bs.getD (row * c.shape.rowBytes + 4 * col + 2) none <;>
      simp only [h2, reduceCtorEq] at h
    cases h3 : bs.getD (row * c.shape.rowBytes + 4 * col + 3) none <;>
      simp only [h3, reduceCtorEq] at h
    cases h
    rfl
  · simp only [TcCopy.cpWord, hc, TcCopy.decompressedWord, bind, Option.bind] at h
    split at h <;> cases h
    rfl

/-- Any represented write with a Tensor Memory value supplies a whole word. -/
theorem tmem_wrote_bytes {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g i : Nat} {cell : Cell} {v : Value}
    (h : Wrote L Assumptions.all X (g, i) cell v) : v.bytes = 4 := by
  have descKind {dst : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
      (hi : X.MmaIssue (g, i) dst s acc mask) : s.descriptor.kind = .f16 .bf16 .f32 := by
    rcases (MmaAccessWindow.mma_spec hpre hX hs ht hi).2 with
      ⟨_, _, _, rfl, _, _⟩ | ⟨_, _, _, rfl, _, _⟩ <;> rfl
  rcases h with hResult | hStore | hCopy | hShift
  · have isFP32 : ∃ r, v = .float .f32 r := by
      cases hResult with
      | overwrite hi _ _ hEval => exact Wg0ScoreSources.bf16_eval_f32 (descKind hi) hEval
      | accumulate hi _ _ _ _ hEval => exact Wg0ScoreSources.bf16_eval_f32 (descKind hi) hEval
      | accumulateStored hi _ _ _ _ hEval => exact Wg0ScoreSources.bf16_eval_f32 (descKind hi) hEval
    obtain ⟨r, rfl⟩ := isFP32
    rfl
  · obtain ⟨address, vals, shape, j, ⟨tag, he⟩, hj, _⟩ := hStore
    have hg := Frame.lt_of_get hX he
    obtain ⟨_, _, _, hFire⟩ :=
      RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by simp)
    have hFields := Wg0ScoreSources.writer_fields hpre hg hFire
      (.inr (.inr (.inl ⟨address, vals, shape, rfl⟩)))
    rcases hFields with ⟨d, tile, _, _, hKind⟩ | ⟨_, _, _, _, hKind⟩ |
      ⟨_, _, _, _, hKind⟩ | ⟨_, _, _, _, hKind⟩
    · obtain ⟨_, rfl, _⟩ := TcKind.st.inj (Kind.tc.inj hKind)
      obtain ⟨word, _, rfl⟩ := List.mem_map.mp
        (show v ∈ (List.range 64).map (Wg0.rescaleValue d) from List.mem_of_getElem? hj)
      rfl
    all_goals cases hKind
  · obtain ⟨c, k, cta, op, row, col, lane, _, _, _, _, _, _, _, hWord⟩ := hCopy
    exact copied_word_bytes hWord
  · obtain ⟨_, _, ⟨⟨s, hi, _⟩, _, _, _⟩, _⟩ := hShift
    exact (Wg0ScoreSources.no_shift_issue hpre hX hs ht hi).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
