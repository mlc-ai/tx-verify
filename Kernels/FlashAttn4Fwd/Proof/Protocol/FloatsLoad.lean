-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Floats
public import Lemmas.Assumption.Facts

@[expose] public section

/-! # Every Tensor Memory load returns single-precision floats

A register of a Tensor Memory load returns a word that contains the value its read source wrote
(DEP-TC-LOAD-VALUE, `LoadReadOk`). Each register's source is an MMA (`LoadSources`): a softmax load
reads the last QK MMA of its tile (`Score.s_readSource`), a correction load the last PV MMA of the
previous tile (`OAcc.o_readSource`). An MMA result is the ideal `kind::f16` MMA's value with an f32
accumulator (assumption `fa4-fwd-ideal-arith`, `FloatFacts.mma_kind`; `TcMma.eval_f16`), a
single-precision float (`wrote_f32`; the kernel has no `tcgen05.cp`, `ScoreFacts.no_cp`, and a
store is not an MMA).

An f32 value fills its word, so the loaded word is that value (`load_floats`). No load reads a
word written by a `tcgen05.st` of the softmax or correction threads (packed f16 pairs of `P`, the
rescaled f32 accumulator, which the next PV MMA reads), which `LoadSources` states. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof TcMma

noncomputable section

namespace Floats

variable {L : Launch} {X : Execution} {K : Kernel} {mem0 : Mem0}

/-- Each register of a Tensor Memory load has a read source that is an MMA, with the value the
MMA wrote there. -/
def LoadSources (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a j : Nat} {vals : List Value}, h < L.threads → X.TLd (h, i) a vals .s32x32b →
    j < vals.length →
    ∃ src value, ReadSource L X .ld src (h, i) (tcDataCell32 L h a j) ∧
      Wrote L asms X src (tcDataCell32 L h a j) value ∧ IsMma X src

/-- **An MMA result of the kernel is a single-precision float.** -/
theorem result_f32 (hf : FloatFacts L X) {i : EvId} {cell : Cell} {v : Value}
    (h : Result L asms X i cell v) : ∃ r, v = .float .f32 r := by
  cases h with
  | overwrite hi _ _ ha =>
    exact eval_f16 (hf.mma_kind hi) (by rw [hf.mma_kind hi]; exact List.mem_singleton.mpr rfl) ha
  | accumulate hi _ _ _ _ ha =>
    exact eval_f16 (hf.mma_kind hi) (by rw [hf.mma_kind hi]; exact List.mem_singleton.mpr rfl) ha
  | accumulateStored hi _ _ _ _ ha =>
    exact eval_f16 (hf.mma_kind hi) (by rw [hf.mma_kind hi]; exact List.mem_singleton.mpr rfl) ha

/-- **The value an MMA leaves in a cell is a single-precision float.** -/
theorem wrote_f32 (ht : ScoreFacts L X) (hf : FloatFacts L X) {src : EvId} {cell : Cell}
    {v : Value} (h : Wrote L asms X src cell v) (hsrc : IsMma X src) :
    ∃ r, v = .float .f32 r := by
  rcases h with h | ⟨a, vals, sh, j, ⟨pc', hs⟩, -, -⟩ | ⟨c, k, cta, ops, row, col, lane, hcp, -⟩ |
      ⟨source, fr, ⟨⟨sp, hsh, -⟩, -⟩, -⟩
  · exact result_f32 hf h
  · obtain ⟨d, s, acc, mask, pc, hm⟩ := hsrc
    rw [hs] at hm
    cases hm
  · exact (ht.no_cp _ _ hcp).elim
  · exact (ht.no_shift _ _ hsh).elim

/-- **Every Tensor Memory load returns single-precision floats.** -/
theorem load_floats (hX : Consistent L K asms mem0 X) (ht : ScoreFacts L X)
    (hf : FloatFacts L X) (hs : LoadSources L X) {g k pc a : Nat} {vals : List Value}
    (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩) :
    F32s vals := by
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  obtain ⟨src, value, hrs, hwr, hsrc⟩ := hs hg ⟨pc, he⟩ hj
  obtain ⟨word, hword, hc⟩ :=
    hX.tcRead.1 _ a vals _ j src _ value ⟨pc, he⟩ (loadCell32 ⟨pc, he⟩ hj) hrs hwr
  obtain ⟨r, rfl⟩ := wrote_f32 ht hf hwr hsrc
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hword
  rw [hword]
  rcases hc with ⟨-, rfl⟩ | ⟨hb, -⟩
  · exact ⟨r, rfl⟩
  · simp [Value.bytes, FloatFmt.bytes] at hb

end Floats

end
end PTX.Kernels.FlashAttn4Fwd.Proof
