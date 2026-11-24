-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.OutProb
public import Kernels.InklingRelDecode.Proof.Interface.ResultThreads

@[expose] public section

/-!
# The words the epilogue stores are `Spec`'s output (result layer, part 2b)

The epilogue (`Epi`) starts from the registers the softmax region leaves (`Br.In`, turned into
the epilogue's `Prm` by the bridge, `Br.prm`) and from the 64 words of the `O` tile its
`tcgen05.ld` returned (`D.o`). It stores `LsePart` once (`Prm.lseWord`) and `OPart` as 64 words
(`D.word`). `RowIn` says what the softmax region leaves for the row: the scale `scale_log2`, the
row sum `l` and the row maximum `m` are those of `rowState`, the state `Softmax.run` reaches over
the blocks of the row (`OutRow.lean`). From it, and from the `O` words being `colState`'s numerator:

* `eq0_iff`: the zero test of the row sum holds exactly for an empty row;
* `word_oPart`: word `k` of `OPart` is the f32 float of `Spec.oPart` (`rcp.approx` is the exact
  reciprocal by `Assumptions.approx`; `l = 0` is replaced by `1`, so an empty row stores `0 · 1`);
* `word_sk`: on the `num_iters < 1` path (no load, products of zero pairs) every word is the zero
  word, and so is `Spec.oPart`;
* `lseWord_oPart`, `lseWord_empty`: the word of `LsePart` is the f32 float of `Spec.lsePart`
  (`lg2` and `fma` by `Assumptions.lg2Exact` and `idealArith`, `Br.lse_fin`), and for an empty row
  the `-inf` pattern.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof

noncomputable section

/-- **What the softmax region leaves for the row** (the bridge's input `Br.In`): the scale is
`scale_log2`, the row sum is the running sum of `Softmax.run` over the blocks of the row, and the
row maximum is its running maximum. -/
structure RowIn (P : Params) (i : Br.In) (r s tok head : Nat) : Prop where
  sc : i.sc = .float .f32 (sl P)
  l : valFloat .f32 i.l = .ok (rowState P r s tok head).l
  mx : i.mx = Assumption.erealValue .f32 (rowState P r s tok head).m

variable {P : Params} {i : Br.In} {r s tok head : Nat}

/-- **The zero test of the row sum holds exactly when the row sum is zero.** -/
theorem eq0_iff (h : RowIn P i r s tok head) :
    (Br.prm i).eq0 = decide ((rowState P r s tok head).l = 0) := by
  have h3 : setpE (.unord .eq) false i.l Epi.zero32 =
      .ok (erealCompare .eq ((rowState P r s tok head).l : EReal) ((0 : ℝ) : EReal)) :=
    setpE_fin (Or.inr rfl) h.l valFloat_zero
  show i.eq0 = _
  simp only [Br.In.eq0, h3, erealCompare, EReal.coe_eq_coe_iff]

/-- **The reciprocal the epilogue multiplies by**: `1 / l`, or `1` for a zero row sum. -/
theorem inv_eq (h : RowIn P i r s tok head) :
    (Br.prm i).inv = fl (1 / (if (rowState P r s tok head).l = 0 then 1
      else (rowState P r s tok head).l)) := by
  have hp : (Br.prm i).l = i.l := rfl
  by_cases h0 : (rowState P r s tok head).l = 0
  · have he : (Br.prm i).eq0 = true := by simp [eq0_iff h, h0]
    have := Epi.inv_fin (Br.prm i) (x := 1) (by simp only [he, ite_true]; exact valFloat_one)
      one_ne_zero
    simpa [h0] using this
  · have he : (Br.prm i).eq0 = false := by simp [eq0_iff h, h0]
    have := Epi.inv_fin (Br.prm i) (x := (rowState P r s tok head).l)
      (by simp only [he, Bool.false_eq_true, ite_false, hp]; exact h.l) h0
    simpa [h0] using this

/-- **A stored word of `OPart`**: if the 64 loaded words are the f32 floats of the numerators of
the row's columns `col0 + k` (the `O` tile), word `k` is the f32 float of `Spec.oPart`. -/
theorem word_oPart (hs : 0 < P.scale) (hsp : 0 < P.splits) (h : RowIn P i r s tok head)
    {d : Epi.D} (hpr : { d.pr with bw := 0 } = Br.prm i) (hsk : d.sk = false) {col0 : Nat}
    (hc : ∀ k < 64, d.o.getD k (b32 0) = fl (colState P r s tok head (col0 + k)).o)
    {k : Nat} (hk : k < 64) : d.word k = fl (oPart P r s tok head (col0 + k)) := by
  have hy : d.pr.inv = fl (1 / (if (rowState P r s tok head).l = 0 then 1
      else (rowState P r s tok head).l)) := by
    show ({ d.pr with bw := 0 } : Epi.Prm).inv = _
    rw [hpr]; exact inv_eq h
  rw [Epi.word_fin d hsk hc hy hk]
  congr 1
  by_cases h0 : rowSum P r s tok head = 0
  · obtain ⟨hl, -, ho, hp⟩ := row_empty hs hsp r s tok head (col0 + k) h0
    rw [hp, ho, hl]
    simp
  · obtain ⟨hl, -, hn, -⟩ := row_nonempty hs hsp r s tok head (col0 + k) h0
    have hne := hl.ne'
    rw [← hn]
    simp only [hne, ↓reduceIte]
    ring

/-- **On the `num_iters < 1` path** every stored word of `OPart` is the zero word. -/
theorem word_sk {d : Epi.D} (hsk : d.sk = true) (k : Nat) : d.word k = b32 0 := by
  unfold Epi.D.word Epi.D.prod
  simp only [hsk, ite_true]
  split_ifs <;> rfl

/-- **The word of `LsePart` of a non-empty row** is the f32 float of `Spec.lsePart`. -/
theorem lseWord_lsePart (hs : 0 < P.scale) (hsp : 0 < P.splits) (h : RowIn P i r s tok head)
    {d : Epi.D} (hpr : { d.pr with bw := 0 } = Br.prm i) (hne : rowSum P r s tok head ≠ 0)
    (d0 : Nat) : d.pr.lseWord = fl (lsePart P r s tok head) := by
  obtain ⟨hl, ⟨M, hM⟩, -, hlse⟩ := row_nonempty hs hsp r s tok head d0 hne
  have he : (Br.prm i).eq0 = false := by simp [eq0_iff h, hl.ne']
  have hsc : valFloat .f32 i.sc = .ok (sl P) := by rw [h.sc]; exact valFloat_float
  have hmx : valFloat .f32 i.mx = .ok M := by
    rw [h.mx, hM, erealValue_coe]; exact valFloat_float
  obtain ⟨-, -, hlseval⟩ := Br.lse_fin i h.l hl hsc hmx
  show ({ d.pr with bw := 0 } : Epi.Prm).lseWord = _
  rw [hpr]
  unfold Epi.Prm.lseWord
  rw [he]
  simp only [Bool.false_eq_true, ite_false]
  show i.lse = _
  rw [hlseval, ← hlse, hM, EReal.toReal_coe]
  congr 1
  ring

/-- **An empty row stores the `-inf` pattern**: the zero test of its row sum holds. -/
theorem eq0_of_empty (h : RowIn P i r s tok head) (hs : 0 < P.scale) (hsp : 0 < P.splits)
    (h0 : rowSum P r s tok head = 0) (d0 : Nat) : (Br.prm i).eq0 = true := by
  obtain ⟨hl, -⟩ := row_empty hs hsp r s tok head d0 h0
  simp [eq0_iff h, hl]

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Out
