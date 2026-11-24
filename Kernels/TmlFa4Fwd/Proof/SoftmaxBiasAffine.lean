-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasWiden
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWeights
public import Kernels.TmlFa4Fwd.Flow.Code.Part056
public import Kernels.TmlFa4Fwd.Flow.Code.Part082
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Flow.SplitJoin

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

/-- A pair of BF16 biases is widened, packed and fused with the two QK scores. -/
structure BiasAffineItem where
  biasLow : Nat
  biasHigh : Nat
  widenedLow : Nat
  widenedHigh : Nat
  packed : Nat
  qk : Nat
  result : Nat

def BiasAffineItem.instructions (i : BiasAffineItem) (scaleReg : Nat) : List Instr :=
  [⟨none, biasConvertOp i.widenedLow i.biasLow⟩,
   ⟨none, biasConvertOp i.widenedHigh i.biasHigh⟩,
   ⟨none, .move ⟨.pack, .int .b 64, [some i.packed], [.reg i.widenedLow, .reg i.widenedHigh]⟩⟩,
   ⟨none, fma2Op i.result i.packed scaleReg i.qk⟩]

variable {l : Launch}

private theorem preservesPairRead {g r : Nat} {t u : TState} (h : u.regs r = t.regs r) :
    readERealPair l g u (.reg r) = readERealPair l g t (.reg r) := by
  simp [readERealPair, readValue, readReg, h]

/-- The four decoded instructions produce the biased QK pair, keeping each masked lane at
negative infinity and each finite lane at `QK + inverseScale * bias`. -/
theorem biasAffineItemRun {g pc scaleReg : Nat} {t : TState} (i : BiasAffineItem) {x y : Option ℝ}
    {scale dot₀ dot₁ : ℝ} (hs : 0 < scale) (ht : At t pc [])
    (hCode : ∀ j < 4, kernel.code[pc + j]? = (i.instructions scaleReg)[j]?)
    (hSites : pc ∈ Assumptions.biasWidenSites ∧ pc + 1 ∈ Assumptions.biasWidenSites)
    (hOff : ∀ j < 4, pc + j ∉ Assumptions.swExp2Sites)
    (hLow : t.regs i.biasLow = some (biasValue x)) (hHigh : t.regs i.biasHigh = some (biasValue y))
    (hReg : i.widenedLow ≠ i.widenedHigh ∧ i.widenedLow ≠ i.biasHigh)
    (hKeep : ∀ r ∈ [scaleReg, i.qk], r ∉ [i.widenedLow, i.widenedHigh, i.packed])
    (hScale : readERealPair l g t (.reg scaleReg) = some (.ok ((scale : EReal), (scale : EReal))))
    (hDot : readERealPair l g t (.reg i.qk) = some (.ok ((dot₀ : EReal), (dot₁ : EReal)))) :
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧ At u (pc + 4)
      [(i.result, .pair (scoreValue (affineScore scale dot₀ x))
        (scoreValue (affineScore scale dot₁ y)))] ∧
      ∀ r ∉ [i.widenedLow, i.widenedHigh, i.packed, i.result], u.regs r = t.regs r := by
  let t₁ := next (setReg t i.widenedLow (scoreValue x))
  let t₂ := next (setReg t₁ i.widenedHigh (scoreValue y))
  let pair := joinValue (scoreValue x) (scoreValue y)
  let t₃ := next (setReg t₂ i.packed pair)
  let u := next (setReg t₃ i.result
    (.pair (scoreValue (affineScore scale dot₀ x)) (scoreValue (affineScore scale dot₁ y))))
  have hp₁ : t₁.pc = pc + 1 := by change t.pc + 1 = _; rw [ht.1]
  have hp₂ : t₂.pc = pc + 2 := by change t₁.pc + 1 = _; rw [hp₁]
  have hp₃ : t₃.pc = pc + 3 := by change t₂.pc + 1 = _; rw [hp₂]
  have hf : t.fault = none := ht.2.2.2.1
  have ha₁ : At t₁ (pc + 1) [] := ⟨hp₁, ht.2.1, ht.2.2.1, hf, trivial⟩
  have h₀ : run kernel Assumptions.all l g 1 t = some t₁ := by
    apply widenBiasRun ht (by simpa [BiasAffineItem.instructions] using hCode 0 (by decide))
      hSites.1 (by simpa using hOff 0 (by decide)) x hLow
  have h₁ : run kernel Assumptions.all l g 1 t₁ = some t₂ := by
    apply widenBiasRun ha₁ (hCode 1 (by decide)) hSites.2 (hOff 1 (by decide)) y
    simp [t₁, next, setReg, hHigh, Function.update_of_ne hReg.2.symm]
  have hPackReads :
      t₂.regs i.widenedLow = some (scoreValue x) ∧ t₂.regs i.widenedHigh = some (scoreValue y) := by
    simp [t₂, t₁, next, setReg, Function.update_of_ne hReg.1]
  have h₂ : run kernel Assumptions.all l g 1 t₂ = some t₃ := by
    let op : Op := .move
      ⟨.pack, .int .b 64, [some i.packed], [.reg i.widenedLow, .reg i.widenedHigh]⟩
    have hAt : At t₂ (pc + 2) [] := ⟨hp₂, ht.2.1, ht.2.2.1, hf, trivial⟩
    apply run_local (op := op) (hCode 2 (by decide)) rfl hAt
    rw [Assumptions.execLocalA_all_eq_numeric,
      Assumptions.execLocalA_eq_nil (hp₂ ▸ hOff 2 (by decide)) rfl]
    have hPack := exec_pack (A := []) (L := l) (g := g) (d := i.packed)
      (by simp [NoPack]) hPackReads.1 hPackReads.2 SegFreePc.nil
    simpa only [scoreValue_bytes, and_self, ↓reduceIte] using hPack
  have hFrame₃ (r : Nat) (hn : r ∉ [i.widenedLow, i.widenedHigh, i.packed]) :
      t₃.regs r = t.regs r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp [t₃, t₂, t₁, next, setReg, Function.update_of_ne hn.1,
      Function.update_of_ne hn.2.1, Function.update_of_ne hn.2.2]
  have h₃ : run kernel Assumptions.all l g 1 t₃ = some u := by
    apply run_step (n := 0) (by rw [hp₃]; exact hCode 3 (by decide)) rfl
      (show t₃.fault = none from hf)
    have hFree := (Assumptions.numeric_segSites.pc (hOff 3 (by decide))).tail
    apply execMaskedFma hs (by simp [t₃, next, setReg, pair])
      ((preservesPairRead (l := l) (g := g) (hFrame₃ scaleReg (hKeep _ (by simp)))).trans hScale)
      ((preservesPairRead (l := l) (g := g) (hFrame₃ i.qk (hKeep _ (by simp)))).trans hDot)
    rw [hp₃]
    intro a ha l' g' t' hp
    rcases List.mem_append.mp ha with ha | hInput
    · rcases List.mem_append.mp ha with hNum | hSync
      · exact hFree a hNum l' g' t' hp
      · simp only [Assumptions.synchronization, List.mem_cons, List.not_mem_nil, or_false] at hSync
        rcases hSync with rfl | rfl | rfl | rfl <;> rfl
    · obtain rfl := List.mem_singleton.mp hInput
      rfl
  refine ⟨u, run_comp h₀ (run_comp h₁ (run_comp h₂ h₃)), ⟨?_, ht.2.1, ht.2.2.1,
    hf, by simp [u, next, setReg], trivial⟩, ?_⟩
  · change t₃.pc + 1 = _
    rw [hp₃]
  · intro r hn
    have hR : r ≠ i.result := by intro hr; apply hn; simp [hr]
    have hOld : r ∉ [i.widenedLow, i.widenedHigh, i.packed] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn ⊢
      exact ⟨hn.1, hn.2.1, hn.2.2.1⟩
    simpa [u, next, setReg, Function.update_of_ne hR] using hFrame₃ r hOld

/-- A packed dot product in its original GQA key order. -/
def queryKeyDot (p : Params) (b h row key : Nat) : ℝ :=
  ∑ d ∈ Finset.range 128,
    p.q (p.qOffset b + row) h d * p.k (p.page b (key / 16)) (h / 6) (key % 16) d

/-- The biased dot product at a physically backed bias column is the row's masked logit. -/
theorem biasedLogit_eq {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {b h row key : Nat} (hb : b < p.batch) (hr : row < p.qLength b) (hh : h < p.heads)
    (hc₀ : 0 ≤ p.biasColumn b row key) (hc₁ : p.biasColumn b row key < 1280) :
    affineScore (abiFloat p.invScaleBits) (queryKeyDot p b h row key)
      (p.bias (p.qOffset b + row) h (p.biasColumn b row key).toNat) =
      maskedLogit p b h row key := by
  have hMask := hp.biasMask b hb row hr h hh key hc₀ hc₁
  cases hValue : p.bias (p.qOffset b + row) h (p.biasColumn b row key).toNat with
  | none =>
    have hn : ¬ key < p.keyCount b row := by simpa [hValue] using hMask.symm
    simp [maskedLogit, affineScore, hn]
  | some bb =>
    have hy : key < p.keyCount b row := by simpa [hValue] using hMask.symm
    have hd : score p b h row key = abiFloat p.scaleLog2Bits *
        (queryKeyDot p b h row key + abiFloat p.invScaleBits * bb) := by
      simp [score, queryKeyDot, hc₀, hc₁, hValue]
    rw [maskedLogit, ite_eq_left hy, hd, mul_comm (abiFloat p.scaleLog2Bits),
      mul_div_cancel_right₀ _ (ne_of_gt (scalePositive hp).1)]
    simp [affineScore, mul_comm, add_comm]

private theorem firstBiasPairWordRun {g : Nat} {t : TState} {x y : Option ℝ} {scale dot₀ dot₁ : ℝ}
    {word : Value} (hs : 0 < scale) (ht : At t 3593 []) (hWordBytes : word.bytes = 4)
    (hScaleRead : valFloat .f32 (splitValue 64 (joinValue word word)).1 = .ok scale ∧
      valFloat .f32 (splitValue 64 (joinValue word word)).2 = .ok scale)
    (hLo : t.regs 793 = some (biasValue x)) (hHi : t.regs 792 = some (biasValue y))
    (hScale : t.regs 7135 = some word)
    (hDot : readERealPair l g t (.reg 7303) = some (.ok ((dot₀ : EReal), (dot₁ : EReal)))) :
    ∃ u, At u 3598 [(7897, .pair (scoreValue (affineScore scale dot₀ x))
        (scoreValue (affineScore scale dot₁ y))),
        (7896, joinValue word word)] ∧
      run kernel Assumptions.all l g 5 t = some u ∧
      ∀ r ∉ [3088, 3089, 7895, 7896, 7897], u.regs r = t.regs r := by
  let t₁ := next (setReg t 3088 (scoreValue x))
  let t₂ := next (setReg t₁ 3089 (scoreValue y))
  let t₃ := next (setReg t₂ 7895 (joinValue (scoreValue x) (scoreValue y)))
  let t₄ := next (setReg t₃ 7896 (joinValue word word))
  let u := next (setReg t₄ 7897
    (.pair (scoreValue (affineScore scale dot₀ x)) (scoreValue (affineScore scale dot₁ y))))
  have hAt₁ : At t₁ 3594 [] :=
    ⟨by change t.pc + 1 = _; rw [ht.1], ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩
  have hAt₂ : At t₂ 3595 [] :=
    ⟨by change t₁.pc + 1 = _; rw [hAt₁.1], ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩
  have hAt₃ : At t₃ 3596 [] :=
    ⟨by change t₂.pc + 1 = _; rw [hAt₂.1], ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩
  have hAt₄ : At t₄ 3597 [] :=
    ⟨by change t₃.pc + 1 = _; rw [hAt₃.1], ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩
  have h₀ : run kernel Assumptions.all l g 1 t = some t₁ :=
    widenBiasRun ht Flow.code_3593 (by decide +kernel) (by decide) x hLo
  have h₁ : run kernel Assumptions.all l g 1 t₁ = some t₂ := by
    apply widenBiasRun hAt₁ Flow.code_3594 (by decide +kernel) (by decide) y
    simpa [t₁, next, setReg] using hHi
  have h₂ : run kernel Assumptions.all l g 1 t₂ = some t₃ := by
    apply run_local Flow.code_3595 rfl hAt₂
    rw [Assumptions.execLocalA_all_eq_numeric,
      Assumptions.execLocalA_eq_nil (hAt₂.1 ▸ (by decide : 3595 ∉ Assumptions.swExp2Sites)) rfl]
    have h := exec_pack (A := []) (L := l) (g := g) (d := 7895)
      (by simp [NoPack]) (show t₂.regs 3088 = some (scoreValue x) by simp [t₂, t₁, next, setReg])
      (show t₂.regs 3089 = some (scoreValue y) by simp [t₂, next, setReg]) SegFreePc.nil
    simpa only [scoreValue_bytes, and_self, ↓reduceIte] using h
  have h₃ : run kernel Assumptions.all l g 1 t₃ = some t₄ := by
    apply run_local Flow.code_3596 rfl hAt₃
    rw [Assumptions.execLocalA_all_eq_numeric,
      Assumptions.execLocalA_eq_nil (hAt₃.1 ▸ (by decide : 3596 ∉ Assumptions.swExp2Sites)) rfl]
    have hRead : t₃.regs 7135 = some word := by
      simpa [t₃, t₂, t₁, next, setReg] using hScale
    have h := exec_pack (A := []) (L := l) (g := g) (d := 7896)
      (by simp [NoPack]) hRead hRead SegFreePc.nil
    simpa only [hWordBytes, and_self, ite_true] using h
  have h₄ : run kernel Assumptions.all l g 1 t₄ = some u := by
    apply run_step (n := 0) (by rw [hAt₄.1]; exact Flow.code_3597) rfl
      (show t₄.fault = none from ht.2.2.2.1)
    apply execMaskedFma hs (by simp [t₄, t₃, next, setReg])
      (readERealPair_reg (L := l) (g := g)
        (show t₄.regs 7896 = some (joinValue word word) by simp [t₄, next, setReg])
        hScaleRead.1 hScaleRead.2)
      ((preservesPairRead (l := l) (g := g) (t := t) (u := t₄) (r := 7303)
        (by simp [t₄, t₃, t₂, t₁, next, setReg])).trans hDot)
    rw [hAt₄.1]
    have hFree := (Assumptions.numeric_segSites.pc
      (by decide : 3597 ∉ Assumptions.swExp2Sites)).tail
    intro a ha l' g' t' hp
    rcases List.mem_append.mp ha with ha | hInput
    · rcases List.mem_append.mp ha with hNum | hSync
      · exact hFree a hNum l' g' t' hp
      · simp only [Assumptions.synchronization, List.mem_cons, List.not_mem_nil, or_false] at hSync
        rcases hSync with rfl | rfl | rfl | rfl <;> rfl
    · obtain rfl := List.mem_singleton.mp hInput
      rfl
  refine ⟨u, ⟨?_, ht.2.1, ht.2.2.1, ht.2.2.2.1, ?_⟩,
    run_comp h₀ (run_comp h₁ (run_comp h₂ (run_comp h₃ h₄))), ?_⟩
  · change t₄.pc + 1 = _
    rw [hAt₄.1]
  · simp [Holds, u, t₄, next, setReg]
  · intro r hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp [u, t₄, t₃, t₂, t₁, next, setReg, Function.update_of_ne hn.1,
      Function.update_of_ne hn.2.1, Function.update_of_ne hn.2.2.1,
      Function.update_of_ne hn.2.2.2.1, Function.update_of_ne hn.2.2.2.2]

/-- With the actual `ld.param.b32` representation the inverse scale is duplicated as
a packed integer word, and its two halves decode to the same positive real coefficient. -/
theorem firstBiasPairBitsRun {g : Nat} {t : TState} {x y : Option ℝ} {bits : Nat} {scale : ℚ}
    {dot₀ dot₁ : ℝ} (hs : 0 < scale) (hBits : bits < 2^32) (hDecode : f32Value bits = some scale)
    (ht : At t 3593 []) (hLo : t.regs 793 = some (biasValue x))
    (hHi : t.regs 792 = some (biasValue y)) (hScale : t.regs 7135 = some (b32 bits))
    (hDot : readERealPair l g t (.reg 7303) = some (.ok ((dot₀ : EReal), (dot₁ : EReal)))) :
    ∃ u, At u 3598 [(7897, .pair (scoreValue (affineScore (scale : ℝ) dot₀ x))
        (scoreValue (affineScore (scale : ℝ) dot₁ y))),
        (7896, joinValue (b32 bits) (b32 bits))] ∧
      run kernel Assumptions.all l g 5 t = some u ∧
      readERealPair l g u (.reg 7896) = some (.ok (((scale : ℝ) : EReal), ((scale : ℝ) : EReal))) ∧
      ∀ r ∉ [3088, 3089, 7895, 7896, 7897], u.regs r = t.regs r := by
  have hSplit : splitValue 64 (joinValue (b32 bits) (b32 bits)) = (b32 bits, b32 bits) :=
    split_join_bits (by rw [toNat_ofNat_lt (by omega)]; exact hBits)
  have hRead := valFloat_b32 (by omega) hDecode
  obtain ⟨u, hu, huRun, huFrame⟩ :=
    firstBiasPairWordRun (scale := (scale : ℝ)) (by exact_mod_cast hs) ht rfl
      ⟨by rw [hSplit]; exact hRead, by rw [hSplit]; exact hRead⟩ hLo hHi hScale hDot
  exact ⟨u, hu, huRun, readERealPair_reg hu.2.2.2.2.2.1
    (by rw [hSplit]; exact hRead) (by rw [hSplit]; exact hRead), huFrame⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
