-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasAffine
public import Lemmas.Kernel.CodeSlice
public import Tactics.KernelRfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

def BiasAffineItem.writes (i : BiasAffineItem) : List Nat :=
  [i.widenedLow, i.widenedHigh, i.packed, i.result]

def BiasAffineItem.reads (i : BiasAffineItem) : List Nat :=
  [i.biasLow, i.biasHigh, i.qk]

private theorem biasReadPair_congr {l : Launch} {g r : Nat} {t u : TState}
    (h : u.regs r = t.regs r) :
    readERealPair l g u (.reg r) = readERealPair l g t (.reg r) := by
  simp [readERealPair, readValue, readReg, h]

/-- The sequence consumes each named BF16 bias register and its corresponding QK pair
once. All scores are written to the packed registers named by the decoded instructions. -/
theorem biasAffineSequence {l : Launch} {g scaleReg : Nat} {scale : ℝ}
    (hs : 0 < scale) (bias : Nat → Option ℝ) (qk : Nat → ℝ × ℝ) :
    ∀ (items : List BiasAffineItem) (pc : Nat) (t : TState),
      At t pc [] →
      (∀ n < 4 * items.length, kernel.code[pc + n]? =
        (items.flatMap (·.instructions scaleReg))[n]?) →
      (∀ n < items.length, pc + 4 * n ∈ Assumptions.biasWidenSites ∧
        pc + 4 * n + 1 ∈ Assumptions.biasWidenSites) →
      (∀ n < 4 * items.length, pc + n ∉ Assumptions.swExp2Sites) →
      readERealPair l g t (.reg scaleReg) = some (.ok ((scale : EReal), (scale : EReal))) →
      (∀ i ∈ items, t.regs i.biasLow = some (biasValue (bias i.biasLow)) ∧
        t.regs i.biasHigh = some (biasValue (bias i.biasHigh)) ∧
        readERealPair l g t (.reg i.qk) = some (.ok (((qk i.qk).1 : ℝ), ((qk i.qk).2 : ℝ)))) →
      (∀ i ∈ items, i.widenedLow ≠ i.biasHigh) →
      (∀ i ∈ items, ∀ w ∈ i.writes, w ≠ scaleReg ∧ ∀ j ∈ items, w ∉ j.reads) →
      (items.flatMap BiasAffineItem.writes).Nodup →
      ∃ u, run kernel Assumptions.all l g (4 * items.length) t = some u ∧
        At u (pc + 4 * items.length) [] ∧
        (∀ r ∉ items.flatMap BiasAffineItem.writes, u.regs r = t.regs r) ∧
        ∀ i ∈ items, u.regs i.result = some (.pair
          (scoreValue (affineScore scale (qk i.qk).1 (bias i.biasLow)))
          (scoreValue (affineScore scale (qk i.qk).2 (bias i.biasHigh)))) := by
  intro items
  induction items with
  | nil =>
    intro pc t ht _ _ _ _ _ _ _ _
    exact ⟨t, rfl, ht, fun _ _ => rfl, by simp⟩
  | cons i items ih =>
    intro pc t ht hCode hWiden hOff hScale hInputs hProtected hD hN
    have hPairs : 0 < (i :: items).length := by simp
    have hW := hWiden 0 hPairs
    simp only [Nat.mul_zero, Nat.add_zero] at hW
    simp only [List.flatMap_cons, List.nodup_append] at hN
    have hLowHigh : i.widenedLow ≠ i.widenedHigh := by
      have h := hN.1
      simp only [BiasAffineItem.writes, List.nodup_cons, List.mem_cons, List.not_mem_nil,
        or_false, not_or, List.nodup_nil] at h
      exact h.1.1
    have hDis (r : Nat) (hr : r ∈ i.writes) := hD i (by simp) r hr
    have hKeep (r : Nat) (hr : r ∈ [scaleReg, i.qk]) :
        r ∉ [i.widenedLow, i.widenedHigh, i.packed] := by
      intro he
      have hw : r ∈ i.writes := by simp [BiasAffineItem.writes] at he ⊢; tauto
      rcases List.mem_cons.mp hr with hr | hr
      · exact (hDis r hw).1 hr
      · obtain rfl : r = i.qk := by simpa using hr
        exact (hDis i.qk hw).2 i (by simp) (by simp [BiasAffineItem.reads])
    have hValues := hInputs i (by simp)
    obtain ⟨t₁, hOne, hAt₁, hFrame₁⟩ := biasAffineItemRun i hs ht
      (fun n hn => by
        have h := hCode n (by simp only [List.length_cons]; omega)
        have hLen : (i.instructions scaleReg).length = 4 := rfl
        rwa [List.flatMap_cons, List.getElem?_append_left (hLen ▸ hn)] at h)
      hW (fun n hn => hOff n (by simp only [List.length_cons]; omega))
      hValues.1 hValues.2.1 ⟨hLowHigh, hProtected i (by simp)⟩ hKeep hScale hValues.2.2
    have hOffScale : scaleReg ∉ i.writes := fun h => (hDis scaleReg h).1 rfl
    have hPreserved (j : BiasAffineItem) (hj : j ∈ items) (r : Nat) (hr : r ∈ j.reads) :
        t₁.regs r = t.regs r :=
      hFrame₁ r (fun hw => (hDis r hw).2 j (by simp [hj]) hr)
    have hNextCode (n : Nat) (hn : n < 4 * items.length) :
        kernel.code[pc + 4 + n]? = (items.flatMap (·.instructions scaleReg))[n]? := by
      have h := hCode (4 + n) (by simp only [List.length_cons]; omega)
      have hLen : (i.instructions scaleReg).length = 4 := rfl
      rw [List.flatMap_cons, List.getElem?_append_right (by rw [hLen]; omega), hLen,
        Nat.add_sub_cancel_left] at h
      simpa only [Nat.add_assoc] using h
    have hNextWiden (n : Nat) (hn : n < items.length) :
        pc + 4 + 4 * n ∈ Assumptions.biasWidenSites ∧
        pc + 4 + 4 * n + 1 ∈ Assumptions.biasWidenSites := by
      have h := hWiden (n + 1) (by simpa using hn)
      rw [show pc + 4 * (n + 1) = pc + 4 + 4 * n by omega] at h
      exact h
    obtain ⟨u, hRun, hAt, hFrame, hOut⟩ := ih (pc + 4) t₁
      ⟨hAt₁.1, hAt₁.2.1, hAt₁.2.2.1, hAt₁.2.2.2.1, trivial⟩
      hNextCode hNextWiden
      (fun n hn => by
        rw [Nat.add_assoc]
        exact hOff (4 + n) (by simp only [List.length_cons]; omega))
      ((biasReadPair_congr (l := l) (g := g) (hFrame₁ scaleReg hOffScale)).trans hScale)
      (fun j hj => by
        obtain ⟨hLo, hHi, hDot⟩ := hInputs j (by simp [hj])
        exact ⟨(hPreserved j hj _ (by simp [BiasAffineItem.reads])).trans hLo,
          (hPreserved j hj _ (by simp [BiasAffineItem.reads])).trans hHi,
          (biasReadPair_congr (l := l) (g := g)
            (hPreserved j hj _ (by simp [BiasAffineItem.reads]))).trans hDot⟩)
      (fun j hj => hProtected j (by simp [hj]))
      (fun j hj w hw => ⟨(hD j (by simp [hj]) w hw).1,
        fun k hk => (hD j (by simp [hj]) w hw).2 k (by simp [hk])⟩) hN.2.1
    have hSize : 4 * (i :: items).length = 4 + 4 * items.length := by
      simp only [List.length_cons]; omega
    refine ⟨u, hSize ▸ run_comp hOne hRun, ?_, ?_, ?_⟩
    · simpa only [hSize, Nat.add_assoc] using hAt
    · intro r hr
      simp only [List.flatMap_cons, List.mem_append, not_or] at hr
      exact (hFrame r hr.2).trans (hFrame₁ r hr.1)
    · intro j hj
      rcases List.mem_cons.mp hj with he | hj
      · subst j
        rw [hFrame i.result (fun he => hN.2.2 _ (by simp [BiasAffineItem.writes]) _ he rfl)]
        exact hAt₁.2.2.2.2.1
      · exact hOut j hj

/-- The code slices cover the long bias runs. The first round establishes its inverse scale
in the preceding pair, then uses the same four-instruction body as the repeated round. -/
def biasBodyBase (repeated : Bool) : Nat := if repeated then 5248 else 3584

def biasBodyStart (repeated : Bool) : Nat := if repeated then 5279 else 3598

def biasBodyPairs (repeated : Bool) : Nat := if repeated then 64 else 63

def biasBodySlice (repeated : Bool) : List Instr :=
  if repeated then
    Decoded.code164 ++ Decoded.code165 ++ Decoded.code166 ++ Decoded.code167 ++
      Decoded.code168 ++ Decoded.code169 ++ Decoded.code170 ++ Decoded.code171 ++ Decoded.code172
  else
    Decoded.code112 ++ Decoded.code113 ++ Decoded.code114 ++ Decoded.code115 ++
      Decoded.code116 ++ Decoded.code117 ++ Decoded.code118 ++ Decoded.code119 ++ Decoded.code120

def biasBodyCode (repeated : Bool) : List Instr :=
  ((biasBodySlice repeated).drop (biasBodyStart repeated - biasBodyBase repeated)).take
    (4 * biasBodyPairs repeated)

private theorem biasBodySlice_eq (repeated : Bool) :
    (Decoded.kernel.code.drop (biasBodyBase repeated)).take 288 = biasBodySlice repeated := by
  cases repeated <;> kernel_rfl

def biasItemAt (code : List Instr) (pc : Nat) : Option BiasAffineItem := do
  let some ⟨none, .cvt a⟩ := code[pc]? | none
  let some ⟨none, .cvt b⟩ := code[pc + 1]? | none
  let [.reg lo] := a.srcs | none
  let [.reg hi] := b.srcs | none
  let some ⟨none, .float f⟩ := code[pc + 3]? | none
  let [.reg pack, _, .reg qk] := f.srcs | none
  let [some dst] := f.dsts | none
  return ⟨lo, hi, a.d, b.d, pack, qk, dst⟩

def biasBodyItems (repeated : Bool) : List BiasAffineItem :=
  (List.range (biasBodyPairs repeated)).filterMap fun i =>
    biasItemAt (biasBodyCode repeated) (4 * i)

private theorem biasItemsLength (repeated : Bool) :
    (biasBodyItems repeated).length = biasBodyPairs repeated := by
  cases repeated <;> decide +kernel

private theorem biasItemsCode (repeated : Bool) :
    (biasBodyItems repeated).flatMap (·.instructions 7896) = biasBodyCode repeated := by
  cases repeated <;> kernel_rfl

private theorem biasItemsWiden (repeated : Bool) :
    (List.range (biasBodyPairs repeated)).all (fun i =>
      Assumptions.biasWidenSites.contains (biasBodyStart repeated + 4 * i) &&
      Assumptions.biasWidenSites.contains (biasBodyStart repeated + 4 * i + 1)) = true := by
  cases repeated <;> decide +kernel

private theorem biasItemsDisjoint (repeated : Bool) :
    ((biasBodyItems repeated).flatMap BiasAffineItem.writes).all (fun r =>
      r != 7896 && !((biasBodyItems repeated).flatMap BiasAffineItem.reads).contains r) = true := by
  cases repeated <;> decide +kernel

private theorem biasItemsProtected (repeated : Bool) :
    (biasBodyItems repeated).all (fun i => i.widenedLow != i.biasHigh) = true := by
  cases repeated <;> decide +kernel

private theorem biasItemsNodup (repeated : Bool) :
    ((biasBodyItems repeated).flatMap BiasAffineItem.writes).Nodup := by
  cases repeated <;> decide +kernel

/-- Both long bias passes compute the actual packed score values, through the unconditional
sequence of 63 or 64 pairs. Each returned state continues the same execution. -/
theorem biasBodyRun {l : Launch} {g : Nat} {t : TState}
    {scale : ℝ} (repeated : Bool) (hs : 0 < scale) (bias : Nat → Option ℝ)
    (qk : Nat → ℝ × ℝ) (ht : At t (biasBodyStart repeated) [])
    (hScale : readERealPair l g t (.reg 7896) = some (.ok ((scale : EReal), (scale : EReal))))
    (hInputs : ∀ i ∈ biasBodyItems repeated,
      t.regs i.biasLow = some (biasValue (bias i.biasLow)) ∧
      t.regs i.biasHigh = some (biasValue (bias i.biasHigh)) ∧
      readERealPair l g t (.reg i.qk) = some (.ok (((qk i.qk).1 : ℝ), ((qk i.qk).2 : ℝ)))) :
    ∃ u, At u (biasBodyStart repeated + 4 * biasBodyPairs repeated) [] ∧
      run kernel Assumptions.all l g (4 * biasBodyPairs repeated) t = some u ∧
      (∀ r ∉ (biasBodyItems repeated).flatMap BiasAffineItem.writes, u.regs r = t.regs r) ∧
      ∀ i ∈ biasBodyItems repeated, u.regs i.result = some (.pair
        (scoreValue (affineScore scale (qk i.qk).1 (bias i.biasLow)))
        (scoreValue (affineScore scale (qk i.qk).2 (bias i.biasHigh)))) := by
  have hBase : biasBodyBase repeated ≤ biasBodyStart repeated := by cases repeated <;> decide
  have hBound : biasBodyStart repeated - biasBodyBase repeated + 4 * biasBodyPairs repeated ≤
      288 := by cases repeated <;> decide
  have hCode (n : Nat) (hn : n < 4 * (biasBodyItems repeated).length) :
      kernel.code[biasBodyStart repeated + n]? =
        ((biasBodyItems repeated).flatMap (·.instructions 7896))[n]? := by
    rw [biasItemsLength] at hn
    rw [biasItemsCode, biasBodyCode, List.getElem?_take, ite_eq_left hn, List.getElem?_drop,
      ← biasBodySlice_eq, List.getElem?_take, ite_eq_left (by omega), List.getElem?_drop]
    rw [← Nat.add_assoc, Nat.add_sub_of_le hBase]
  have hWiden (n : Nat) (hn : n < (biasBodyItems repeated).length) :
      biasBodyStart repeated + 4 * n ∈ Assumptions.biasWidenSites ∧
        biasBodyStart repeated + 4 * n + 1 ∈ Assumptions.biasWidenSites := by
    rw [biasItemsLength] at hn
    simpa only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] using
      List.all_eq_true.mp (biasItemsWiden repeated) n (List.mem_range.mpr hn)
  have hOff (n : Nat) (hn : n < 4 * (biasBodyItems repeated).length) :
      biasBodyStart repeated + n ∉ Assumptions.swExp2Sites := by
    rw [biasItemsLength] at hn
    cases repeated <;>
      simp only [biasBodyPairs, biasBodyStart, Bool.false_eq_true, ↓reduceIte,
        Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢ <;> omega
  have hDis (i : BiasAffineItem) (hi : i ∈ biasBodyItems repeated) (w : Nat) (hw : w ∈ i.writes) :
      w ≠ 7896 ∧ ∀ j ∈ biasBodyItems repeated, w ∉ j.reads := by
    have h := List.all_eq_true.mp (biasItemsDisjoint repeated) w
      (List.mem_flatMap.mpr ⟨i, hi, hw⟩)
    simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    exact ⟨h.1, fun j hj hr => h.2 (List.mem_flatMap.mpr ⟨j, hj, hr⟩)⟩
  obtain ⟨u, hRun, hAt, hFrame, hOut⟩ := biasAffineSequence hs bias qk (biasBodyItems repeated)
    (biasBodyStart repeated) t ht hCode hWiden hOff hScale hInputs
    (fun j hj => by simpa only [bne_iff_ne] using
      List.all_eq_true.mp (biasItemsProtected repeated) j hj)
    hDis (biasItemsNodup repeated)
  rw [biasItemsLength] at hAt hRun
  exact ⟨u,hAt,hRun,hFrame,hOut⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
