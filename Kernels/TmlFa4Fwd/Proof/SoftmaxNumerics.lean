-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Real.MaskedSoftmaxUpdate
public import Lemmas.Real.Rescale

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd

open Finset PTX.Numeric

noncomputable section

/-- Each tile is visited in descending key-block order. -/
def visitKey (blocks visit col : Nat) : Nat := 128 * (blocks - 1 - visit) + col

/-- The tile contributes only its keys in the causal prefix. -/
def maskedBlockSum (live blocks visit : Nat) (f : Nat → ℝ) : ℝ :=
  ∑ col ∈ range 128,
    if visitKey blocks visit col < live then f (visitKey blocks visit col) else 0

private theorem blockPrefix_eq_zero {live blocks visit : Nat} (f : Nat → ℝ)
    (h : live ≤ visitKey blocks visit 0) :
    (∑ i ∈ range (visit + 1), maskedBlockSum live blocks i f) = 0 := by
  apply sum_eq_zero
  intro i hi
  have horder := mem_range.mp hi
  unfold maskedBlockSum
  apply sum_eq_zero
  intro col _
  exact ite_eq_right (by unfold visitKey at h ⊢; omega)

private theorem sum_maskedBlocks {live blocks : Nat} (f : Nat → ℝ) (h : live ≤ 128 * blocks) :
    (∑ i ∈ range blocks, maskedBlockSum live blocks i f) = ∑ j ∈ range live, f j :=
  sum_desc_masked f h

/-- Weight times the value-cache component of one key. -/
def weightedValue (p : Params) (b h row d j : Nat) : ℝ :=
  weight p b h row j * p.v (p.page b (j / 16)) (h / 6) (j % 16) d

/-- The denominator recurrence of a row's execution. References are in base-two exponent units.
Before the first visible key, a stored negative infinity is represented by `none`. -/
structure SoftmaxSumPrefix (p : Params) (b h row blocks visited : Nat)
    (ref : Nat → Option ℝ) (rowSum : Nat → ℝ) : Prop where
  empty : ∀ visit < visited, ref visit = none → p.keyCount b row ≤ visitKey blocks visit 0
  sumInitial : rowSum 0 = (2 : ℝ) ^ (-(ref 0).getD 0) *
    maskedBlockSum (p.keyCount b row) blocks 0 (weight p b h row)
  sumStep : ∀ visit, visit + 1 < visited →
    rowSum (visit + 1) = rowSum visit * maskedRescale (ref visit) (ref (visit + 1)) +
      (2 : ℝ) ^ (-(ref (visit + 1)).getD 0) *
        maskedBlockSum (p.keyCount b row) blocks (visit + 1) (weight p b h row)

/-- The denominator recurrence after every scheduled key block has been visited. -/
abbrev SoftmaxSumRun (p : Params) (b h row blocks : Nat)
    (ref : Nat → Option ℝ) (rowSum : Nat → ℝ) :=
  SoftmaxSumPrefix p b h row blocks blocks ref rowSum

namespace SoftmaxSumPrefix

variable {p : Params} {b h row blocks visited : Nat}
  {ref : Nat → Option ℝ} {rowSum : Nat → ℝ}

theorem first (mx : Option ℝ) (sum : ℝ)
    (hempty : mx = none → p.keyCount b row ≤ visitKey blocks 0 0)
    (hsum : sum = (2 : ℝ) ^ (-mx.getD 0) *
      maskedBlockSum (p.keyCount b row) blocks 0 (weight p b h row)) :
    SoftmaxSumPrefix p b h row blocks 1 (fun _ => mx) (fun _ => sum) := by
  refine ⟨?_, hsum, by omega⟩
  intro visit hv hNone
  have : visit = 0 := by omega
  simpa only [this] using hempty hNone

/-- Extend the recorded prefix with the next decoded recurrence while leaving all earlier
visits unchanged. The key indices continue to use the original tile count. -/
theorem extend (run : SoftmaxSumPrefix p b h row blocks visited ref rowSum)
    (hv : 0 < visited) (mx : Option ℝ) (sum : ℝ)
    (hempty : mx = none → p.keyCount b row ≤ visitKey blocks visited 0)
    (hsum : sum = rowSum (visited - 1) * maskedRescale (ref (visited - 1)) mx +
      (2 : ℝ) ^ (-mx.getD 0) * maskedBlockSum (p.keyCount b row) blocks visited
        (weight p b h row)) :
    SoftmaxSumPrefix p b h row blocks (visited + 1)
      (Function.update ref visited mx) (Function.update rowSum visited sum) := by
  refine ⟨?_, ?_, ?_⟩
  · intro visit hi hRef
    by_cases he : visit = visited
    · subst visit
      exact hempty (by simpa only [Function.update_self] using hRef)
    · exact run.empty visit (by omega)
        (by simpa only [Function.update_of_ne he] using hRef)
  · have h0 : 0 ≠ visited := by omega
    simpa only [Function.update_of_ne h0] using run.sumInitial
  · intro visit hi
    have hCurr : visit ≠ visited := by omega
    by_cases he : visit + 1 = visited
    · have hp : visit = visited - 1 := by omega
      simpa only [he, Function.update_self, Function.update_of_ne hCurr, ← hp] using hsum
    · simpa only [Function.update_of_ne he, Function.update_of_ne hCurr] using
        run.sumStep visit (by omega)

end SoftmaxSumPrefix

/-- The full attention computation also accumulates the probability-weighted value vectors. -/
structure SoftmaxRun (p : Params) (b h row blocks : Nat)
    (ref : Nat → Option ℝ) (rowSum : Nat → ℝ) (acc : Nat → Nat → ℝ)
    : Prop extends toSoftmaxSumRun : SoftmaxSumPrefix p b h row blocks blocks ref rowSum where
  accInitial : ∀ d < 128, acc 0 d = (2 : ℝ) ^ (-(ref 0).getD 0) *
    maskedBlockSum (p.keyCount b row) blocks 0 (weightedValue p b h row d)
  accStep : ∀ visit, visit + 1 < blocks → ∀ d < 128,
    acc (visit + 1) d = acc visit d * maskedRescale (ref visit) (ref (visit + 1)) +
      (2 : ℝ) ^ (-(ref (visit + 1)).getD 0) *
        maskedBlockSum (p.keyCount b row) blocks (visit + 1) (weightedValue p b h row d)

namespace SoftmaxSumRun

variable {p : Params} {b h row blocks : Nat}
  {ref : Nat → Option ℝ} {rowSum : Nat → ℝ}

theorem sum_eq (run : SoftmaxSumRun p b h row blocks ref rowSum) {visit : Nat}
    (hv : visit < blocks) :
    rowSum visit = (2 : ℝ) ^ (-(ref visit).getD 0) *
      ∑ i ∈ range (visit + 1), maskedBlockSum (p.keyCount b row) blocks i (weight p b h row) :=
  shifted_acc_masked run.sumInitial run.sumStep
    (fun i hi emp => blockPrefix_eq_zero (weight p b h row) (run.empty i hi emp)) visit hv

/-- The last visited tile has key zero, so a nonempty causal prefix gives a finite reference. -/
theorem final_ref (run : SoftmaxSumRun p b h row blocks ref rowSum) (hn : 0 < blocks)
    (hkey : 0 < p.keyCount b row) : (ref (blocks - 1)).isSome = true := by
  cases he : ref (blocks - 1) with
  | some x => rfl
  | none =>
    have hz := run.empty (blocks - 1) (by omega) he
    simp only [visitKey, Nat.sub_self, mul_zero, add_zero] at hz
    omega

/-- The terminal denominator is the full causal mass at the terminal reference. -/
theorem final_sum_eq (run : SoftmaxSumRun p b h row blocks ref rowSum) (hn : 0 < blocks)
    (hcover : p.keyCount b row ≤ 128 * blocks) :
    rowSum (blocks - 1) = (2 : ℝ) ^ (-(ref (blocks - 1)).getD 0) * mass p b h row := by
  have hCount : blocks - 1 + 1 = blocks := by omega
  have hSum := run.sum_eq (show blocks - 1 < blocks by omega)
  rw [hCount, sum_maskedBlocks _ hcover] at hSum
  exact hSum

/-- The last running sum is positive when the visits cover a nonempty causal prefix. -/
theorem final_sum_pos (run : SoftmaxSumRun p b h row blocks ref rowSum) (hn : 0 < blocks)
    (hkey : 0 < p.keyCount b row) (hcover : p.keyCount b row ≤ 128 * blocks) :
    0 < rowSum (blocks - 1) := by
  have hMass : 0 < mass p b h row := sum_two_rpow_pos (by simpa using hkey.ne') _
  rw [run.final_sum_eq hn hcover]
  exact mul_pos (two_rpow_pos _) hMass

/-- LSE depends only on the denominator and its reference. -/
theorem final_lse (run : SoftmaxSumRun p b h row blocks ref rowSum) (hn : 0 < blocks)
    (hkey : 0 < p.keyCount b row) (hcover : p.keyCount b row ≤ 128 * blocks) :
    abiFloat 0x3F317218 * ((ref (blocks - 1)).getD 0 + Real.logb 2 (rowSum (blocks - 1))) =
      lse p b h row := by
  have hMass : 0 < mass p b h row := sum_two_rpow_pos (by simpa using hkey.ne') _
  rw [run.final_sum_eq hn hcover, lse_cancel_reference _ _ hMass]
  rfl

end SoftmaxSumRun

namespace SoftmaxRun

variable {p : Params} {b h row blocks : Nat}
  {ref : Nat → Option ℝ} {rowSum : Nat → ℝ} {acc : Nat → Nat → ℝ}

theorem acc_eq (run : SoftmaxRun p b h row blocks ref rowSum acc) {visit d : Nat}
    (hv : visit < blocks) (hd : d < 128) :
    acc visit d = (2 : ℝ) ^ (-(ref visit).getD 0) *
      ∑ i ∈ range (visit + 1), maskedBlockSum (p.keyCount b row) blocks i
        (weightedValue p b h row d) :=
  shifted_acc_masked (acc := fun i => acc i d) (run.accInitial d hd)
    (fun i hi => run.accStep i hi d hd)
    (fun i hi emp => blockPrefix_eq_zero (weightedValue p b h row d) (run.empty i hi emp)) visit hv

/-- The guarded reciprocal gives the attention output and the base-two logarithm gives the ABI
LSE after the last visit. -/
theorem result (run : SoftmaxRun p b h row blocks ref rowSum acc) (hn : 0 < blocks)
    (hkey : 0 < p.keyCount b row) (hcover : p.keyCount b row ≤ 128 * blocks) {d : Nat}
    (hd : d < 128) :
    let last := blocks - 1
    acc last d * (1 / (if rowSum last = 0 then 1 else rowSum last)) = attention p b h row d ∧
    abiFloat 0x3F317218 * ((ref last).getD 0 + Real.logb 2 (rowSum last)) = lse p b h row := by
  dsimp
  have hlast : blocks - 1 < blocks := by omega
  have hcount : blocks - 1 + 1 = blocks := by omega
  have hm := SoftmaxSumRun.final_sum_eq run.toSoftmaxSumRun hn hcover
  have ha := run.acc_eq hlast hd
  rw [hcount, sum_maskedBlocks _ hcover] at ha
  have hsumpos := SoftmaxSumRun.final_sum_pos run.toSoftmaxSumRun hn hkey hcover
  constructor
  · rw [mul_recip_guard hsumpos, ha, hm]
    exact mul_div_mul_left _ _ (two_rpow_ne_zero _)
  · exact SoftmaxSumRun.final_lse run.toSoftmaxSumRun hn hkey hcover

end SoftmaxRun

/-- The dual-stage query tile's key-block count covers every visible key of its rows. -/
theorem Params.keyCount_le_kvBlocks (p : Params) {b row tile : Nat}
    (hrow : row < 256 * (tile + 1)) :
    p.keyCount b row ≤ 128 * min ((p.kLength b + 127) / 128)
      ((p.kLength b - p.qLength b + 256 * (tile + 1) + 127) / 128) := by
  unfold Params.keyCount
  omega

/-- Bias indexing splits into the tile's relative 128-column block and the column within it. -/
theorem Params.biasColumn_of_block (p : Params) (b row block col : Nat) :
    let past := p.kLength b - p.qLength b
    let endBlock := (min ((row / 128 + 1) * 128 + past) (p.kLength b) + 127) / 128
    p.biasColumn b row (128 * block + col) = 128 * (10 + (block : Int) - endBlock) + col := by
  dsimp [Params.biasColumn]
  push_cast
  ring

/-- Every valid suffix query has at least one causally visible key. -/
theorem Pre.keyCount_pos {p : Params} {l : Launch} {m : Mem0} (pre : Pre p l m)
    {b row : Nat} (hb : b < p.batch) (hrow : row < p.qLength b) :
    0 < p.keyCount b row := by
  have hlen := (pre.lengths b hb).2.1
  unfold Params.keyCount
  omega

end
end PTX.Kernels.TmlFa4Fwd
