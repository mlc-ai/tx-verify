-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.DerivedRun
public import Lemmas.Flow.ArithCore
public import Lemmas.Flow.Recip

@[expose] public section

/-! # The derived constants as numbers

With the scale parameter a positive number `s`, the derived registers read as `s * log2 e` (498),
`1 / s` (805) and `-(s * log2 e)` (499), and the pair of 1960 as two copies of `1 / s`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Assumption Control

noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

theorem derV_525 : derV e L g 525 = scaleVal L := by
  simp [derV, G6, G5, G4, G3, G2, G1, G0, lookupD, Gen.io_facts3, Gen.ie_facts1, Gen.ng_facts1,
    Gen.e8_facts1, Gen.dv_facts1, Gen.en_facts1, List.lookup]

theorem scaleVal_float {Q : Params} {m : Mem0} (hp : Pre Q L m) :
    valFloat .f32 (scaleVal L) = .ok Q.scale := by
  obtain ⟨bits, hb, hl, hs⟩ := hp.paramScale
  obtain ⟨q, hq, hqs⟩ := Option.map_eq_some_iff.mp hs
  have h := valFloat_b32 (b := bits) (by omega) hq
  have : scaleVal L = b32 bits := by
    simp only [scaleVal, hl, Option.getD_some, truncBits, b32]
    congr 2
    simp [BitVec.toNat_ofNat]
    omega
  rw [this, ← hqs]; exact h

theorem valFloat_log2e : valFloat .f32 (.bits 32 (BitVec.ofNat 64 1069066811)) = .ok log2eF32 := by
  obtain ⟨q, hq, hqs⟩ := Option.map_eq_some_iff.mp log2eF32_pattern
  have := valFloat_b32 (b := 1069066811) (by norm_num) hq
  rw [← hqs]; exact this

theorem derV_dv (e : Entry) :
    derV e L g 498 = Gen.dv_v601 (lookupD (G1 e L g)) ∧
    derV e L g 805 = Gen.dv_v600 (lookupD (G1 e L g)) := by
  constructor <;>
  simp [derV, G6, G5, G4, G3, G2, lookupD, Gen.io_facts3, Gen.ie_facts1, Gen.ng_facts1,
    Gen.e8_facts1, Gen.dv_facts1, List.lookup]

theorem derV_498 (h : valFloat .f32 (scaleVal L) = .ok s) :
    derV e L g 498 = .float .f32 (s * log2eF32) := by
  rw [(derV_dv e).1]
  have h5 : lookupD (G1 e L g) 525 = scaleVal L := by
    simp [G1, G0, lookupD, Gen.en_facts1, List.lookup]
  simp only [Gen.dv_v601, h5, fF, regsOf, mulL]
  simp [fOpnd, lk, regOf, List.flatMap, mulE_fin h valFloat_log2e, okVal]

theorem negE_fin {va : Value} {x : ℝ} (hx : valFloat .f32 va = .ok x) :
    negE false va = .ok (.float .f32 (-x)) := by
  unfold negE
  simp only [idealNeg, readEReal_of_valFloat hx, bindRead, pure, Except.pure]
  rw [← EReal.coe_neg, erealValue_coe]

theorem derV_805 (h : valFloat .f32 (scaleVal L) = .ok s) (h0 : s ≠ 0) :
    derV e L g 805 = .float .f32 (1 / s) := by
  rw [(derV_dv e).2]
  have h5 : lookupD (G1 e L g) 525 = scaleVal L := by
    simp [G1, G0, lookupD, Gen.en_facts1, List.lookup]
  have h1 : valFloat .f32 (Gen.dv_v599 (lookupD (G1 e L g))) = .ok 1 := by
    simpa [Gen.dv_v599] using valFloat_one
  simp [Gen.dv_v600, h5, fF, regOf, regsOf, fOpnd, lk, List.flatMap, divFullE, okVal,
    List.lookup, approxVal, finiteVal_of h, finiteVal_of h1, bindRead, h0, pure, Except.pure]

theorem derV_499 (h : valFloat .f32 (scaleVal L) = .ok s) :
    derV e L g 499 = .float .f32 (-(s * log2eF32)) := by
  have h4 : derV e L g 499 = Gen.ng_v807 (lookupD (G3 e L g)) := by
    simp [derV, G6, G5, G4, lookupD, Gen.io_facts3, Gen.ie_facts1, Gen.ng_facts1, List.lookup]
  have h3 : lookupD (G3 e L g) 498 = .float .f32 (s * log2eF32) := by
    rw [← derV_498 (e := e) (g := g) h]
    simp [derV, G6, G5, G4, G3, G2, lookupD, Gen.io_facts3, Gen.ie_facts1, Gen.ng_facts1,
      Gen.e8_facts1, Gen.dv_facts1, List.lookup]
  rw [h4]
  have hv : valFloat .f32 (.float .f32 (s * log2eF32)) = .ok (s * log2eF32) := by
    simp [valFloat, pure, Except.pure]
  simp [Gen.ng_v807, h3, fF, regOf, regsOf, fOpnd, lk, List.flatMap, negL, okVal,
    negE_fin hv]

theorem derV_1960 (h : valFloat .f32 (scaleVal L) = .ok s) (h0 : s ≠ 0) :
    derV e L g 1960 = joinValue (.float .f32 (1 / s)) (.float .f32 (1 / s)) := by
  have h805 : lookupD (G5 e L g) 805 = .float .f32 (1 / s) := by
    rw [← derV_805 (e := e) (g := g) h h0]
    simp [derV, G6, G5, lookupD, Gen.io_facts3, Gen.ie_facts1, List.lookup]
  have : derV e L g 1960 = Gen.io_v848 (lookupD (G5 e L g)) := by
    simp [derV, G6, lookupD, Gen.io_facts3]
  rw [this]
  simp [Gen.io_v848, h805]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
