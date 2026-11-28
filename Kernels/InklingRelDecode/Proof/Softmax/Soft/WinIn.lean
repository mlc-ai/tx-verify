-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.CurDefs
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Bias
import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Inp
import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Pair
import Kernels.InklingRelDecode.Proof.Softmax.Data.Constants

@[expose] public section

/-! # The inputs of the first window read as the exact scores, biases and scale

With the score words of the value state the loads of the trace returned and the bias words the
loads left, the registers the first window reads are the pairs of those, as `BiasIn` says. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow PTX.Assumption Control Data

variable {Q : Params} {L : Launch} {g : Nat} {e : Control.Entry}

theorem BW.bw {v : Value} {b : ℝ} (h : BW v b) : Bw v := by
  rcases h with h | ⟨h, -⟩
  · exact .inl ⟨b, h⟩
  · exact .inr h

theorem BW.read {v : Value} {b : ℝ} (h : BW v b) :
    readEReal .bf16 v = some (.ok (b : EReal)) := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · simp [readEReal, pure, Except.pure]
  · have hz := classify_bits (fmt := .bf16) (n := 0) (x := .zero false) (by decide) (by decide)
    change classify .bf16 (.bits 16 (BitVec.ofNat 64 0)) = .ok (.zero false) at hz
    change readEReal.ofDatum (classify .bf16 (.bits 16 (BitVec.ofNat 64 0))) = _
    rw [hz]; rfl

/-- **The first window's inputs are the exact scores, biases and reciprocal scale.** -/
theorem bias_in_w1 {m : Mem0} (hp : Pre Q L m) {d : Data.D} {S β : Nat → ℝ}
    (hs : ∀ j < 64, d.v.s[j]? = some (.float .f32 (S j)))
    (hc : ∀ j < 64, BW (d.v.cur j) (β j)) :
    BiasIn (w1V e L g d) S β (1 / Q.scale) := by
  have sget : ∀ j < 64, d.v.s.getD j (b32 0) = .float .f32 (S j) := fun j hj => by
    rw [List.getD_eq_getElem?_getD, hs j hj]; rfl
  have cev : ∀ x : ℝ, Ev (.float .f32 x) (x : EReal) := fun x => ⟨(erealValue_coe .f32 x).symm,
    EReal.coe_ne_top _⟩
  have pk : ∀ r, 1916 ≤ r → r < 1948 → w1V e L g d r =
      packV (d.v.cur (2 * (r - 1916))) (d.v.cur (2 * (r - 1916) + 1)) := fun r h1 h2 => by
    rw [w1V, lookupD_mem (base_once (canon d) (by simp; omega)) (pack_mem (canon d) h1 h2)]
    rfl
  refine ⟨fun r h1 h2 => ?_, fun r h1 h2 => ?_, fun r h1 h2 => ?_, ?_⟩
  · rw [w1V, lookupD_mem (base_once (canon d) (by simp; omega)) (score_mem (canon d) h1 h2)]
    change PE (joinValue (d.v.s.getD _ _) (d.v.s.getD _ _)) _ _
    rw [sget (2 * (r - 2447)) (by omega), sget (2 * (r - 2447) + 1) (by omega)]
    exact pe_join (cev _) (cev _)
  · have a1 : 2 * (r - 1916) < 64 := by omega
    have a2 : 2 * (r - 1916) + 1 < 64 := by omega
    rw [pk r h1 h2, packV_split (BW.bw (hc _ a1)) (BW.bw (hc _ a2))]
    exact BW.read (hc _ a1)
  · have a1 : 2 * (r - 1916) < 64 := by omega
    have a2 : 2 * (r - 1916) + 1 < 64 := by omega
    rw [pk r h1 h2, packV_split (BW.bw (hc _ a1)) (BW.bw (hc _ a2))]
    exact BW.read (hc _ a2)
  · have hs := scaleVal_float (L := L) hp
    have h0 : Q.scale ≠ 0 := hp.scalePos.ne'
    rw [w1V, lookupD_mem (base_once (canon d) (by simp)) (step_mem (canon d)), derV_1960 hs h0]
    exact pe_join (cev _) (cev _)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
