-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainE0
public import Lemmas.Flow.SegLane

@[expose] public section

/-! # A plain round's software `exp2` sites as pieces

Each software `exp2` site of a plain round's exponent stretch is one piece (`Seg.segLaneTwo`):
its outputs are the lane readings (`laneR`) of its inputs, which the lanes accept when the inputs
read as reals or `-∞` (`lane_ok`); the defining site also sets the template's constants. The
facts before and after are the lookups in the stretch's lists (`swPiece`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

/-- A lane input that reads as a real or is the `-∞` encoding: the software `exp2` lane accepts
it, and `laneR` is its reading. -/
theorem lane_ok {v : Value}
    (h : (∃ r : ℝ, Assumption.readEReal .f32 v = some (.ok (r : EReal))) ∨ v = negInf32) :
    Assumptions.swExp2Lane v = .ok (laneR v) := by
  rcases h with ⟨r, hr⟩ | rfl
  · have key : ∃ y, Assumptions.swExp2Lane v = .ok y := by
      unfold Assumptions.swExp2Lane
      split
      · exact ⟨_, rfl⟩
      · rename_i hv
        have hr' : Assumption.readEReal.ofDatum (classify .f32 v) = some (.ok (r : EReal)) := by
          unfold Assumption.readEReal at hr
          split at hr
          · rename_i f x
            by_cases hf : f = .f32
            · subst hf; exact absurd rfl (hv x)
            · simpa [hf] using hr
          · exact hr
        cases hc : classify .f32 v with
        | error e => rw [hc] at hr'; simp [Assumption.readEReal.ofDatum] at hr'
        | ok x =>
          rw [hc] at hr'
          cases x with
          | inf neg =>
            cases neg
            · simp [Assumption.readEReal.ofDatum, pure, Except.pure] at hr'
            · exact ⟨0, rfl⟩
          | nan _ => simp [Assumption.readEReal.ofDatum] at hr'
          | zero _ => exact ⟨_, rfl⟩
          | fin _ => exact ⟨_, rfl⟩
    obtain ⟨y, hy⟩ := key
    simp only [laneR, hy]
  · rw [show negInf32 = .bits 32 (BitVec.ofNat 64 0xFF800000) from rfl,
      Assumptions.swExp2Lane_negInf]
    simp only [laneR, Assumptions.swExp2Lane_negInf]


/-- The template instance at `pc` with shape `sh`, its slots as the template's matcher assigns
them. -/
def swMatch (pc : Nat) (sh : SegShape CuteSlot) : SegMatch CuteSlot :=
  ⟨sh, (matchBody sh.body (kernel.code.drop pc) []).getD [], pc + sh.body.length⟩

theorem matchAt7090 : cuteExp2.matchAt kernel 7090 = some (swMatch 7090 cuteExp2Define) := by
  rfl

theorem allSplit : Assumptions.all = [Assumptions.idealArith, Assumptions.approx,
    Assumptions.lg2, Assumptions.bf16Convert] ++ Assumptions.swExp2 ::
    (Assumptions.synchronization ++ [Assumptions.inputReadOnly]) := rfl

/-- **The defining site at pc 7090** from facts on the inputs: the outputs and the constants. -/
theorem sw7090 (L : Launch) (g : Nat) (base : Nat → Value) (liveS liveT : List Nat)
    (h0 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5564) = some (.ok (r : EReal))) ∨
      base 5564 = negInf32)
    (h1 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5565) = some (.ok (r : EReal))) ∨
      base 5565 = negInf32)
    (hi0 : 5564 ∈ liveS) (hi1 : 5565 ∈ liveS)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys (swMatch 7090 cuteExp2Define) CuteSlot.y0 CuteSlot.y1 ∨
      (r ∉ segKeys (swMatch 7090 cuteExp2Define) CuteSlot.y0 CuteSlot.y1 ++
        (swMatch 7090 cuteExp2Define).shape.writes.map (swMatch 7090 cuteExp2Define).regOf ∧
        r ∈ liveS)) :
    Seg kernel Assumptions.all L g 1 7090 (factsFrom liveS (valueEx base [])) 7121
      (factsFrom liveT (valueEx base (segValsY (swMatch 7090 cuteExp2Define) CuteSlot.y0
        CuteSlot.y1 (laneR (base 5564)) (laneR (base 5565)) ++ []))) := by
  rw [allSplit]
  exact Seg.segLaneTwo (i₀ := CuteSlot.x0) (o₀ := CuteSlot.y0) (i₁ := CuteSlot.x1)
    (o₁ := CuteSlot.y1) Flow.code_7090 rfl (fun t e1 e2 e3 => by
      simp only [Assumptions.swExp2, e1, e2, e3, List.isEmpty_nil, and_self, matchAt7090]
      rfl) rfl (.inl rfl) hi0 (lane_ok (v := valueEx base []
      ((swMatch 7090 cuteExp2Define).regOf CuteSlot.x0)) h0)
    hi1 (lane_ok (v := valueEx base []
      ((swMatch 7090 cuteExp2Define).regOf CuteSlot.x1)) h1) (by decide) hcov (by seg_free_pc)

/-- The reusing instance at pc 7121. -/
abbrev mt7121 : SegMatch CuteSlot := swMatch 7121 cuteExp2Reuse

theorem matchAt7121 : cuteExp2.matchAt kernel 7121 = some mt7121 := by
  rfl

/-- The reusing site at pc 7121: its outputs from facts on its inputs and on the constants. -/
theorem sw7121 (L : Launch) (g : Nat) (base : Nat → Value) (liveS liveT : List Nat)
    (h0 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5566) = some (.ok (r : EReal))) ∨
      base 5566 = negInf32)
    (h1 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5567) = some (.ok (r : EReal))) ∨
      base 5567 = negInf32)
    (hi0 : 5566 ∈ liveS) (hi1 : 5567 ∈ liveS)
    (hcst : (∀ p ∈ mt7121.shape.consts, mt7121.regOf p.1 ∈ liveS) ∧
      mt7121.shape.consts.map (fun p => valueEx base [] (mt7121.regOf p.1)) =
        mt7121.shape.consts.map Prod.snd)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys mt7121 CuteSlot.y0 CuteSlot.y1 ∨
      (r ∉ segKeys mt7121 CuteSlot.y0 CuteSlot.y1 ++
        mt7121.shape.writes.map mt7121.regOf ∧ r ∈ liveS)) :
    Seg kernel Assumptions.all L g 1 7121 (factsFrom liveS (valueEx base [])) 7142
      (factsFrom liveT (valueEx base (segValsY mt7121 CuteSlot.y0
        CuteSlot.y1 (laneR (base 5566)) (laneR (base 5567)) ++ []))) := by
  rw [allSplit]
  exact Seg.segLaneTwo (i₀ := CuteSlot.x0) (o₀ := CuteSlot.y0) (i₁ := CuteSlot.x1)
    (o₁ := CuteSlot.y1) Flow.code_7121 rfl (fun t e1 e2 e3 => by
      simp only [Assumptions.swExp2, e1, e2, e3, List.isEmpty_nil, and_self, matchAt7121]
      rfl) rfl (.inr hcst) hi0 (lane_ok (v := valueEx base []
      (mt7121.regOf CuteSlot.x0)) h0)
    hi1 (lane_ok (v := valueEx base []
      (mt7121.regOf CuteSlot.x1)) h1) (by decide) hcov (by seg_free_pc)

/-- The reusing instance at pc 7154. -/
abbrev mt7154 : SegMatch CuteSlot := swMatch 7154 cuteExp2Reuse

theorem matchAt7154 : cuteExp2.matchAt kernel 7154 = some mt7154 := by
  rfl

/-- The reusing site at pc 7154: its outputs from facts on its inputs and on the constants. -/
theorem sw7154 (L : Launch) (g : Nat) (base : Nat → Value) (liveS liveT : List Nat)
    (h0 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5580) = some (.ok (r : EReal))) ∨
      base 5580 = negInf32)
    (h1 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5581) = some (.ok (r : EReal))) ∨
      base 5581 = negInf32)
    (hi0 : 5580 ∈ liveS) (hi1 : 5581 ∈ liveS)
    (hcst : (∀ p ∈ mt7154.shape.consts, mt7154.regOf p.1 ∈ liveS) ∧
      mt7154.shape.consts.map (fun p => valueEx base [] (mt7154.regOf p.1)) =
        mt7154.shape.consts.map Prod.snd)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys mt7154 CuteSlot.y0 CuteSlot.y1 ∨
      (r ∉ segKeys mt7154 CuteSlot.y0 CuteSlot.y1 ++
        mt7154.shape.writes.map mt7154.regOf ∧ r ∈ liveS)) :
    Seg kernel Assumptions.all L g 1 7154 (factsFrom liveS (valueEx base [])) 7175
      (factsFrom liveT (valueEx base (segValsY mt7154 CuteSlot.y0
        CuteSlot.y1 (laneR (base 5580)) (laneR (base 5581)) ++ []))) := by
  rw [allSplit]
  exact Seg.segLaneTwo (i₀ := CuteSlot.x0) (o₀ := CuteSlot.y0) (i₁ := CuteSlot.x1)
    (o₁ := CuteSlot.y1) Flow.code_7154 rfl (fun t e1 e2 e3 => by
      simp only [Assumptions.swExp2, e1, e2, e3, List.isEmpty_nil, and_self, matchAt7154]
      rfl) rfl (.inr hcst) hi0 (lane_ok (v := valueEx base []
      (mt7154.regOf CuteSlot.x0)) h0)
    hi1 (lane_ok (v := valueEx base []
      (mt7154.regOf CuteSlot.x1)) h1) (by decide) hcov (by seg_free_pc)

/-- The reusing instance at pc 7175. -/
abbrev mt7175 : SegMatch CuteSlot := swMatch 7175 cuteExp2Reuse

theorem matchAt7175 : cuteExp2.matchAt kernel 7175 = some mt7175 := by
  rfl

/-- The reusing site at pc 7175: its outputs from facts on its inputs and on the constants. -/
theorem sw7175 (L : Launch) (g : Nat) (base : Nat → Value) (liveS liveT : List Nat)
    (h0 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5582) = some (.ok (r : EReal))) ∨
      base 5582 = negInf32)
    (h1 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5583) = some (.ok (r : EReal))) ∨
      base 5583 = negInf32)
    (hi0 : 5582 ∈ liveS) (hi1 : 5583 ∈ liveS)
    (hcst : (∀ p ∈ mt7175.shape.consts, mt7175.regOf p.1 ∈ liveS) ∧
      mt7175.shape.consts.map (fun p => valueEx base [] (mt7175.regOf p.1)) =
        mt7175.shape.consts.map Prod.snd)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys mt7175 CuteSlot.y0 CuteSlot.y1 ∨
      (r ∉ segKeys mt7175 CuteSlot.y0 CuteSlot.y1 ++
        mt7175.shape.writes.map mt7175.regOf ∧ r ∈ liveS)) :
    Seg kernel Assumptions.all L g 1 7175 (factsFrom liveS (valueEx base [])) 7196
      (factsFrom liveT (valueEx base (segValsY mt7175 CuteSlot.y0
        CuteSlot.y1 (laneR (base 5582)) (laneR (base 5583)) ++ []))) := by
  rw [allSplit]
  exact Seg.segLaneTwo (i₀ := CuteSlot.x0) (o₀ := CuteSlot.y0) (i₁ := CuteSlot.x1)
    (o₁ := CuteSlot.y1) Flow.code_7175 rfl (fun t e1 e2 e3 => by
      simp only [Assumptions.swExp2, e1, e2, e3, List.isEmpty_nil, and_self, matchAt7175]
      rfl) rfl (.inr hcst) hi0 (lane_ok (v := valueEx base []
      (mt7175.regOf CuteSlot.x0)) h0)
    hi1 (lane_ok (v := valueEx base []
      (mt7175.regOf CuteSlot.x1)) h1) (by decide) hcov (by seg_free_pc)

/-- The reusing instance at pc 7232. -/
abbrev mt7232 : SegMatch CuteSlot := swMatch 7232 cuteExp2Reuse

theorem matchAt7232 : cuteExp2.matchAt kernel 7232 = some mt7232 := by
  rfl

/-- The reusing site at pc 7232: its outputs from facts on its inputs and on the constants. -/
theorem sw7232 (L : Launch) (g : Nat) (base : Nat → Value) (liveS liveT : List Nat)
    (h0 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5596) = some (.ok (r : EReal))) ∨
      base 5596 = negInf32)
    (h1 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5597) = some (.ok (r : EReal))) ∨
      base 5597 = negInf32)
    (hi0 : 5596 ∈ liveS) (hi1 : 5597 ∈ liveS)
    (hcst : (∀ p ∈ mt7232.shape.consts, mt7232.regOf p.1 ∈ liveS) ∧
      mt7232.shape.consts.map (fun p => valueEx base [] (mt7232.regOf p.1)) =
        mt7232.shape.consts.map Prod.snd)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys mt7232 CuteSlot.y0 CuteSlot.y1 ∨
      (r ∉ segKeys mt7232 CuteSlot.y0 CuteSlot.y1 ++
        mt7232.shape.writes.map mt7232.regOf ∧ r ∈ liveS)) :
    Seg kernel Assumptions.all L g 1 7232 (factsFrom liveS (valueEx base [])) 7253
      (factsFrom liveT (valueEx base (segValsY mt7232 CuteSlot.y0
        CuteSlot.y1 (laneR (base 5596)) (laneR (base 5597)) ++ []))) := by
  rw [allSplit]
  exact Seg.segLaneTwo (i₀ := CuteSlot.x0) (o₀ := CuteSlot.y0) (i₁ := CuteSlot.x1)
    (o₁ := CuteSlot.y1) Flow.code_7232 rfl (fun t e1 e2 e3 => by
      simp only [Assumptions.swExp2, e1, e2, e3, List.isEmpty_nil, and_self, matchAt7232]
      rfl) rfl (.inr hcst) hi0 (lane_ok (v := valueEx base []
      (mt7232.regOf CuteSlot.x0)) h0)
    hi1 (lane_ok (v := valueEx base []
      (mt7232.regOf CuteSlot.x1)) h1) (by decide) hcov (by seg_free_pc)

/-- The reusing instance at pc 7253. -/
abbrev mt7253 : SegMatch CuteSlot := swMatch 7253 cuteExp2Reuse

theorem matchAt7253 : cuteExp2.matchAt kernel 7253 = some mt7253 := by
  rfl

/-- The reusing site at pc 7253: its outputs from facts on its inputs and on the constants. -/
theorem sw7253 (L : Launch) (g : Nat) (base : Nat → Value) (liveS liveT : List Nat)
    (h0 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5598) = some (.ok (r : EReal))) ∨
      base 5598 = negInf32)
    (h1 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5599) = some (.ok (r : EReal))) ∨
      base 5599 = negInf32)
    (hi0 : 5598 ∈ liveS) (hi1 : 5599 ∈ liveS)
    (hcst : (∀ p ∈ mt7253.shape.consts, mt7253.regOf p.1 ∈ liveS) ∧
      mt7253.shape.consts.map (fun p => valueEx base [] (mt7253.regOf p.1)) =
        mt7253.shape.consts.map Prod.snd)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys mt7253 CuteSlot.y0 CuteSlot.y1 ∨
      (r ∉ segKeys mt7253 CuteSlot.y0 CuteSlot.y1 ++
        mt7253.shape.writes.map mt7253.regOf ∧ r ∈ liveS)) :
    Seg kernel Assumptions.all L g 1 7253 (factsFrom liveS (valueEx base [])) 7274
      (factsFrom liveT (valueEx base (segValsY mt7253 CuteSlot.y0
        CuteSlot.y1 (laneR (base 5598)) (laneR (base 5599)) ++ []))) := by
  rw [allSplit]
  exact Seg.segLaneTwo (i₀ := CuteSlot.x0) (o₀ := CuteSlot.y0) (i₁ := CuteSlot.x1)
    (o₁ := CuteSlot.y1) Flow.code_7253 rfl (fun t e1 e2 e3 => by
      simp only [Assumptions.swExp2, e1, e2, e3, List.isEmpty_nil, and_self, matchAt7253]
      rfl) rfl (.inr hcst) hi0 (lane_ok (v := valueEx base []
      (mt7253.regOf CuteSlot.x0)) h0)
    hi1 (lane_ok (v := valueEx base []
      (mt7253.regOf CuteSlot.x1)) h1) (by decide) hcov (by seg_free_pc)

/-- The reusing instance at pc 7286. -/
abbrev mt7286 : SegMatch CuteSlot := swMatch 7286 cuteExp2Reuse

theorem matchAt7286 : cuteExp2.matchAt kernel 7286 = some mt7286 := by
  rfl

/-- The reusing site at pc 7286: its outputs from facts on its inputs and on the constants. -/
theorem sw7286 (L : Launch) (g : Nat) (base : Nat → Value) (liveS liveT : List Nat)
    (h0 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5612) = some (.ok (r : EReal))) ∨
      base 5612 = negInf32)
    (h1 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5613) = some (.ok (r : EReal))) ∨
      base 5613 = negInf32)
    (hi0 : 5612 ∈ liveS) (hi1 : 5613 ∈ liveS)
    (hcst : (∀ p ∈ mt7286.shape.consts, mt7286.regOf p.1 ∈ liveS) ∧
      mt7286.shape.consts.map (fun p => valueEx base [] (mt7286.regOf p.1)) =
        mt7286.shape.consts.map Prod.snd)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys mt7286 CuteSlot.y0 CuteSlot.y1 ∨
      (r ∉ segKeys mt7286 CuteSlot.y0 CuteSlot.y1 ++
        mt7286.shape.writes.map mt7286.regOf ∧ r ∈ liveS)) :
    Seg kernel Assumptions.all L g 1 7286 (factsFrom liveS (valueEx base [])) 7307
      (factsFrom liveT (valueEx base (segValsY mt7286 CuteSlot.y0
        CuteSlot.y1 (laneR (base 5612)) (laneR (base 5613)) ++ []))) := by
  rw [allSplit]
  exact Seg.segLaneTwo (i₀ := CuteSlot.x0) (o₀ := CuteSlot.y0) (i₁ := CuteSlot.x1)
    (o₁ := CuteSlot.y1) Flow.code_7286 rfl (fun t e1 e2 e3 => by
      simp only [Assumptions.swExp2, e1, e2, e3, List.isEmpty_nil, and_self, matchAt7286]
      rfl) rfl (.inr hcst) hi0 (lane_ok (v := valueEx base []
      (mt7286.regOf CuteSlot.x0)) h0)
    hi1 (lane_ok (v := valueEx base []
      (mt7286.regOf CuteSlot.x1)) h1) (by decide) hcov (by seg_free_pc)

/-- The reusing instance at pc 7307. -/
abbrev mt7307 : SegMatch CuteSlot := swMatch 7307 cuteExp2Reuse

theorem matchAt7307 : cuteExp2.matchAt kernel 7307 = some mt7307 := by
  rfl

/-- The reusing site at pc 7307: its outputs from facts on its inputs and on the constants. -/
theorem sw7307 (L : Launch) (g : Nat) (base : Nat → Value) (liveS liveT : List Nat)
    (h0 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5614) = some (.ok (r : EReal))) ∨
      base 5614 = negInf32)
    (h1 : (∃ r : ℝ, Assumption.readEReal .f32 (base 5615) = some (.ok (r : EReal))) ∨
      base 5615 = negInf32)
    (hi0 : 5614 ∈ liveS) (hi1 : 5615 ∈ liveS)
    (hcst : (∀ p ∈ mt7307.shape.consts, mt7307.regOf p.1 ∈ liveS) ∧
      mt7307.shape.consts.map (fun p => valueEx base [] (mt7307.regOf p.1)) =
        mt7307.shape.consts.map Prod.snd)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys mt7307 CuteSlot.y0 CuteSlot.y1 ∨
      (r ∉ segKeys mt7307 CuteSlot.y0 CuteSlot.y1 ++
        mt7307.shape.writes.map mt7307.regOf ∧ r ∈ liveS)) :
    Seg kernel Assumptions.all L g 1 7307 (factsFrom liveS (valueEx base [])) 7328
      (factsFrom liveT (valueEx base (segValsY mt7307 CuteSlot.y0
        CuteSlot.y1 (laneR (base 5614)) (laneR (base 5615)) ++ []))) := by
  rw [allSplit]
  exact Seg.segLaneTwo (i₀ := CuteSlot.x0) (o₀ := CuteSlot.y0) (i₁ := CuteSlot.x1)
    (o₁ := CuteSlot.y1) Flow.code_7307 rfl (fun t e1 e2 e3 => by
      simp only [Assumptions.swExp2, e1, e2, e3, List.isEmpty_nil, and_self, matchAt7307]
      rfl) rfl (.inr hcst) hi0 (lane_ok (v := valueEx base []
      (mt7307.regOf CuteSlot.x0)) h0)
    hi1 (lane_ok (v := valueEx base []
      (mt7307.regOf CuteSlot.x1)) h1) (by decide) hcov (by seg_free_pc)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
