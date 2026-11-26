-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Lemmas.Flow.OutKinds
public import Lemmas.Flow.SegLane

@[expose] public section

/-! # The software `exp2` template on lanes of the kinds

A software `exp2` instance (`Assumptions.swExp2`) as one piece (`Seg.segLaneTwo`), for start facts
of any value function `W` whose two lane inputs are reals or `-∞` (`SK.ni`): the outputs are the
lane readings `laneY` of the inputs (`swExp2Lane`: the template's function of a real, `0` for
`-∞`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section

/-- A lane's reading (`0` where the lane reader fails, which the kinds exclude). -/
def laneY (v : Value) : ℝ :=
  match Assumptions.swExp2Lane v with
  | .ok y => y
  | .error _ => 0

theorem lane_of_ni {v : Value} (h : SK.ni.Has v) : ∃ y, Assumptions.swExp2Lane v = .ok y := by
  rcases h with ⟨-, r, hr⟩ | rfl
  · have key : ∀ d : Exec FVal, readEReal.ofDatum d = some (.ok (r : EReal)) →
        ∃ y, (do let x ← d; match x with | .inf true => pure 0 | _ => cuteExp2.fn <$> x.finite :
          Exec ℝ) = .ok y := by
      intro d hd
      rcases d with e | x
      · simp [readEReal.ofDatum] at hd
      · cases x with
        | inf neg =>
          cases neg
          · simp [readEReal.ofDatum, pure, Except.pure] at hd
          · exact ⟨0, rfl⟩
        | _ => simp_all [readEReal.ofDatum, pure, Except.pure, FVal.finite, bind,
          Except.bind, Functor.map, Except.map]
    cases v with
    | float f x => cases f <;> first | exact ⟨_, rfl⟩ | exact key _ hr
    | _ => exact key _ hr
  · exact ⟨0, Assumptions.swExp2Lane_negInf⟩

theorem laneY_spec {v : Value} (h : SK.ni.Has v) :
    Assumptions.swExp2Lane v = .ok (laneY v) := by
  obtain ⟨y, hy⟩ := lane_of_ni h
  rw [hy]; simp only [laneY, hy]

variable {L : Launch} {g : Nat}

/-- **A software `exp2` instance** at `pc` (the template's match `m`), from facts of `W` on
`keys` to facts on `liveT` of `W` with the outputs written. -/
theorem seg_swExp2 {pc : Nat} {op : Op} {m : SegMatch CuteSlot} {keys liveT : List Nat}
    {W : Nat → Value}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hm : cuteExp2.matchAt kernel pc = some m) (hsite : Assumptions.swExp2Sites.contains pc = true)
    (hio : m.shape.io = [(CuteSlot.x0, CuteSlot.y0), (CuteSlot.x1, CuteSlot.y1)])
    (hcst : m.shape.defines = true ∨ ((∀ p ∈ m.shape.consts, m.regOf p.1 ∈ keys) ∧
      m.shape.consts.map (fun p => valueEx W [] (m.regOf p.1)) = m.shape.consts.map Prod.snd))
    (hi₀ : m.regOf CuteSlot.x0 ∈ keys) (hk₀ : SK.ni.Has (W (m.regOf CuteSlot.x0)))
    (hi₁ : m.regOf CuteSlot.x1 ∈ keys) (hk₁ : SK.ni.Has (W (m.regOf CuteSlot.x1)))
    (hnd : (segKeys m CuteSlot.y0 CuteSlot.y1).Nodup)
    (hcov : ∀ r ∈ liveT, r ∈ segKeys m CuteSlot.y0 CuteSlot.y1 ∨
      (r ∉ segKeys m CuteSlot.y0 CuteSlot.y1 ++ m.shape.writes.map m.regOf ∧ r ∈ keys))
    (hA : SegFreePc [Assumptions.idealArith, Assumptions.approx, Assumptions.lg2,
      Assumptions.bf16Convert] pc) :
    Seg kernel Assumptions.all L g 1 pc (factsFrom keys W) m.stop
      (factsFrom liveT (valueEx W (segValsY m CuteSlot.y0 CuteSlot.y1
        (laneY (W (m.regOf CuteSlot.x0))) (laneY (W (m.regOf CuteSlot.x1))) ++ []))) := by
  have hA' : Assumptions.all = [Assumptions.idealArith, Assumptions.approx, Assumptions.lg2,
      Assumptions.bf16Convert] ++ Assumptions.swExp2 ::
      (Assumptions.synchronization ++ [Assumptions.inputReadOnly]) := rfl
  have hS : factsFrom keys W = factsFrom keys (valueEx W []) := rfl
  rw [hA', hS]
  exact Seg.segLaneTwo hc hl (fun t h1 h2 h3 => by
      simp only [Assumptions.swExp2, h1, h2, h3, List.isEmpty_nil, and_self, hm, hsite,
        ↓reduceIte, Option.map_some]
      rfl) hio hcst hi₀ (laneY_spec hk₀) hi₁ (laneY_spec hk₁) hnd hcov hA

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
