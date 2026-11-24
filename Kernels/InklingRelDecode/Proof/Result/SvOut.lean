-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvTrace
public import Kernels.InklingRelDecode.Proof.Result.OutPremises
public import Kernels.InklingRelDecode.Proof.Result.RsOSource

@[expose] public section

/-!
# `Out.Inputs.smExit` from the iteration invariant

`blk_fst_halves`: the scores of the key-order block of `Out.blk` are the two halves' visible
logits (`Sv.halfScores`), the premise `hB` of the iteration invariant. `smExit_of`: the softmax
state that hands over to the epilogue holds the launch's scale and the running maximum and sum of
`Out.blocks0` (`Out.Inputs.smExit`), from `Sv.sm_exit_corr`, given the protocol layer's premises
`Sv.SvPrem` (the S tile's load returns the exact scores; the exchange with the partner lane).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma (reqOf splitOf blockOf)
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)

noncomputable section
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

theorem filter_map_range_add {α : Type} (p : Nat → Bool) (f : Nat → α) :
    (((List.range 128).filter p).map f) =
      ((List.range 64).filter p).map f ++
        ((List.range 64).filter fun j => p (64 + j)).map fun j => f (64 + j) := by
  rw [show 128 = 64 + 64 from rfl, List.range_add, List.filter_append, List.map_append]
  congr 1
  rw [List.filter_map, List.map_map]
  congr 1

/-- **The scores of the row's block, in key order, are the two halves' visible logits.** -/
theorem blk_fst_halves (Q : Params) (r s tok head : Nat) (vv : Nat → Nat → ℝ) (b : Nat) :
    (blk Q r s tok head vv b).map Prod.fst =
      halfScores Q r s tok head b 0 ++ halfScores Q r s tok head b 1 := by
  have hkey : ∀ j, key Q s b (64 + j) = keyB Q s b 1 j := fun j => by unfold key keyB; omega
  have hkey0 : ∀ j, key Q s b j = keyB Q s b 0 j := fun j => by unfold key keyB; omega
  unfold blk blockOf halfScores
  rw [List.map_map, filter_map_range_add]
  have hf0 : (Prod.fst ∘ fun k => (logit Q r s tok head b k, vv b k)) =
      logitB Q r s tok head b 0 := by
    funext k
    simp only [Function.comp_apply, logit, logitB, hkey0]
  have hf1 : (fun j => (Prod.fst ∘ fun k => (logit Q r s tok head b k, vv b k)) (64 + j)) =
      logitB Q r s tok head b 1 := by
    funext j
    simp only [Function.comp_apply, logit, logitB, hkey]
  have h1 : List.filter (fun k => decide (Vis Q r s tok b k)) (List.range 64) =
      List.filter (fun k => decide (visB Q r s tok b 0 k)) (List.range 64) :=
    List.filter_congr (fun k _ => decide_eq_decide.mpr (by simp only [Vis, visB, hkey0]))
  have h2 : List.filter (fun j => decide (Vis Q r s tok b (64 + j))) (List.range 64) =
      List.filter (fun k => decide (visB Q r s tok b 1 k)) (List.range 64) :=
    List.filter_congr (fun k _ => decide_eq_decide.mpr (by simp only [Vis, visB, hkey]))
  rw [hf1, hf0, h1, h2]

/-- The epilogue's head index is the softmax thread's. -/
theorem outHead_eq (L : Launch) (g : Nat) :
    Epi.outHead L g = ProA.cta L g .y * 6 + Sm.remOf (g % L.block) := by
  unfold Epi.outHead Epi.headM
  rw [Interface.remOf_eq]
  omega

/-- **`Out.Inputs.smExit`**: the softmax state that goes straight into the epilogue (a valid row)
holds the launch's scale and the running maximum and sum of the row's blocks (`blocks0`), given the
protocol layer's premises on the S tile's load and on the exchange with the partner lane. -/
theorem smExit_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (P : SvPrem Q L X) :
    ∀ {g k : Nat} {dsm : Sm.D} {d : Epi.D}, g < L.threads →
      St Q L X g k = some (some (.d (.sm dsm))) →
      St Q L X g (k + 1) = some (some (.d (.epi d))) → d.pr.rv = true →
      dsm.e.sc = Q.scale ∧ Sm.Corr (sl Q) (blocks0 Q (reqOf L g) (splitOf L g)
        (Epi.tokM (g % L.block)) (Epi.outHead L g)) dsm := by
  intro g k dsm d hg hσ hσ' hrv
  have hm : Epi.Means Q L g d.pr := (hf.reach hg hσ').2
  have hvr : ValidRow Q L g := by
    rw [hm.rv] at hrv
    simp only [decide_eq_true_eq] at hrv
    unfold ValidRow
    rw [Interface.rowM_eq, Interface.tokOf_eq]
    exact hrv
  obtain ⟨-, -, hz⟩ := ProA.cta_lt hpre hg
  have hnI : Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) < 2 ^ 31 := by
    have := Rs.numIters_le hpre hz (ProA.cta L g .x)
    omega
  have h := sm_exit_corr hpre hX hf P hg hvr (B := blk Q (ProA.cta L g .z) (ProA.cta L g .x)
    (Sm.tokOf (g % L.block)) (ProA.cta L g .y * 6 + Sm.remOf (g % L.block)) (fun _ _ => 0))
    (fun b _ => blk_fst_halves Q _ _ _ _ _ b) hnI hσ hσ'
  refine ⟨h.1, ?_⟩
  have e1 : Epi.tokM (g % L.block) = Sm.tokOf (g % L.block) := (Interface.tokOf_eq _).symm
  rw [e1, outHead_eq]
  exact h.2

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
