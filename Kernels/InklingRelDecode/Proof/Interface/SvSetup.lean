-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvStep

@[expose] public section

/-!
# The loop's setup and its update keep the iteration invariant

* `biasB_zero`: a block before `n_bias` has no bias;
* `SvInv.afterSetup`: the loop test and the next block's loads' guard (`Sm.afterSetup`): the words
  of a masked load stay the zero half-word, which is the key's bias because the block is before
  `n_bias`;
* `SvInv.toBar20`: the update of the running maximum and sum after the stage is `Softmax.step`'s
  (`corr_step_stage`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Softmax

noncomputable section
open Classical
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g r s kvh : Nat} {B : Nat → List (ℝ × ℝ)}

/-- **A block before `n_bias` has no bias.** -/
theorem biasB_zero {e : Ent} (hE : EntFull Q r s kvh e) {tok head b h k : Nat} (hh : h < 2)
    (hk : k < 64) (hb : ¬ e.nbias ≤ blkOf e b) : biasB Q r s tok head b h k = 0 := by
  unfold biasB bias keyB
  have h1 := hE.blk b
  have h2 : ¬ Q.nBias r ≤ s + b * Q.splits := by
    rw [← hE.nbias, ← h1]; exact hb
  have h3 : ¬ Q.nBias r * 128 ≤ 128 * (s + b * Q.splits) + 64 * h + k := by
    intro hh
    have := Nat.mul_lt_mul_of_pos_right (not_le.mp h2) (by norm_num : 0 < 128)
    omega
  simp only [h3, ↓reduceIte]

/-- The zero half-word reads as the number 0. -/
theorem bfR_z16 : bfR z16 = 0 := rfl

/-- The number of blocks of a state below `r26` forces `r25 < 2 ^ 31` and `r26 = r25`. -/
theorem _root_.PTX.Kernels.InklingRelDecode.Proof.Sm.Ent.Ok.r26_of_lt {e : Ent} (h : e.Ok)
    {i : Nat} (hi : i < e.r26) :
    e.r25 < 2 ^ 31 ∧ e.r26 = e.r25 := by
  have := h.r26
  split_ifs at this with hh
  · exact ⟨hh, this⟩
  · omega

/-- **The loop test and the next block's loads' guard**, from a state that is not past the update
whose bias words satisfy the invariant's clauses. -/
theorem SvInv.afterSetup {x d' : D} (hE : EntFull Q r s kvh x.e) (hok : x.e.Ok)
    (hv : rowValid x.e (g % L.block) = true)
    (hc : Corr (slQ Q) ((List.range x.i).map B) x)
    (hwb : ∀ k < x.cw, x.i < x.e.r26 →
      bfR (x.w k) = biasB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) x.i
        (Sm.half (g % L.block)) k)
    (hvb : ∀ k < x.cv, x.i + 1 < x.e.r26 →
      bfR (x.v k) = biasB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) (x.i + 1)
        (Sm.half (g % L.block)) k)
    (hn : Sm.afterSetup L g x = some (some d')) :
    SvInv Q L g r s kvh B d' := by
  have hh2 : Sm.half (g % L.block) < 2 := by unfold Sm.half; omega
  unfold Sm.afterSetup at hn
  split at hn
  · cases hn
  · split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      refine ⟨hE, ?_, hwb, hvb, ?_, ?_, ?_, ?_⟩
      · have : nDone { x with site := .nxt 0 } = x.i := by simp [nDone, PostSite]
        rw [this]; exact hc
      · intro hh; cases hh
      · intro hh; cases hh
      · intro hh; simp [StageSite] at hh
      · intro hh; simp [PfSite, StageSite, PostSite] at hh
    · rename_i hne hact
      simp only [Option.some.injEq] at hn
      subst hn
      refine ⟨hE, ?_, hwb, ?_, ?_, ?_, ?_, ?_⟩
      · have : nDone { x with site := .waitS, cv := 64, v := fun _ => z16 } = x.i := by
          simp [nDone, PostSite]
        rw [this]; exact hc
      · intro k hk hi
        dsimp only at hk hi ⊢
        rw [bfR_z16]
        refine (biasB_zero hE hh2 hk ?_).symm
        simp only [actB, Bool.and_eq_true, decide_eq_true_eq, not_and, hv, true_and] at hact
        have hr25 : x.i + 1 < x.e.r25 ∧ x.e.r25 < 2 ^ 31 := by
          have := hok.r26_of_lt (i := x.i + 1) hi
          omega
        have := hact hr25
        unfold blkOf
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · intro hh; cases hh
      · intro hh; cases hh
      · intro hh; simp [StageSite] at hh
      · intro hh; simp [PfSite, StageSite, PostSite] at hh

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
