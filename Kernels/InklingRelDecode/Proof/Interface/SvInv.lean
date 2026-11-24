-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvStage
public import Kernels.InklingRelDecode.Proof.Thread.SmEntryBase

@[expose] public section

/-!
# The iteration invariant of the softmax region

`SvInv B d` is the invariant that ties a state `d` of the softmax region (`Sm.D`) of a thread of
tile row `r` to the row's blocks `B 0, B 1, …` (`Softmax.run`):

* `corr`: the running maximum and sum are `Softmax.run` over the blocks the update has taken in
  (`nDone`: `d.i` before the update of iteration `d.i`, `d.i + 1` from the update on);
* `wb`, `vb`: the bias words loaded so far (of the block in the registers and of the next one) are
  the keys' biases (`Spec.bias`);
* `sv`: after the S tile's load the 64 score words are the exact scores (`Spec.score`);
* `own`: at the first shuffle of the stage the final score words are the row's logits where the
  key is visible and `-inf` elsewhere (`SvScore.fin_sv`), so the visible ones are `halfScores`;
* `stage`: from the stage's two shuffles on until the update, the numbers the stage left are
  `Softmax.step`'s for the block `B d.i` (`StageOk`).

The premises on the events are the bias loads (`BiasEv`) and the S tile's load (`ScoreEv`); the
exchange with the partner lane is `ExchOk` (the premise of `SvInv.pair`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Softmax

noncomputable section
open Classical
set_option maxRecDepth 100000

/-- The sites from the update to the arrival on `p_ready`: the update of the iteration is done. -/
def PostSite : Site → Prop
  | .bar20 => True
  | .tmemSt => True
  | .tmemWait => True
  | .bar21 => True
  | .arrive => True
  | _ => False

/-- The sites between the stage's two shuffles and the update. -/
def StageSite : Site → Prop
  | .waitO => True
  | .bar22 => True
  | .shfl7 => True
  | .shfl8 => True
  | .shfl9 => True
  | .shfl10 => True
  | .store10 => True
  | .bar23 => True
  | .ldL => True
  | .shfl11 => True
  | .shfl12 => True
  | .ldO => True
  | .waitLdO => True
  | .bar24 => True
  | .stO => True
  | .waitStO => True
  | _ => False

/-- The sites at which the probabilities of the iteration's block (`D.pf`) are the stage's: from the
stage to the arrival on `p_ready`. -/
def PfSite (S : Site) : Prop := StageSite S ∨ PostSite S

/-- The number of blocks the running maximum and sum have taken in. -/
def nDone (d : D) : Nat := if PostSite d.site then d.i + 1 else d.i

variable (Q : Params) (L : Launch) (g r s kvh : Nat) (B : Nat → List (ℝ × ℝ))

/-- **The iteration invariant.** -/
structure SvInv (d : D) : Prop where
  ent : EntFull Q r s kvh d.e
  corr : Corr (slQ Q) ((List.range (nDone d)).map B) d
  wb : ∀ k < d.cw, d.i < d.e.r26 →
    bfR (d.w k) = biasB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) d.i
      (Sm.half (g % L.block)) k
  vb : ∀ k < d.cv, d.i + 1 < d.e.r26 →
    bfR (d.v k) = biasB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) (d.i + 1)
      (Sm.half (g % L.block)) k
  sv : d.site = .waitLd → ∀ k < 64, (d.sv k).1 = Value.float .f32
    (score Q r (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block))
      (keyB Q s d.i (Sm.half (g % L.block)) k))
  own : d.site = .shfl5 → ∀ k < 64, (d.stg.fsv k).1 =
    if visB Q r s (tokOf (g % L.block)) d.i (Sm.half (g % L.block)) k then
      Value.float .f32 (logitB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) d.i
        (Sm.half (g % L.block)) k)
    else infB
  stage : StageSite d.site →
    StageOk (slQ Q) (Softmax.run (slQ Q) ((List.range d.i).map B)).m (B d.i) d
  /-- The probabilities of the block `d.i` the thread stores: `2 ^ (sl · logit - m_use · sl)` for a
  visible key, `0` for a masked one. -/
  pf : PfSite d.site → ∀ k < 64, d.pf k =
    if visB Q r s (tokOf (g % L.block)) d.i (Sm.half (g % L.block)) k then
      (2 : ℝ) ^ (slQ Q * logitB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) d.i
        (Sm.half (g % L.block)) k -
        muStage (slQ Q) (Softmax.run (slQ Q) ((List.range d.i).map B)).m (B d.i) * slQ Q)
    else 0

variable {Q L g r s kvh B}

/-! ### The first state -/

/-- **The first state of the region**: no block taken in, the running maximum `-inf` and sum `0`. -/
theorem SvInv.init {e : Ent} (hE : EntFull Q r s kvh e) :
    SvInv Q L g r s kvh B (SmEntry.d0 e) where
  ent := hE
  corr := by
    have h0 : nDone (SmEntry.d0 e) = 0 := by simp [nDone, PostSite, SmEntry.d0]
    rw [h0]
    exact corr_init _ rfl rfl
  wb := by intro k hk; simp [SmEntry.d0] at hk
  vb := by intro k hk; simp [SmEntry.d0] at hk
  sv := by intro h; simp [SmEntry.d0] at h
  own := by intro h; simp [SmEntry.d0] at h
  stage := by intro h; simp [SmEntry.d0, StageSite] at h
  pf := by intro h; simp [SmEntry.d0, PfSite, StageSite, PostSite] at h

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
