-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmMax
public import Kernels.InklingRelDecode.Proof.Thread.SmBridge

@[expose] public section

/-! # The numbers of the score stage are `Softmax.step`'s

The machine records, after the shuffle of the row maximum (`D.afterMax`), the new running maximum
(`mn`), the lazy-rescale decision (`kp`) and `alpha` (`al`), and after the shuffle of the half sums
(`D.afterSum`) the row sum (`rs`). This file states them in the form `SmBridge.upd_eq_step` asks
for.

A row of the tile has 128 columns, 64 in each of two lanes (`lane ^ 16`); the lanes exchange their
maxima and sums. `blkOwn` is the thread's own visible scores (its `64` columns), `blkPeer` the
other lane's, and the row's block is `blkOwn ++ blkPeer`. The lane's data are premises: the value
the shuffle returned is the peer's maximum, as an extended real, and its sum, as a number. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Softmax
open Classical

noncomputable section

theorem blockMax_append (a b : List (ℝ × ℝ)) :
    blockMax (a ++ b) = max (blockMax a) (blockMax b) := by
  induction a with
  | nil => simp [blockMax_nil]
  | cons p t ih =>
    have h1 : blockMax (p :: t) = max (p.1 : EReal) (blockMax t) := rfl
    have h2 : blockMax (p :: (t ++ b)) = max (p.1 : EReal) (blockMax (t ++ b)) := rfl
    rw [List.cons_append, h2, ih, h1, max_assoc]

/-- The scores of the thread's columns and of the peer's make the row's block. -/
structure RowOf (d : D) (rv : Value) (blkOwn blkPeer : List (ℝ × ℝ)) : Prop where
  own : d.ownE = blockMax blkOwn
  peer : eOf rv = blockMax blkPeer

theorem mnE_eq {d : D} {rv : Value} {bo bp : List (ℝ × ℝ)} (h : RowOf d rv bo bp) :
    d.mnE (eOf rv) = max d.mE (blockMax (bo ++ bp)) := by
  rw [D.mnE, h.own, h.peer, blockMax_append, max_assoc]


/-! ### The decision and `alpha` -/

theorem kp_iff {d : D} {rv : Value} {sl : ℝ} {m : EReal} {blk : List (ℝ × ℝ)}
    (hsl : slOf d.e = sl) (hm : d.mE = m) (hmn : d.mnE (eOf rv) = max m (blockMax blk)) :
    (d.afterMax rv).stg.kp = true ↔ Keep (alphaLog2 sl m (max m (blockMax blk))) := by
  simp only [D.afterMax, D.keepB, decide_eq_true_eq, D.aLog, hsl, hm, hmn]

theorem al_val {d : D} {rv : Value} {sl : ℝ} {m : EReal} {blk : List (ℝ × ℝ)}
    (hsl : slOf d.e = sl) (hm : d.mE = m) (hmn : d.mnE (eOf rv) = max m (blockMax blk)) :
    valFloat .f32 (d.afterMax rv).stg.al =
      .ok (if Keep (alphaLog2 sl m (max m (blockMax blk))) then 1
        else pow2 (alphaLog2 sl m (max m (blockMax blk)))) := by
  simp only [D.afterMax, D.alV, D.aLog, hsl, hm, hmn]
  split_ifs
  · exact valFloat_one
  · exact valFloat_float _

/-- `upd_eq_step` with `alpha` and the row sum read as numbers (`alpha` is the pattern `1.0`
where the rescale is lazy). -/
theorem upd_eq_step_v {d : D} {sl : ℝ} {blk : List (ℝ × ℝ)} {m : EReal} {l o : ℝ}
    (hm : d.m = erealValue .f32 m) (hl : valFloat .f32 d.l = .ok l)
    (hmn : d.stg.mn = erealValue .f32 (max m (blockMax blk)))
    (hkp : d.stg.kp = true ↔ Keep (alphaLog2 sl m (max m (blockMax blk))))
    (hal : valFloat .f32 d.stg.al = .ok (if Keep (alphaLog2 sl m (max m (blockMax blk))) then 1
        else pow2 (alphaLog2 sl m (max m (blockMax blk)))))
    (hrs : valFloat .f32 d.stg.rs = .ok (blk.map fun q => (2 : ℝ) ^ (sl * q.1 -
      (if Keep (alphaLog2 sl m (max m (blockMax blk))) then m.toReal
        else mSafe (max m (blockMax blk))) * sl)).sum) :
    d.upd.m = erealValue .f32 (Softmax.step sl blk ⟨m, l, o⟩).m ∧
      d.upd.l = .float .f32 (Softmax.step sl blk ⟨m, l, o⟩).l := by
  constructor
  · simp only [D.upd, D.mNew, Softmax.step]
    by_cases hk : Keep (alphaLog2 sl m (max m (blockMax blk)))
    · have : d.stg.kp = true := hkp.mpr hk
      simp [this, hk, hm]
    · have : d.stg.kp = false := by
        cases h : d.stg.kp
        · rfl
        · exact absurd (hkp.mp h) hk
      simp [this, hk, hmn]
  · simp only [D.upd, D.lOut, Softmax.step]
    rw [floatE_fma_fin hl hal hrs]
    rfl

/-- `corr_step` with `alpha` and the row sum read as numbers. -/
theorem corr_step_v {d : D} {sl : ℝ} {bs : List (List (ℝ × ℝ))} {blk : List (ℝ × ℝ)}
    {m : EReal} {l o : ℝ} (hc : Corr sl bs d) (hr : Softmax.run sl bs = ⟨m, l, o⟩)
    (hmn : d.stg.mn = erealValue .f32 (max m (blockMax blk)))
    (hkp : d.stg.kp = true ↔ Keep (alphaLog2 sl m (max m (blockMax blk))))
    (hal : valFloat .f32 d.stg.al = .ok (if Keep (alphaLog2 sl m (max m (blockMax blk))) then 1
        else pow2 (alphaLog2 sl m (max m (blockMax blk)))))
    (hrs : valFloat .f32 d.stg.rs = .ok (blk.map fun q => (2 : ℝ) ^ (sl * q.1 -
      (if Keep (alphaLog2 sl m (max m (blockMax blk))) then m.toReal
        else mSafe (max m (blockMax blk))) * sl)).sum) :
    Corr sl (bs ++ [blk]) d.upd := by
  have hrun : Softmax.run sl (bs ++ [blk]) = Softmax.step sl blk ⟨m, l, o⟩ := by
    rw [← hr]
    simp [Softmax.run, List.foldl_append]
  obtain ⟨hm, hl⟩ := hc
  rw [hr] at hm hl
  obtain ⟨h1, h2⟩ := upd_eq_step_v (d := d) (sl := sl) (blk := blk) hm hl hmn hkp hal hrs
  unfold Corr
  rw [hrun]
  refine ⟨h1, ?_⟩
  rw [h2]
  exact valFloat_float _

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
