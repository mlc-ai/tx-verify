-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvScore
public import Kernels.InklingRelDecode.Proof.Thread.SmPeer

@[expose] public section

/-!
# The two shuffles of the score stage make the update `Softmax.step`'s

`StageOk` states the four numbers the score stage leaves (the new maximum `mn`, the lazy-rescale
decision `kp`, `alpha` and the row sum `rs`) in the form `SmStg.corr_step_v` asks for, for the
row's block `blk`. `stage_pair`: after the exchange of the row maximum and the row sum with the
partner lane (`Sm.PeerExchange`, supplied by the protocol layer as a premise) the state
`(d.afterMax rv).afterSumR y` satisfies `StageOk` for the block whose scores are, up to order,
the two lanes' visible scores. `corr_step_stage` is then `Sm.corr_step_v`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Softmax

noncomputable section
open Classical

/-- `m_use` of `Softmax.step` against the block `blk` after the blocks whose maximum is `m`. -/
def muStage (sl : ℝ) (m : EReal) (blk : List (ℝ × ℝ)) : ℝ :=
  if Keep (alphaLog2 sl m (max m (blockMax blk))) then m.toReal
  else mSafe (max m (blockMax blk))

/-- **The stage's numbers are `Softmax.step`'s for the block `blk`** after the blocks whose
running maximum is `m`. -/
structure StageOk (sl : ℝ) (m : EReal) (blk : List (ℝ × ℝ)) (d : D) : Prop where
  mn : d.stg.mn = erealValue .f32 (max m (blockMax blk))
  kp : d.stg.kp = true ↔ Keep (alphaLog2 sl m (max m (blockMax blk)))
  al : valFloat .f32 d.stg.al = .ok (if Keep (alphaLog2 sl m (max m (blockMax blk))) then 1
    else pow2 (alphaLog2 sl m (max m (blockMax blk))))
  rs : valFloat .f32 d.stg.rs = .ok (blk.map fun q => (2 : ℝ) ^ (sl * q.1 -
    (if Keep (alphaLog2 sl m (max m (blockMax blk))) then m.toReal
      else mSafe (max m (blockMax blk))) * sl)).sum
  /-- The number `alpha` stands for (the rescale's multiplier). -/
  alr : d.stg.alr = if Keep (alphaLog2 sl m (max m (blockMax blk))) then 1
    else pow2 (alphaLog2 sl m (max m (blockMax blk)))

/-- **The update after the stage is `Softmax.step`'s**: `Sm.corr_step_v` for `StageOk`. -/
theorem corr_step_stage {d : D} {sl : ℝ} {bs : List (List (ℝ × ℝ))} {blk : List (ℝ × ℝ)}
    {m : EReal} {l o : ℝ} (hc : Corr sl bs d) (hr : Softmax.run sl bs = ⟨m, l, o⟩)
    (hs : StageOk sl m blk d) : Corr sl (bs ++ [blk]) d.upd :=
  corr_step_v hc hr hs.mn hs.kp hs.al hs.rs

/-- The running maximum of a `Corr` state, read back. -/
theorem mE_of_corr {d : D} {sl : ℝ} {bs : List (List (ℝ × ℝ))} (hc : Corr sl bs d) :
    d.mE = (Softmax.run sl bs).m := by
  unfold D.mE
  rw [hc.1]
  exact eOf_erealValue (run_m_ne_top sl bs)

theorem StageOk.stg_eq {sl : ℝ} {m : EReal} {blk : List (ℝ × ℝ)} {d d' : D}
    (h : StageOk sl m blk d) (hmn : d'.stg.mn = d.stg.mn) (hkp : d'.stg.kp = d.stg.kp)
    (hal : d'.stg.al = d.stg.al) (hrs : d'.stg.rs = d.stg.rs) (halr : d'.stg.alr = d.stg.alr) :
    StageOk sl m blk d' :=
  ⟨by rw [hmn]; exact h.mn, by rw [hkp]; exact h.kp, by rw [hal]; exact h.al,
    by rw [hrs]; exact h.rs, by rw [halr]; exact h.alr⟩

/-- **The score stage after the two exchanges.** At the shuffle of the row maximum a thread whose
running maximum and sum are those of `bs` (`Corr`), whose visible scores are `d.ownScores`, with a
partner lane that exchanged its maximum and its sum (`PeerExchange d dp rv y`) and whose visible
scores are `dp.ownScores`, ends the stage with `StageOk` for every block `blk` whose scores are the
two lanes' visible scores in some order. -/
theorem stage_pair {d dp : D} {rv : Value} {y : ℝ} {sl : ℝ} {bs : List (List (ℝ × ℝ))}
    {blk : List (ℝ × ℝ)} {m : EReal} {l o : ℝ} (hsl : slOf d.e = sl) (hc : Corr sl bs d)
    (hr : Softmax.run sl bs = ⟨m, l, o⟩) (hx : PeerExchange d dp rv y)
    (hperm : (blk.map Prod.fst).Perm (d.ownScores ++ dp.ownScores)) :
    StageOk sl m blk ((d.afterMax rv).afterSumR y) := by
  set bo : List (ℝ × ℝ) := d.ownScores.map fun x => (x, 0) with hbo
  set bp : List (ℝ × ℝ) := dp.ownScores.map fun x => (x, 0) with hbp
  have hbo' : bo.map Prod.fst = d.ownScores := by simp [hbo, List.map_map, Function.comp_def]
  have hbp' : bp.map Prod.fst = dp.ownScores := by simp [hbp, List.map_map, Function.comp_def]
  have hrow := hx.rowOf hbo' hbp'
  have hmE : d.mE = m := by rw [mE_of_corr hc, hr]
  have hperm' : (blk.map Prod.fst).Perm ((bo ++ bp).map Prod.fst) := by
    rw [List.map_append, hbo', hbp']
    exact hperm
  have hbm : blockMax (bo ++ bp) = blockMax blk := (blockMax_perm hperm').symm
  have hmn : d.mnE (eOf rv) = max m (blockMax blk) := by
    rw [mnE_eq hrow, hmE, hbm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show erealValue .f32 (d.mnE (eOf rv)) = _
    rw [hmn]
  · exact kp_iff hsl hmE hmn
  · have := al_val (d := d) (rv := rv) hsl hmE hmn
    simpa [D.afterSumR, D.afterSum] using this
  · have h := hx.rs_eq hbo' hbp'
    rw [hsl, hmE, hbm] at h
    rw [h]
    congr 1
    have := sum_perm (blk := bo ++ bp) (blk' := blk)
      (fun x => (2 : ℝ) ^ (sl * x - (if Keep (alphaLog2 sl m (max m (blockMax blk))) then m.toReal
        else mSafe (max m (blockMax blk))) * sl)) hperm'.symm
    exact this.symm.symm
  · show d.alR (eOf rv) = _
    unfold D.alR D.aLog
    rw [hsl, hmE, hmn]

/-- **The probabilities the stage stores use `m_use` of the step**: the reference maximum of the
state after the first shuffle, whose running maximum is that of the blocks taken in. -/
theorem mUse_stage {d dp : D} {rv : Value} {y : ℝ} {sl : ℝ} {bs : List (List (ℝ × ℝ))}
    {blk : List (ℝ × ℝ)} {m : EReal} {l o : ℝ} (hsl : slOf d.e = sl) (hc : Corr sl bs d)
    (hr : Softmax.run sl bs = ⟨m, l, o⟩) (hx : PeerExchange d dp rv y)
    (hperm : (blk.map Prod.fst).Perm (d.ownScores ++ dp.ownScores)) :
    d.mUse (eOf rv) = muStage sl m blk := by
  set bo : List (ℝ × ℝ) := d.ownScores.map fun x => (x, 0) with hbo
  set bp : List (ℝ × ℝ) := dp.ownScores.map fun x => (x, 0) with hbp
  have hbo' : bo.map Prod.fst = d.ownScores := by simp [hbo, List.map_map, Function.comp_def]
  have hbp' : bp.map Prod.fst = dp.ownScores := by simp [hbp, List.map_map, Function.comp_def]
  have hrow := hx.rowOf hbo' hbp'
  have hmE : d.mE = m := by rw [mE_of_corr hc, hr]
  have hperm' : (blk.map Prod.fst).Perm ((bo ++ bp).map Prod.fst) := by
    rw [List.map_append, hbo', hbp']
    exact hperm
  have hbm : blockMax (bo ++ bp) = blockMax blk := (blockMax_perm hperm').symm
  have hmn : d.mnE (eOf rv) = max m (blockMax blk) := by
    rw [mnE_eq hrow, hmE, hbm]
  unfold D.mUse D.aLog muStage
  rw [hsl, hmE, hmn]

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
