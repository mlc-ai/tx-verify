-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaNth
public import Kernels.FlashAttn4Fwd.Proof.Interface.TcMmaThread

@[expose] public section

/-! # The K steps and the accumulation of the MMAs

The K step of an MMA (`qkStep`, `pvStep`) is its step `j` in its block (`qkStep_eq`,
`pvStep_eq`), and the MMA before it in number is step `j - 1` of the block, or, at step 0 of a
PV block from trip 1 on, step 7 of the stage's PV block of the trip before (`prev_pv`). So:

* `MmaStepFacts`: a step is below 8; a QK MMA overwrites at step 0, a PV MMA exactly at step 0
  of trip 0 (`(pPolls - 1) % n` is the trip); a PV block is whole (its steps are consecutive
  MMAs); PV step `j` reads A at column `128 st + 64 + 8 j`.
* `TcMmaThreadFacts.qk_acc`, `pv_acc`: an accumulating MMA follows one writing the same cells
  (the cells are a function of the block's accumulator column), of its tile, or of the tile
  before for step 0 of a PV block.
* `ScoreFacts.pv_qk`: a PV MMA of tile `u` precedes the stage's QK MMAs of the tiles after `u`.
-/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem kvBlocks_eq (hpre : Pre P L mem0) : kvBlocks P = Mma.trips L := by
  unfold kvBlocks Mma.trips
  rw [skOf_eq hpre]

namespace Mma

/-- The PV block of stage `st` in the trip loop. -/
def loopPv (st : Fin 2) : Fin 8 := if st.val = 0 then 2 else 4

theorem loopPv_spec (b : Fin 8) (hp : isPv b = true) {n t : Nat} (h : TripAt n b t)
    (ht : t ≠ 0) :
    isPv (loopPv (mmaStage b)) = true ∧ mmaStage (loopPv (mmaStage b)) = mmaStage b ∧
      TripAt n (loopPv (mmaStage b)) (t - 1) ∧ blk (loopPv (mmaStage b)) (t - 1) < blk b t := by
  unfold TripAt at h ⊢
  fin_cases b <;> simp [isPv] at hp <;> simp [loopPv, mmaStage, isPv, blk] at h ⊢ <;> omega

theorem tripAt_lt {n t : Nat} {b : Fin 8} (hn : 1 ≤ n) (h : TripAt n b t) : t < n := by
  unfold TripAt at h; split_ifs at h <;> omega

/-- A PV MMA follows the S-full commits of the stage's QK MMAs before it. -/
theorem pv_qk_arith {n i i' t t' j j' : Nat} {b b' : Fin 8} (hn : 1 ≤ n) (hp : isPv b = true)
    (hp' : isPv b' = false) (hs : mmaStage b = mmaStage b') (h : TripAt n b t)
    (h' : TripAt n b' t') (hj : j < 8) (hj' : j' < 8)
    (hlt : 32 * n * i' + 8 * blk b' t' + j' < 32 * n * i + 8 * blk b t + j) :
    n * i' + sv (mmaStage b') b' t' < n * i + pv (mmaStage b) b t := by
  have hb := blk_lt hn h
  have hb' := blk_lt hn h'
  have hsv := sv_own_lt hp' h' hn
  rw [pv_own hp]
  rcases Nat.lt_trichotomy i' i with hi | rfl | hi
  · have : n * (i' + 1) ≤ n * i := Nat.mul_le_mul_left _ hi
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  · unfold TripAt at h h'
    fin_cases b <;> fin_cases b' <;> simp [isPv] at hp hp' <;>
      simp [mmaStage, sv, blk] at hs h h' hlt ⊢ <;> omega
  · have : 32 * n * (i + 1) ≤ 32 * n * i' := Nat.mul_le_mul_left _ hi
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

end Mma

namespace MmaSt

variable {g k : Nat} {d : Mma.D} {b j : Fin 8}

/-- Two MMAs of one block of one trip of one item write the same cells. -/
theorem cell_eq {k' : Nat} {d' : Mma.D} {b' j' : Fin 8} (h : MmaSt L X g k d b j)
    (h' : MmaSt L X g k' d' b' j') (hc : Mma.mmaCol b = Mma.mmaCol b') (cell : Cell) :
    X.MmaCell (g, k) cell ↔ X.MmaCell (g, k') cell := by
  rw [h.cell_iff, h'.cell_iff, hc]

/-- The S-full counts of the stages that hold cells agree at two MMAs of one block of one trip
of one item. -/
theorem sCommits_eq (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {k' : Nat} {d' : Mma.D} {j' : Fin 8}
    (h : MmaSt L X g k d b j) (h' : MmaSt L X g k' d' b j') (hi : d.i = d'.i)
    (htt : d.t = d'.t) {st : Nat} (hst : st < 4) :
    Proof.sCommits L X g st k = Proof.sCommits L X g st k' := by
  by_cases h2 : st < 2
  · rw [show st = (⟨st, h2⟩ : Fin 2).val from rfl, h.sCommits, h'.sCommits, hi, htt]
  · rw [sCommits_high hpre hX ht (by omega) hst, sCommits_high hpre hX ht (by omega) hst]

end MmaSt

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- The MMA before step `j ≥ 1`: step `j - 1` of the block. -/
theorem prev_step (ht : Frame.Tracked (code L) X) {g k : Nat} {d : Mma.D} {b j : Fin 8}
    (h : MmaSt L X g k d b j) (hj : j.val ≠ 0) :
    ∃ k' < k, ∃ d', MmaSt L X g k' d' b ⟨j.val - 1, by omega⟩ ∧ d'.i = d.i ∧ d'.t = d.t := by
  apply mma_at_val hpre hX ht h.tripAt
  rw [h.mmas]
  omega

/-- The MMA before step 0 of a PV block of trip `t ≥ 1`: step 7 of the stage's PV block of trip
`t - 1`. -/
theorem prev_pv (ht : Frame.Tracked (code L) X) {g k : Nat} {d : Mma.D} {b j : Fin 8}
    (h : MmaSt L X g k d b j) (hp : Mma.isPv b = true) (htt : d.t ≠ 0) :
    ∃ k' < k, ∃ d', MmaSt L X g k' d' (Mma.loopPv (Mma.mmaStage b)) 7 ∧ d'.i = d.i ∧
      d'.t = d.t - 1 := by
  obtain ⟨-, -, htrip, hlt⟩ := Mma.loopPv_spec b hp h.tripAt htt
  apply mma_at_val hpre hX ht htrip
  rw [h.mmas]
  omega

/-- **The field `MmaStepFacts.qk_step`.** -/
theorem MmaStepFacts_qk_step (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {cell : Cell} {st : Nat} (hst : st < 2)
    (hi : X.MmaIssue i d s acc mask) (hc : X.MmaCell i cell) (hS : InS st cell) :
    qkStep L X i.1 st i.2 < 8 ∧ (acc = false → qkStep L X i.1 st i.2 = 0) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, h, -, -, rfl, -⟩ := mmaSt_of hpre hX ht hi
  obtain ⟨hp, rfl⟩ := (h.inS_iff hst).mp ⟨cell, hc, hS⟩
  rw [qkStep_eq hpre hX ht h hp]
  refine ⟨j.isLt, fun ha => ?_⟩
  unfold Mma.mmaAcc at ha
  split at ha
  · assumption
  · cases ha

/-- **The field `MmaStepFacts.pv_step`.** -/
theorem MmaStepFacts_pv_step (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {cell : Cell} {st : Nat} (hst : st < 2)
    (hi : X.MmaIssue i d s acc mask) (hc : X.MmaCell i cell) (hO : InO st cell) :
    pvStep L X i.1 st i.2 < 8 ∧ (acc = false ↔
      pvStep L X i.1 st i.2 = 0 ∧ (pPolls L X i.1 st i.2 - 1) % kvBlocks P = 0) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, h, -, -, rfl, -⟩ := mmaSt_of hpre hX ht hi
  obtain ⟨hp, rfl⟩ := h.inO_iff.mp ⟨cell, hc, hO⟩
  rw [pvStep_eq hpre hX ht h hp, h.pPolls, Mma.pv_own hp, kvBlocks_eq hpre]
  have htl := Mma.tripAt_lt (trips_pos hpre) h.tripAt
  have hmod : (Mma.trips L * dd.i + (1 + dd.t) - 1) % Mma.trips L = dd.t := by
    rw [show Mma.trips L * dd.i + (1 + dd.t) - 1 = dd.t + Mma.trips L * dd.i by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt htl]
  rw [hmod]
  refine ⟨j.isLt, ?_⟩
  unfold Mma.mmaAcc
  rw [hp]
  split <;> simp_all

/-- **The field `MmaStepFacts.pv_a`.** -/
theorem MmaStepFacts_pv_a (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {cell : Cell} {st : Nat} (_hst : st < 2)
    (hi : X.MmaIssue i d s acc mask) (hc : X.MmaCell i cell) (hO : InO st cell) :
    ∃ address, s.aTmem = some address ∧
      address % 2 ^ 16 = 128 * st + 64 + 8 * pvStep L X i.1 st i.2 := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, h, -, rfl, -, -⟩ := mmaSt_of hpre hX ht hi
  obtain ⟨hp, rfl⟩ := h.inO_iff.mp ⟨cell, hc, hO⟩
  rw [pvStep_eq hpre hX ht h hp, Mma.mmaSpec_aTmem, hp]
  have := Mma.mmaStage_lt b
  have hj := j.isLt
  exact ⟨_, rfl, Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega : _ < 65536) (by norm_num))⟩

/-- **The field `MmaStepFacts.pv_next`.** -/
theorem MmaStepFacts_pv_next (ht : Frame.Tracked (code L) X) {g st k k' : Nat} (_hst : st < 2)
    (hk : PvAt X g st k) (hj : pvStep L X g st k < 7) (hk' : PvAt X g st k') (hkk : k < k')
    (hlt : pPolls L X g st k < pPolls L X g st k') :
    ∃ k'', k < k'' ∧ k'' < k' ∧ PvAt X g st k'' ∧ pPolls L X g st k'' = pPolls L X g st k := by
  have hn := trips_pos hpre
  obtain ⟨d, b, j, h, hp, rfl⟩ := (pvAt_iff hpre hX ht).mp hk
  obtain ⟨d', b', j', h', hp', hst'⟩ := (pvAt_iff hpre hX ht).mp hk'
  rw [pvStep_eq hpre hX ht h hp] at hj
  have hc := h.count_lt hkk
  rw [h.mmas] at hc
  -- the MMA after `k` is step `j + 1` of the block
  have hnext : 32 * Mma.trips L * d.i + 8 * Mma.blk b d.t + (j.val + 1) + 1 ≤
      ((X.tr g).take k').countP Mma.isMma := by
    by_contra hne
    have he : ((X.tr g).take k').countP Mma.isMma =
        32 * Mma.trips L * d.i + 8 * Mma.blk b d.t + (j.val + 1) := by omega
    rw [h'.mmas] at he
    obtain ⟨hi, rfl, htt, -⟩ := Mma.num_decode hn h'.tripAt h.tripAt j'.isLt (by omega) he
    rw [h.pPolls, h'.pPolls, hi, htt] at hlt
    omega
  obtain ⟨k'', hk'', d'', h'', hi'', ht''⟩ := mma_at_val hpre hX ht h.tripAt (by omega) hnext
  refine ⟨k'', ?_, hk'', (pvAt_iff hpre hX ht).mpr ⟨d'', b, _, h'', hp, rfl⟩, ?_⟩
  · by_contra hle
    have := countP_take_mono Mma.isMma (X.tr g) (show k'' ≤ k by omega)
    rw [h''.mmas, h.mmas, hi'', ht''] at this
    simp at this
  · rw [h''.pPolls, h.pPolls, hi'', ht'']

/-- **The field `TcMmaThreadFacts.qk_acc`.** -/
theorem TcMmaThreadFacts_qk_acc (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat}
    {s : OperandSpec} {mask : List Nat} {cell : Cell} {st : Nat} (hi : X.MmaIssue i d s true mask)
    (hc : X.MmaCell i cell) (hS : InS st cell) :
    ∃ k < i.2, X.MmaCell (i.1, k) cell ∧ sCommits L X i.1 st k = sCommits L X i.1 st i.2 := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, h, -, -, hacc, -⟩ := mmaSt_of hpre hX ht hi
  have hst4 : st < 4 := by
    obtain ⟨row, col, -, hcol, rfl⟩ := (h.cell_iff cell).mp hc
    simp only [InS] at hS
    rcases Mma.mmaCol_cases b with ⟨-, he⟩ | ⟨-, he⟩ <;> have := Mma.mmaStage_lt b <;> omega
  by_cases hj : j.val = 0
  · -- step 0 accumulates only in a PV block of trip `t ≥ 1`
    simp only [Mma.mmaAcc, hj, ↓reduceIte] at hacc
    have hacc' := hacc.symm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc'
    obtain ⟨hp, htt⟩ := hacc'
    obtain ⟨k', hk', d', h', hi', ht'⟩ := prev_pv hpre hX ht h hp htt
    obtain ⟨hp', hs', -, -⟩ := Mma.loopPv_spec b hp h.tripAt htt
    have hcol : Mma.mmaCol b = Mma.mmaCol (Mma.loopPv (Mma.mmaStage b)) := by
      unfold Mma.mmaCol; rw [hp, hp', hs']
    refine ⟨k', hk', (h.cell_eq h' hcol cell).mp hc, ?_⟩
    have h2 : 2 ≤ st := by
      obtain ⟨row, col, -, hcol, rfl⟩ := (h.cell_iff cell).mp hc
      simp only [InS] at hS
      rcases Mma.mmaCol_cases b with ⟨hq, -⟩ | ⟨-, he⟩
      · rw [hp] at hq; cases hq
      · have := Mma.mmaStage_lt b; omega
    rw [sCommits_high hpre hX ht h2 hst4, sCommits_high hpre hX ht h2 hst4]
  · obtain ⟨k', hk', d', h', hi', ht'⟩ := prev_step hpre hX ht h hj
    exact ⟨k', hk', (h.cell_eq h' rfl cell).mp hc,
      (h.sCommits_eq hpre hX ht h' hi'.symm ht'.symm hst4).symm⟩

/-- **The field `TcMmaThreadFacts.pv_acc`.** -/
theorem TcMmaThreadFacts_pv_acc (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat}
    {s : OperandSpec} {mask : List Nat} {cell : Cell} {st : Nat} (hi : X.MmaIssue i d s true mask)
    (hc : X.MmaCell i cell) (hO : InO st cell) :
    ∃ k < i.2, X.MmaCell (i.1, k) cell ∧ pPolls L X i.1 st i.2 ≤ pPolls L X i.1 st k + 1 := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, h, -, -, hacc, -⟩ := mmaSt_of hpre hX ht hi
  obtain ⟨hp, rfl⟩ := h.inO_iff.mp ⟨cell, hc, hO⟩
  by_cases hj : j.val = 0
  · simp only [Mma.mmaAcc, hj, ↓reduceIte] at hacc
    have hacc' := hacc.symm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc'
    obtain ⟨-, htt⟩ := hacc'
    obtain ⟨k', hk', d', h', hi', ht'⟩ := prev_pv hpre hX ht h hp htt
    obtain ⟨hp', hs', -, -⟩ := Mma.loopPv_spec b hp h.tripAt htt
    have hcol : Mma.mmaCol b = Mma.mmaCol (Mma.loopPv (Mma.mmaStage b)) := by
      unfold Mma.mmaCol; rw [hp, hp', hs']
    refine ⟨k', hk', (h.cell_eq h' hcol cell).mp hc, ?_⟩
    rw [h.pPolls, ← hs', h'.pPolls, Mma.pv_own hp', hs', Mma.pv_own hp, hi', ht']
    omega
  · obtain ⟨k', hk', d', h', hi', ht'⟩ := prev_step hpre hX ht h hj
    refine ⟨k', hk', (h.cell_eq h' rfl cell).mp hc, ?_⟩
    rw [h.pPolls, h'.pPolls, hi', ht']
    omega

/-- **The field `ScoreFacts.pv_qk`.** -/
theorem ScoreFacts_pv_qk (ht : Frame.Tracked (code L) X) {i i' : EvId} {cell cell' : Cell}
    {st : Nat} (hi : IsMma X i) (hi' : IsMma X i') (hg : i.1 = i'.1) (hc : X.MmaCell i cell)
    (hO : InO st cell) (hc' : X.MmaCell i' cell') (hS : InS st cell')
    (hle : pPolls L X i.1 st i.2 ≤ sCommits L X i'.1 st i'.2) : i.2 < i'.2 := by
  obtain ⟨g, k⟩ := i
  obtain ⟨g', k'⟩ := i'
  simp only at hg hle ⊢
  subst hg
  obtain ⟨dd, s, acc, mask, hi⟩ := hi
  obtain ⟨dd', s', acc', mask', hi'⟩ := hi'
  obtain ⟨d, b, j, h, -⟩ := mmaSt_of hpre hX ht hi
  obtain ⟨d', b', j', h', -⟩ := mmaSt_of hpre hX ht hi'
  obtain ⟨hp, rfl⟩ := h.inO_iff.mp ⟨cell, hc, hO⟩
  obtain ⟨hp', hs⟩ := (h'.inS_iff (Mma.mmaStage_lt b)).mp ⟨cell', hc', hS⟩
  have hs' : Mma.mmaStage b' = Mma.mmaStage b := Fin.ext hs
  by_contra hge
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hge) with hlt | heq
  · have hc := h'.count_lt hlt
    rw [h'.mmas, h.mmas] at hc
    have := Mma.pv_qk_arith (trips_pos hpre) hp hp' hs'.symm h.tripAt h'.tripAt j.isLt j'.isLt hc
    rw [h.pPolls, h'.sCommits] at hle
    rw [hs'] at this
    omega
  · subst heq
    obtain ⟨-, rfl, -⟩ := h.unique h'
    rw [hp] at hp'
    cases hp'

end
end PTX.Kernels.FlashAttn4Fwd.Proof
