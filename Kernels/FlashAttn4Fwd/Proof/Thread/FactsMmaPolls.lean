-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCount
public import Kernels.FlashAttn4Fwd.Proof.Interface.Exit
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemLife

@[expose] public section

/-! # The MMA thread's polls and commits at its MMAs

The counts of `MmaSt` at an MMA of block `b` (`sv`, `pv`, `p2v`, `ofv`) compare as the fields
need:

* a QK MMA of stage `st` follows as many successful P-ready and second P-ready polls of the
  stage as commits to its S-full object (`ScoreFacts_qk_polls`);
* a PV MMA of stage `st` follows `t + 1` P-ready polls of the item's stage (at least one), as
  many as S-full commits; its A operand is the stage's P columns `128 st + 64 + 8 j …`, and the
  columns `112 …` (steps 6, 7) are read after the second P-ready poll of the tile
  (`ScoreFacts_pv_polls`);
* an MMA is in an item of the cluster, before the item's O-full commits
  (`ExitFacts_mma_ofull`, `TmemLifeFacts_mma_item`, `RouteFacts_mma_pv`).

No thread commits to the P-ready objects, which `sCommits` names for the stages 2 and 3
(`sCommits_high`): every commit is the MMA warp's, to an S-full, KV-empty, Q-empty or O-full
object. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Mma

theorem qk_le {b : Fin 8} (hp : isPv b = false) (j : Fin 8) (t : Nat) :
    sv (mmaStage b) b t ≤ pv (mmaStage b) b t ∧ sv (mmaStage b) b t ≤ p2v (mmaStage b) b j t := by
  fin_cases b <;> simp_all [isPv, sv, pv, p2v, mmaStage]

theorem pv_le {b : Fin 8} (hp : isPv b = true) (t : Nat) :
    1 ≤ pv (mmaStage b) b t ∧ sv (mmaStage b) b t ≤ pv (mmaStage b) b t ∧
      ofv (mmaStage b) b = 0 ∧ pv (mmaStage b) b t = 1 + t := by
  fin_cases b <;> simp_all [isPv, sv, pv, ofv, mmaStage]

theorem pv_p2 {b : Fin 8} (hp : isPv b = true) {j : Fin 8} (hj : 6 ≤ j.val) (t : Nat) :
    p2v (mmaStage b) b j t = pv (mmaStage b) b t := by
  fin_cases b <;> simp_all [isPv, p2v, pv, mmaStage]

theorem ofv_one (b : Fin 8) : ofv 1 b = 0 := by
  fin_cases b <;> rfl

/-- The A cells of a PV MMA: the stage's P columns of its step, in the thread's pair. -/
theorem aCell_pv {L : Launch} {g : Nat} {d : D} {b j : Fin 8} (hp : isPv b = true)
    {index : Nat} {c : Cell} {pos : Nat} (h : aCell (mmaSpec L g d b j) index = some (c, pos)) :
    128 * (mmaStage b).val + 64 + 8 * j.val ≤ c.column ∧
      c.column < 128 * (mmaStage b).val + 64 + 8 * j.val + 8 ∧
      (c.cta = pairLo L g ∨ c.cta = pairLo L g + 1) := by
  have ha : (mmaSpec L g d b j).aTmem = some (128 * (mmaStage b).val + 64 + 8 * j.val) := by
    rw [mmaSpec_aTmem, hp]; rfl
  have hd : (mmaSpec L g d b j).descriptor = pvDesc := by rw [mmaSpec_desc, hp]; rfl
  have hst := (mmaStage b).isLt
  have hj := j.isLt
  simp only [aCell, ha, hd, Option.bind_some, pvDesc, Kind.k, Kind.width, mmaSpec_lowCta,
    mmaSpec_highCta] at h
  have hmod : (128 * (mmaStage b).val + 64 + 8 * j.val) % 2 ^ 16 =
      128 * (mmaStage b).val + 64 + 8 * j.val :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega : _ < 65536) (by norm_num))
  rw [hmod] at h
  split_ifs at h with hc
  all_goals
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; simp⟩

end Mma

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- **No commits to the P-ready objects**: the S-full counts of the stages 2 and 3 (the
P-ready objects' addresses) are zero. -/
theorem sCommits_high (ht : Frame.Tracked (code L) X) {g k st : Nat} (h2 : 2 ≤ st) (h4 : st < 4) :
    sCommits L X g st k = 0 := by
  unfold sCommits
  apply List.countP_eq_zero.mpr
  intro e he
  have he' : e ∈ X.tr g := List.mem_of_mem_take he
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he'
  have hb : sFullBar L (ctaOf L g) st = FBar.loc L (ctaOf L g) (.pReady ⟨st - 2, by omega⟩) := by
    simp only [sFullBar, FBar.loc, FBar.off, Loc.mk.injEq, true_and]
    omega
  rw [hb]
  cases hk : (X.tr g)[n].kind with
  | tc kd =>
    cases kd with
    | commit sp =>
      rw [commitsTo_of_kind hk]
      have hget : X.get (g, n) = some ⟨(X.tr g)[n].pc, .tc (.commit sp)⟩ := by
        show (X.tr g)[n]? = _
        rw [List.getElem?_eq_getElem hn, ← hk]
      obtain ⟨-, d, t, ins, o, -, -, hh, hc, hf⟩ := mma_commitRun hpre hX ht hget
      have hg := Frame.lt_of_get hX hget
      obtain ⟨c, -, rfl⟩ := Mma.commit_site hpre hg hh hc hf rfl
      rw [show (Mma.cSpec L g (Mma.bar L g (Mma.cBar L d c))).mbar =
        FBar.loc L (ctaOf L g) (Mma.cBar L d c) from rfl, decide_eq_true_iff]
      intro hl
      have := (FBar.loc_inj hl).1
      fin_cases c <;> simp [Mma.cBar] at this
    | _ => simp [commitsTo, hk]
  | _ => simp [commitsTo, hk]

/-- **The field `ScoreFacts.qk_polls`.** -/
theorem ScoreFacts_qk_polls (ht : Frame.Tracked (code L) X) {i : EvId} {cell : Cell} {st : Nat}
    (hi : IsMma X i) (hc : X.MmaCell i cell) (hS : InS st cell) :
    sCommits L X i.1 st i.2 ≤ pPolls L X i.1 st i.2 ∧
      sCommits L X i.1 st i.2 ≤ p2Polls L X i.1 st i.2 := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, s, acc, mask, hi⟩ := hi
  obtain ⟨d, b, j, h, -⟩ := mmaSt_of hpre hX ht hi
  by_cases hst : st < 2
  · obtain ⟨hp, rfl⟩ := (h.inS_iff hst).mp ⟨cell, hc, hS⟩
    rw [h.sCommits, h.pPolls, h.p2Polls]
    have := Mma.qk_le hp j d.t
    omega
  · by_cases h4 : st < 4
    · rw [sCommits_high hpre hX ht (by omega) h4]
      omega
    · obtain ⟨row, col, -, hcol, rfl⟩ := (h.cell_iff cell).mp hc
      simp only [InS] at hS
      rcases Mma.mmaCol_cases b with ⟨-, he⟩ | ⟨-, he⟩ <;> have := Mma.mmaStage_lt b <;> omega

/-- **The field `ScoreFacts.pv_polls`.** -/
theorem ScoreFacts_pv_polls (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {cell : Cell} {st : Nat} (hi : X.MmaIssue i d s acc mask)
    (hc : X.MmaCell i cell) (hO : InO st cell) :
    1 ≤ pPolls L X i.1 st i.2 ∧ sCommits L X i.1 st i.2 ≤ pPolls L X i.1 st i.2 ∧
      s.aTmem.isSome ∧ ∀ index c pos, aCell s index = some (c, pos) →
        InP st c ∧ leadCta c.cta = ctaOf L i.1 ∧
          (InPHigh st c → p2Polls L X i.1 st i.2 = pPolls L X i.1 st i.2) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, h, -, rfl, -, -⟩ := mmaSt_of hpre hX ht hi
  obtain ⟨hp, rfl⟩ := h.inO_iff.mp ⟨cell, hc, hO⟩
  have hr0 := h.item.2
  simp only [Mma.rank] at hr0
  obtain ⟨h1, h2, -, -⟩ := Mma.pv_le hp dd.t
  rw [h.sCommits, h.pPolls, h.p2Polls]
  refine ⟨by omega, by omega, by rw [Mma.mmaSpec_aTmem, hp]; rfl, fun index c pos hac => ?_⟩
  obtain ⟨hlo, hhi, hcta⟩ := Mma.aCell_pv hp hac
  have hj := j.isLt
  refine ⟨⟨by omega, by omega⟩, ?_, fun hH => ?_⟩
  · simp only [leadCta, ctaOf, Mma.pairLo] at hcta ⊢
    omega
  · simp only [InPHigh] at hH
    rw [Mma.pv_p2 hp (by omega)]

/-- **The field `RouteFacts.mma_pv`.** -/
theorem RouteFacts_mma_pv (ht : Frame.Tracked (code L) X) {x : EvId} {cell : Cell} {st : Nat}
    (hi : IsMma X x) (hc : X.MmaCell x cell) (hO : InO st cell) :
    kvTiles L * oFullCommits L X x.1 st x.2 < pPolls L X x.1 st x.2 := by
  obtain ⟨g, k⟩ := x
  obtain ⟨dd, s, acc, mask, hi⟩ := hi
  obtain ⟨d, b, j, h, -⟩ := mmaSt_of hpre hX ht hi
  obtain ⟨hp, rfl⟩ := h.inO_iff.mp ⟨cell, hc, hO⟩
  obtain ⟨-, -, h3, h4⟩ := Mma.pv_le hp d.t
  rw [h.oFullCommits, h.pPolls, h3, h4]
  show Mma.trips L * (d.i + 0) < _
  rw [Nat.add_zero]
  omega

/-- **The field `ExitFacts.mma_ofull`.** -/
theorem ExitFacts_mma_ofull (ht : Frame.Tracked (code L) X) {g k d : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue (g, k) d s acc mask) :
    ∃ st < 2,
      workOf L g (((X.tr g).take k).countP (commitsTo (oFullBar L (ctaOf L g) st))) <
        totOf L := by
  obtain ⟨dd, b, j, h, -⟩ := mmaSt_of hpre hX ht hi
  refine ⟨1, by decide, ?_⟩
  have := h.oFullCommits 1
  simp only [oFullCommits, Fin.val_one, Mma.ofv_one, Nat.add_zero] at this
  rw [this]
  exact h.item.1

/-- **The field `TmemLifeFacts.mma_item`.** -/
theorem TmemLifeFacts_mma_item (ht : Frame.Tracked (code L) X) {x : EvId} (hi : IsMma X x) :
    ∃ st < 2, workOf L x.1 (oFullCommits L X x.1 st x.2) < totOf L := by
  obtain ⟨g, k⟩ := x
  obtain ⟨dd, s, acc, mask, hi⟩ := hi
  exact ExitFacts_mma_ofull hpre hX ht hi

end
end PTX.Kernels.FlashAttn4Fwd.Proof
