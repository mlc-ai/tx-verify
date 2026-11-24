-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaOrigin
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc
public import Kernels.FlashAttn4Fwd.Proof.Interface.Async

@[expose] public section

/-! # The MMAs' issue: shape, pair and result cells

Every MMA is its site's (`mma_origin`): the QK or PV instruction descriptor (M = 256 over the
pair, N = 128), K-major or MN-major 128-byte-swizzled shared descriptors, the thread's pair, the
accumulator column `mmaCol b` (0, 128, 256 or 384), the zero lane masks and, for PV, the A
column `128 st + 64 + 8 j`. From that:

* the issue shape is valid and every operand byte has a location (`TcFacts_mma_shape`);
* the operand CTAs are the issuer's pair (`AsyncFacts_mma_pair`);
* the cells an MMA writes are its result cells (`TcFacts_mma_reads`, no lane is masked), row
  `r < 256` and column `c < 128` at lane `r % 128` of the low (`r < 128`) or high CTA of the pair
  and column `mmaCol b + c` (`mmaCell_iff`); so they are all in one stage's scores or all in one
  stage's accumulator (`ScoreFacts_mma_cells`), and two MMAs writing a region of one pair use
  the same accumulator (`ScoreFacts_mma_acc'`).

`TcFacts.qk_smem` and `ScoreFacts.mma_acc` are not true as the interface states them: a PV MMA
writes columns `256 …` that `InS 2` and `InS 3` contain, and MMAs of two clusters write the
same stage region of their own pairs. The theorems below add the hypotheses `st < 2`
(`TcFacts_qk_smem'`) and that the two cells are in one pair (`ScoreFacts_mma_acc'`), which every
use in the protocol layer has. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Mma

/-- A shared descriptor of the MMA warp's form: 128-byte swizzle, relative leading offset, first
LUT segment, base offset 0. -/
def SwOk (sd : TcShared.Descriptor) : Prop :=
  sd.swizzle = .b128 ∧ sd.leadingAbsolute = false ∧ sd.lutSecondSegment = false ∧
    sd.baseOffset = 0

theorem swOk_k (S : Nat) : SwOk (kMajorDesc S) := ⟨rfl, rfl, rfl, rfl⟩

theorem swOk_mn (S : Nat) : SwOk (mnMajorDesc S) := ⟨rfl, rfl, rfl, rfl⟩

/-- Every byte of a shared operand of the kernel's descriptors has a location. -/
theorem byteLoc_some {dsc : Descriptor} (hd : dsc = qkDesc ∨ dsc = pvDesc)
    {sa sb : TcShared.Descriptor} (ha : SwOk sa) (hb : SwOk sb) {lo hi : Nat} {aT : Option Nat}
    {col : Collectors} {op : Operand} {index : Nat} (hidx : index < op.bytes dsc)
    (hop : op = .b ∨ aT = none) :
    ∃ loc, (⟨dsc, sa, sb, lo, hi, aT, col⟩ : OperandSpec).byteLoc op index = some loc := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  rcases hd with rfl | rfl <;> cases op <;>
    simp_all [OperandSpec.byteLoc, TcShared.byteAddress, Operand.bytes, Operand.rows,
      Operand.extent, Operand.major, qkDesc, pvDesc, Kind.k, Kind.width, CtaGroup.size] <;>
    exact ⟨⟨by decide, by omega⟩, by simp only [show index % 2 ≤ 1 by omega, ↓reduceIte,
      Option.bind_some, Option.some.injEq, exists_eq']⟩

theorem mmaSpec_desc (L : Launch) (g : Nat) (d : D) (b j : Fin 8) :
    (mmaSpec L g d b j).descriptor = if isPv b then pvDesc else qkDesc := by
  unfold mmaSpec; split <;> rfl

theorem mmaSpec_aTmem (L : Launch) (g : Nat) (d : D) (b j : Fin 8) :
    (mmaSpec L g d b j).aTmem =
      if isPv b then some (128 * (mmaStage b).val + 64 + 8 * j.val) else none := by
  unfold mmaSpec; split <;> rfl

theorem mmaSpec_lowCta (L : Launch) (g : Nat) (d : D) (b j : Fin 8) :
    (mmaSpec L g d b j).lowCta = pairLo L g := by
  unfold mmaSpec; split <;> rfl

theorem mmaSpec_highCta (L : Launch) (g : Nat) (d : D) (b j : Fin 8) :
    (mmaSpec L g d b j).highCta = pairLo L g + 1 := by
  unfold mmaSpec; split <;> rfl

theorem mmaSpec_descOk (L : Launch) (g : Nat) (d : D) (b j : Fin 8) :
    (mmaSpec L g d b j).descriptor = qkDesc ∨ (mmaSpec L g d b j).descriptor = pvDesc := by
  rw [mmaSpec_desc]; split <;> simp

/-- The accumulator columns: S of stage 0 or 1 (QK blocks), O of stage 0 or 1 (PV blocks). -/
theorem mmaCol_cases (b : Fin 8) :
    (isPv b = false ∧ mmaCol b = 128 * (mmaStage b).val) ∨
      (isPv b = true ∧ mmaCol b = 256 + 128 * (mmaStage b).val) := by
  fin_cases b <;> decide

theorem mmaStage_lt (b : Fin 8) : (mmaStage b).val < 2 := (mmaStage b).isLt

/-- The result cells of an MMA of the kernel's descriptors at a column below 384. -/
theorem resultCell_iff {s : OperandSpec} (hd : s.descriptor = qkDesc ∨ s.descriptor = pvDesc)
    {base row col : Nat} {cell : Cell} (hb : base + 128 ≤ 512) :
    resultCell s base row col = some cell ↔ row < 256 ∧ col < 128 ∧
      cell = ⟨if row < 128 then s.lowCta else s.highCta, row % 128, base + col⟩ := by
  have h0 : base / 2 ^ 16 = 0 := by omega
  have h1 : base % 2 ^ 16 = base := by omega
  rcases hd with hd | hd <;>
    simp only [resultCell, hd, h0, h1, qkDesc, pvDesc, CtaGroup.size, resultColumns,
      LaneAligned, true_or, ↓reduceIte, Nat.reduceMul, Nat.reduceDiv] <;>
    by_cases hr : row < 256 <;> by_cases hc : col < 128 <;>
    simp +decide [hr, hc, show base + 128 ≤ 512 from hb, eq_comm]

/-- With the zero lane masks an MMA writes all its result cells. -/
theorem writeCell_eq {s : OperandSpec} (hd : s.descriptor = qkDesc ∨ s.descriptor = pvDesc)
    {base row col : Nat} (hb : base + 128 ≤ 512) :
    writeCell s base (List.replicate 8 0) row col = resultCell s base row col := by
  have hg : s.descriptor.group = .two ∧ s.descriptor.m = 256 := by
    rcases hd with hd | hd <;> rw [hd] <;> exact ⟨rfl, rfl⟩
  unfold writeCell
  have hv : OutputMaskValid s.descriptor.group (List.replicate 8 0) := by rw [hg.1]; decide
  simp only [hv, not_true_eq_false, ↓reduceIte]
  cases hr : resultCell s base row col with
  | none => rfl
  | some cell =>
    obtain ⟨hrow, -, rfl⟩ := (resultCell_iff hd hb).mp hr
    simp only [Option.bind_eq_bind, Option.bind_some, hg.2, hg.1, CtaGroup.size]
    have hl : (row / (256 / 2) * 128 + row % 128) / 32 < 8 := by omega
    rw [List.getElem?_replicate]
    simp [hl]

end Mma

/-- Two MMA issues at one event are one. -/
theorem mmaIssue_unique {i : EvId} {d d' : Nat} {s s' : OperandSpec} {a a' : Bool}
    {m m' : List Nat} (h : X.MmaIssue i d s a m) (h' : X.MmaIssue i d' s' a' m') :
    d = d' ∧ s = s' ∧ a = a' ∧ m = m' := by
  obtain ⟨pc, h⟩ := h
  obtain ⟨pc', h'⟩ := h'
  rw [h] at h'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at h'
  exact h'.2

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- **The cells an MMA writes**: lane `r % 128` of the low (`r < 128`) or high CTA of the
thread's pair, at column `mmaCol b + c`, for `r < 256`, `c < 128`. -/
theorem mmaCell_iff (ht : Frame.Tracked (code L) X) {g k dd : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue (g, k) dd s acc mask) :
    ∃ (d : Mma.D) (b j : Fin 8), Frame.stateAt (code L) X g k = some (some (.inr (.mma d))) ∧
      d.site = .mma b j ∧ Mma.Counts L g d ((X.tr g).take k) ∧ Mma.Inv L g d ∧
      g < L.threads ∧ warpOf L g = 12 ∧ dd = Mma.mmaCol b ∧ s = Mma.mmaSpec L g d b j ∧
      acc = Mma.mmaAcc d b j ∧ mask = List.replicate 8 0 ∧
      ∀ cell, X.MmaCell (g, k) cell ↔ ∃ row col, row < 256 ∧ col < 128 ∧
        cell = ⟨if row < 128 then Mma.pairLo L g else Mma.pairLo L g + 1, row % 128,
          Mma.mmaCol b + col⟩ := by
  obtain ⟨d, b, j, hσ, hs, hJ, hinv, hg, hw, rfl, rfl, rfl, rfl⟩ := mma_origin hpre hX ht hi
  have hb : Mma.mmaCol b + 128 ≤ 512 := by
    rcases Mma.mmaCol_cases b with ⟨-, h⟩ | ⟨-, h⟩ <;> have := Mma.mmaStage_lt b <;> omega
  refine ⟨d, b, j, hσ, hs, hJ, hinv, hg, hw, rfl, rfl, rfl, rfl, fun cell => ⟨?_, ?_⟩⟩
  · rintro ⟨d', s', a', m', row, col, hi', hw'⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := mmaIssue_unique hi' hi
    rw [Mma.writeCell_eq (Mma.mmaSpec_descOk ..) hb, Mma.resultCell_iff (Mma.mmaSpec_descOk ..) hb,
      Mma.mmaSpec_lowCta, Mma.mmaSpec_highCta] at hw'
    exact ⟨row, col, hw'⟩
  · rintro ⟨row, col, hr, hc, rfl⟩
    refine ⟨_, _, _, _, row, col, hi, ?_⟩
    rw [Mma.writeCell_eq (Mma.mmaSpec_descOk ..) hb, Mma.resultCell_iff (Mma.mmaSpec_descOk ..) hb,
      Mma.mmaSpec_lowCta, Mma.mmaSpec_highCta]
    exact ⟨hr, hc, rfl⟩

/-! ### The fields -/

/-- **The field `AsyncFacts.mma_pair`.** -/
theorem AsyncFacts_mma_pair (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat}
    {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i d s acc mask) :
    s.lowCta / 2 = ctaOf L i.1 / 2 ∧ s.highCta / 2 = ctaOf L i.1 / 2 := by
  obtain ⟨g, k⟩ := i
  obtain ⟨d, b, j, -, -, -, -, -, -, -, rfl, -⟩ := mma_origin hpre hX ht hi
  rw [Mma.mmaSpec_lowCta, Mma.mmaSpec_highCta]
  simp only [Mma.pairLo, ctaOf]
  omega

/-- **The field `TcFacts.mma_shape`.** -/
theorem TcFacts_mma_shape (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i d s acc mask) : IssueShape L i d s mask := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, -, -, -, -, hg, -, rfl, rfl, -, rfl⟩ := mma_origin hpre hX ht hi
  have hb := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hb
  have hcta := cta_lt hg
  have hcl := hpre.cluster
  have hgr := hpre.grid
  unfold ctaOf at hcta
  have hcol : Mma.mmaCol b + 128 ≤ 512 := by
    rcases Mma.mmaCol_cases b with ⟨-, h⟩ | ⟨-, h⟩ <;> have := Mma.mmaStage_lt b <;> omega
  have hdesc := Mma.mmaSpec_descOk L g dd b j
  have henc : ∀ S, S % 16 = 0 → S < 2 ^ 18 →
      SharedEncoded (kMajorDesc S) ∧ SharedEncoded (mnMajorDesc S) := fun S h1 h2 => by
    simp only [SharedEncoded, kMajorDesc, mnMajorDesc]
    exact ⟨⟨h2, by norm_num, by norm_num, h1, by norm_num, by norm_num⟩,
      ⟨h2, by norm_num, by norm_num, h1, by norm_num, by norm_num⟩⟩
  refine ⟨hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hdesc with h | h <;> rw [h] <;> decide
  · rcases hdesc with h | h <;> rw [h] <;> decide
  · rw [OperandSpec.matchesLaunch_iff]
    simp only [Mma.mmaSpec_lowCta, Mma.mmaSpec_highCta]
    have hg2 : (Mma.mmaSpec L g dd b j).descriptor.group.size = 2 := by
      rcases hdesc with h | h <;> rw [h] <;> rfl
    rw [hg2]
    have h1 := hpre.oneDimLaunch.1
    simp only [Launch.peerCta, Launch.oneDim_rankOfCta h1, Launch.oneDim_clusterOfCta h1,
      Launch.oneDim_clusterStart h1, Launch.oneDim_clusterSizeOf h1, hcl, Mma.pairLo]
    refine ⟨?_, ?_⟩ <;> split_ifs with h
    · congr 1; omega
    · exact absurd ⟨hcta, by omega, by omega⟩ h
    · congr 1; omega
    · exact absurd ⟨hcta, by omega, by omega⟩ h
  · unfold Mma.mmaSpec
    split
    · obtain ⟨-, h16, hS⟩ := Mma.vWord_eq hpre (Mma.vSlot L dd) j
      exact (henc _ h16 hS).2
    · have hst := (Mma.mmaStage b).isLt
      have hj := j.isLt
      refine (henc _ ?_ ?_).1 <;> simp only [qStepStart, FBar.regionOff] <;> omega
  · unfold Mma.mmaSpec
    split
    · obtain ⟨-, h16, hS⟩ := Mma.vWord_eq hpre (Mma.vSlot L dd) j
      exact (henc _ h16 hS).2
    · obtain ⟨-, h16, hS⟩ := Mma.kWord_eq hpre (Mma.kSlot L dd b) j
      exact (henc _ h16 hS).1
  · left
    simp only [show Mma.mmaCol b / 2 ^ 16 = 0 by omega]
  · intro address _ hh
    rcases hdesc with h | h <;> rw [h] at hh <;> simp [halfDatapath, Mma.qkDesc, Mma.pvDesc] at hh
  · rcases hdesc with h | h <;> rw [h] <;>
      simp only [resultColumns, Mma.qkDesc, Mma.pvDesc, CtaGroup.size, true_or, ↓reduceIte] <;>
      omega
  · intro op index hidx
    have hsw : Mma.SwOk (Mma.mmaSpec L g dd b j).a ∧ Mma.SwOk (Mma.mmaSpec L g dd b j).b := by
      unfold Mma.mmaSpec; split
      · exact ⟨Mma.swOk_mn _, Mma.swOk_mn _⟩
      · exact ⟨Mma.swOk_k _, Mma.swOk_k _⟩
    cases hp : Mma.isPv b
    · have hn : (Mma.mmaSpec L g dd b j).aTmem = none := by
        rw [Mma.mmaSpec_aTmem, hp]; rfl
      left
      exact Mma.byteLoc_some hdesc hsw.1 hsw.2 hidx (.inr hn)
    · cases op
      · right
        refine ⟨rfl, ?_⟩
        have hd : (Mma.mmaSpec L g dd b j).descriptor = Mma.pvDesc := by
          rw [Mma.mmaSpec_desc, hp]; rfl
        have ha : (Mma.mmaSpec L g dd b j).aTmem =
            some (128 * (Mma.mmaStage b).val + 64 + 8 * j.val) := by
          rw [Mma.mmaSpec_aTmem, hp]; rfl
        have hst := Mma.mmaStage_lt b
        have hj := j.isLt
        have hidx' : index < 8192 := by
          rw [hd] at hidx
          simpa [Operand.bytes, Operand.rows, Operand.extent, Mma.pvDesc, Kind.k, Kind.width]
            using hidx
        simp +decide [aCell, ha, hd, Mma.pvDesc, Kind.k, Kind.width, Operand.rows,
          Operand.extent, CtaGroup.size, halfDatapath]
        omega
      · left
        exact Mma.byteLoc_some hdesc hsw.1 hsw.2 hidx (.inl rfl)

/-- **The field `TcFacts.mma_reads`.** -/
theorem TcFacts_mma_reads (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {row col : Nat} {cell : Cell} (hi : X.MmaIssue i d s acc mask)
    (hr : resultCell s d row col = some cell) : X.MmaCell i cell := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, -, -, -, -, -, -, rfl, rfl, -, rfl⟩ := mma_origin hpre hX ht hi
  have hb : Mma.mmaCol b + 128 ≤ 512 := by
    rcases Mma.mmaCol_cases b with ⟨-, h⟩ | ⟨-, h⟩ <;> have := Mma.mmaStage_lt b <;> omega
  exact ⟨_, _, _, _, row, col, hi, by rw [Mma.writeCell_eq (Mma.mmaSpec_descOk ..) hb]; exact hr⟩

/-- **The field `TcFacts.mma_cell`.** -/
theorem TcFacts_mma_cell (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i d s acc mask) : ∃ cell, X.MmaCell i cell := by
  obtain ⟨g, k⟩ := i
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := mmaCell_iff hpre hX ht hi
  exact ⟨_, (hc _).mpr ⟨0, 0, by decide, by decide, rfl⟩⟩

/-- The column range of an MMA's cells decides its block's kind and stage. -/
theorem mma_cell_col (ht : Frame.Tracked (code L) X) {g k dd : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {cell : Cell} (hi : X.MmaIssue (g, k) dd s acc mask)
    (hc : X.MmaCell (g, k) cell) :
    ∃ (d : Mma.D) (b j : Fin 8), d.site = .mma b j ∧ dd = Mma.mmaCol b ∧
      s = Mma.mmaSpec L g d b j ∧ Mma.mmaCol b ≤ cell.column ∧
      cell.column < Mma.mmaCol b + 128 ∧ leadCta cell.cta = Mma.pairLo L g := by
  obtain ⟨d, b, j, -, hs, -, -, -, -, rfl, rfl, -, -, hcell⟩ := mmaCell_iff hpre hX ht hi
  obtain ⟨row, col, -, hcol, rfl⟩ := (hcell cell).mp hc
  refine ⟨d, b, j, hs, rfl, rfl, by simp, by simp; omega, ?_⟩
  simp only [leadCta, Mma.pairLo]
  split <;> omega

/-- **The field `TcFacts.qk_smem`**, for the two score stages: an MMA writing a cell of stage
`st`'s scores reads A from shared memory. (For `st ≥ 2` the field is false: `InS 2` and
`InS 3` are the accumulator columns that PV MMAs write.) -/
theorem TcFacts_qk_smem' (ht : Frame.Tracked (code L) X) {i : EvId} {d st : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {cell : Cell} (hst : st < 2) (hi : X.MmaIssue i d s acc mask)
    (hc : X.MmaCell i cell) (hS : InS st cell) : s.aTmem = none := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, -, -, rfl, h1, h2, -⟩ := mma_cell_col hpre hX ht hi hc
  rw [Mma.mmaSpec_aTmem]
  unfold InS at hS
  have := Mma.mmaStage_lt b
  rcases Mma.mmaCol_cases b with ⟨hp, h⟩ | ⟨hp, h⟩ <;> rw [hp]
  · rfl
  · omega

/-- **The field `ScoreFacts.mma_cells`.** -/
theorem ScoreFacts_mma_cells (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i d s acc mask) :
    i.1 < L.threads ∧ warpOf L i.1 = 12 ∧
      leadCta (ctaOf L i.1) = ctaOf L i.1 ∧ ∃ st < 2,
        (∀ cell, X.MmaCell i cell → InS st cell ∧ leadCta cell.cta = ctaOf L i.1) ∨
          (∀ cell, X.MmaCell i cell → InO st cell ∧ leadCta cell.cta = ctaOf L i.1) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, -, hs, -, hinv, hg, hw, rfl, rfl, -, -, hcell⟩ := mmaCell_iff hpre hX ht hi
  have hr0 : Mma.rank L g = 0 := (hinv.i (by rw [hs]; trivial)).2
  have hlead : leadCta (ctaOf L g) = ctaOf L g := by
    simp only [Mma.rank] at hr0; simp only [leadCta, ctaOf]; omega
  have hpl : Mma.pairLo L g = ctaOf L g := by
    simp only [Mma.rank] at hr0; simp only [Mma.pairLo, ctaOf]; omega
  have hcta : ∀ row : Nat, leadCta (if row < 128 then Mma.pairLo L g else Mma.pairLo L g + 1) =
      ctaOf L g := by
    intro row; rw [hpl]; simp only [leadCta, ctaOf] at hlead ⊢; split <;> omega
  refine ⟨hg, hw, hlead, (Mma.mmaStage b).val, Mma.mmaStage_lt b, ?_⟩
  rcases Mma.mmaCol_cases b with ⟨-, h⟩ | ⟨-, h⟩
  · refine .inl fun cell hc => ?_
    obtain ⟨row, col, -, hcol, rfl⟩ := (hcell cell).mp hc
    exact ⟨by simp only [InS]; omega, hcta row⟩
  · refine .inr fun cell hc => ?_
    obtain ⟨row, col, -, hcol, rfl⟩ := (hcell cell).mp hc
    exact ⟨by simp only [InO]; omega, hcta row⟩

/-- **The field `ScoreFacts.mma_acc`**, for cells of one pair: two MMAs writing cells of one
stage's scores, or of one stage's accumulator, of one CTA pair use the same accumulator. (Without
the pair the field is false: the MMA threads of two clusters write the same stage region of
their own pairs.) -/
theorem ScoreFacts_mma_acc' (ht : Frame.Tracked (code L) X) {i i' : EvId} {d d' st : Nat}
    {s s' : OperandSpec} {acc acc' : Bool} {mask mask' : List Nat} {cell cell' : Cell}
    (hi : X.MmaIssue i d s acc mask) (hi' : X.MmaIssue i' d' s' acc' mask') (hc : X.MmaCell i cell)
    (hc' : X.MmaCell i' cell') (hpair : leadCta cell.cta = leadCta cell'.cta)
    (hreg : (InS st cell ∧ InS st cell') ∨ (InO st cell ∧ InO st cell')) :
    SameAccumulator d s d' s' := by
  obtain ⟨g, k⟩ := i
  obtain ⟨g', k'⟩ := i'
  obtain ⟨dd, b, j, -, rfl, rfl, h1, h2, hl⟩ := mma_cell_col hpre hX ht hi hc
  obtain ⟨dd', b', j', -, rfl, rfl, h1', h2', hl'⟩ := mma_cell_col hpre hX ht hi' hc'
  have hcol : Mma.mmaCol b = Mma.mmaCol b' := by
    have := Mma.mmaStage_lt b
    have := Mma.mmaStage_lt b'
    simp only [InS, InO] at hreg
    rcases Mma.mmaCol_cases b with ⟨-, h⟩ | ⟨-, h⟩ <;>
      rcases Mma.mmaCol_cases b' with ⟨-, h'⟩ | ⟨-, h'⟩ <;> omega
  have hpl : Mma.pairLo L g = Mma.pairLo L g' := by rw [← hl, ← hl', hpair]
  have hm : ∀ (dd : Mma.D) b j, (Mma.mmaSpec L g dd b j).descriptor.m = 256 ∧
      (Mma.mmaSpec L g dd b j).descriptor.n = 128 := by
    intro dd b j; rcases Mma.mmaSpec_descOk L g dd b j with h | h <;> rw [h] <;> exact ⟨rfl, rfl⟩
  have hm' : ∀ (dd : Mma.D) b j, (Mma.mmaSpec L g' dd b j).descriptor.m = 256 ∧
      (Mma.mmaSpec L g' dd b j).descriptor.n = 128 := by
    intro dd b j; rcases Mma.mmaSpec_descOk L g' dd b j with h | h <;> rw [h] <;> exact ⟨rfl, rfl⟩
  refine ⟨hcol, by rw [(hm ..).1, (hm' ..).1], by rw [(hm ..).2, (hm' ..).2], ?_, ?_⟩
  · rw [Mma.mmaSpec_lowCta, Mma.mmaSpec_lowCta, hpl]
  · rw [Mma.mmaSpec_highCta, Mma.mmaSpec_highCta, hpl]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
