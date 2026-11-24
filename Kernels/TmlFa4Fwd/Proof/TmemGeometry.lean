-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Tmem.Alloc512
public import Core.Tc.TcDataAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd

open TcMma

/-- The warp-12 allocation takes the entire per-CTA Tensor Memory address space. -/
theorem tmem_full_allocation :
    Tmem.perform {} (.alloc 512 0) =
      .done { previousColumns := some 512, nextLifetime := 1, live := [⟨0, 0, 512⟩] } := by
  rfl

/-- The two 128-column softmax score tiles occupy the lower 256 columns. -/
def scoreColumn (stage : Fin 2) : Nat := 128 * stage.val

/-- The two 128-column PV outputs occupy the upper 256 columns. -/
def outputColumn (stage : Fin 2) : Nat := 256 + 128 * stage.val

/-- BF16 probabilities reuse the upper half of the score tile of the same stage. -/
def probabilityColumn (stage : Fin 2) : Nat := scoreColumn stage + 64

theorem scoreColumn_range (stage : Fin 2) : scoreColumn stage + 128 ≤ 256 := by
  have := stage.isLt
  unfold scoreColumn
  omega

theorem outputColumn_range (stage : Fin 2) : outputColumn stage + 128 ≤ 512 := by
  have := stage.isLt
  unfold outputColumn
  omega

theorem probabilityColumn_range (stage : Fin 2) :
    probabilityColumn stage + 64 = scoreColumn stage + 128 := by
  simp [probabilityColumn, Nat.add_assoc]

/-- Score tiles do not overlap the PV results, including when their stage numbers differ. -/
theorem score_output_apart (s t : Fin 2) :
    scoreColumn s + 128 ≤ outputColumn t := by
  have := scoreColumn_range s
  unfold outputColumn
  omega

theorem scoreColumn_distinct {s t : Fin 2} {i j : Fin 128}
    (h : scoreColumn s + i.val = scoreColumn t + j.val) : s = t ∧ i = j := by
  have := i.isLt
  have := j.isLt
  simp only [scoreColumn] at h
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/-- The fixed QK shape from the first inline assembly descriptor. -/
def qkDescriptor : Descriptor := ⟨.one, .f16 .bf16 .f32, 128, 128, false, false,
  false, false, false⟩

/-- The fixed PV shape uses the transposed shared V layout. -/
def pvDescriptor : Descriptor := ⟨.one, .f16 .bf16 .f32, 128, 128, false, false,
  false, true, false⟩

theorem qkDescriptor_decode : decode .one false .f16 0x8200490 = some qkDescriptor := by decide
theorem pvDescriptor_decode : decode .one false .f16 0x8210490 = some pvDescriptor := by decide

private theorem resultCell_cta128 {s : OperandSpec} {base row col : Nat}
    (hv : Valid s.descriptor) (hg : s.descriptor.group = .one)
    (hm : s.descriptor.m = 128) (hn : s.descriptor.n = 128)
    (hr : row < 128) (hc : col < 128) (hb : base + 128 ≤ 512) :
    resultCell s base row col = some ⟨s.lowCta, row, base + col⟩ := by
  have hbase : base < 65536 := by omega
  have hfit : base ≤ 384 := by omega
  simp [resultCell, LaneAligned, resultColumns, hv, hg, hm, hn, hr, hc,
    CtaGroup.size, hbase, hfit, Nat.mod_eq_of_lt hbase, Nat.mod_eq_of_lt hr]

/-- A QK issue writes row `row` of the stage's score tile to physical lane `row`. -/
theorem qkResultCell {s : OperandSpec} (h : s.descriptor = qkDescriptor) (stage : Fin 2)
    (row col : Fin 128) :
    resultCell s (scoreColumn stage) row.val col.val =
      some ⟨s.lowCta, row.val, scoreColumn stage + col.val⟩ := by
  refine resultCell_cta128 (h ▸ (show Valid qkDescriptor by decide)) ?_ ?_ ?_
    row.isLt col.isLt ((scoreColumn_range stage).trans (by decide))
  all_goals simp [h, qkDescriptor]

/-- A PV issue writes row `row` of the stage's output tile to physical lane `row`. -/
theorem pvResultCell {s : OperandSpec} (h : s.descriptor = pvDescriptor) (stage : Fin 2)
    (row col : Fin 128) :
    resultCell s (outputColumn stage) row.val col.val =
      some ⟨s.lowCta, row.val, outputColumn stage + col.val⟩ := by
  refine resultCell_cta128 (h ▸ (show Valid pvDescriptor by decide)) ?_ ?_ ?_
    row.isLt col.isLt (outputColumn_range stage)
  all_goals simp [h, pvDescriptor]

/-- The unmasked single-CTA MMA writes every cell named by its result layout. -/
theorem writeCell_no_mask_128 {s : OperandSpec} {base row col : Nat} {cell : Cell}
    (hg : s.descriptor.group = .one) (hm : s.descriptor.m = 128)
    (hr : row < 128) (hl : cell.lane < 128)
    (hcell : resultCell s base row col = some cell) :
    writeCell s base (List.replicate 4 0) row col = some cell := by
  have hindex : cell.lane / 32 < 4 := by omega
  have hmzero : OutputMaskValid .one (List.replicate 4 0) := by decide
  have hword : (List.replicate 4 0)[cell.lane / 32]? = some 0 := by
    simp only [List.getElem?_replicate, ite_eq_left hindex]
  simp only [writeCell, hg, hm, CtaGroup.size, Nat.div_one, Nat.div_eq_of_lt hr,
    Nat.zero_mul, Nat.zero_add, hcell, hmzero, not_true_eq_false, ↓reduceIte,
    bind, Option.bind, hword, Nat.zero_div, Nat.zero_mod]

/-- Each PV instruction reads eight 32-bit columns of its row's packed probabilities. -/
theorem pvACell {s : OperandSpec} (hd : s.descriptor = pvDescriptor) (stage : Fin 2)
    (step : Fin 8) (row : Fin 128) (byte : Fin 32)
    (h : s.aTmem = some (probabilityColumn stage + 8 * step.val)) :
    aCell s (32 * row.val + byte.val) =
      some (⟨s.lowCta, row.val, probabilityColumn stage + 8 * step.val + byte.val / 4⟩,
        byte.val % 4) := by
  have hv : Valid pvDescriptor := by decide
  have hrow : (32 * row.val + byte.val) / 32 = row.val := by
    have := byte.isLt
    omega
  have hbyte : (32 * row.val + byte.val) % 32 = byte.val := by
    have := byte.isLt
    omega
  have hbase := scoreColumn_range stage
  have hstep := step.isLt
  have hcol : probabilityColumn stage + 8 * step.val < 65536 := by
    unfold probabilityColumn
    omega
  have hfit : probabilityColumn stage + 8 * step.val ≤ 504 := by
    unfold probabilityColumn
    omega
  unfold pvDescriptor at hv
  simp [aCell, h, hd, hv, pvDescriptor, Operand.rows, Operand.extent, Kind.k, Kind.width,
    CtaGroup.size, halfDatapath, hcol, Nat.mod_eq_of_lt hcol, hrow, hbyte, hfit,
    row.isLt, Nat.mod_eq_of_lt row.isLt]

/-- A softmax x16 store supplies two neighboring PV A fragments. -/
theorem pvASegment (stage : Fin 2) (step : Fin 8) (byte : Fin 32) :
    probabilityColumn stage + 8 * step.val + byte.val / 4 =
      probabilityColumn stage + 16 * (step.val / 2) + (8 * (step.val % 2) + byte.val / 4) ∧
    8 * (step.val % 2) + byte.val / 4 < 16 := by
  have := byte.isLt
  omega

/-- The softmax lane-field mask selects the four aligned 32-lane TMEM blocks. -/
theorem tmem_lane_field_mask (L : Launch) (g : Nat) :
    ((g % L.block) <<< 16) &&& 6291456 = 65536 * laneBase L g := by
  let tid := g % L.block
  have hmask : (tid &&& 96) / 32 = tid / 32 % 4 := by
    rw [show 32 = 2 ^ 5 by decide, Nat.and_div_two_pow]
    rw [show (96 : Nat) / 2 ^ 5 = 2 ^ 2 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  have hmasklo : (tid &&& 96) % 32 = 0 := by
    rw [show 32 = 2 ^ 5 by decide, Nat.and_mod_two_pow]
    simp
  have hhigh : ((tid <<< 16) &&& 6291456) / 65536 = tid &&& 96 := by
    rw [show 65536 = 2 ^ 16 by decide, Nat.and_div_two_pow, Nat.shiftLeft_eq]
    simp
  have hlow : ((tid <<< 16) &&& 6291456) % 65536 = 0 := by
    rw [show 65536 = 2 ^ 16 by decide, Nat.and_mod_two_pow]
    simp
  change ((tid <<< 16) &&& 6291456) = 65536 * (tid / 32 % 4 * 32)
  omega

/-- The warp's lane field and the allocated column combine by bitwise OR in the PTX. -/
theorem tmem_lane_or_column {lane col : Nat} (hcol : col < 512) :
    (lane <<< 16) ||| col = 2 ^ 16 * lane + col := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : col < 2 ^ 16)]
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

theorem tmem_warp_encoding_lt (L : Launch) (g : Nat) {col : Nat} (hc : col < 512) :
    2 ^ 16 * laneBase L g + col < 2 ^ 32 := by
  have h := Nat.mod_lt (g % L.block / 32) (show 0 < 4 by decide)
  unfold laneBase
  omega

theorem tmem_thread_lane_lt (L : Launch) (g : Nat) : laneBase L g + laneOf L g < 128 := by
  have hl := Nat.mod_lt (g % L.block) (show 0 < 32 by decide)
  have hw := Nat.mod_lt (g % L.block / 32) (show 0 < 4 by decide)
  unfold laneBase laneOf
  omega

/-- The absolute lane field encoded in a 32x32b address permits the warp's full lane group. -/
theorem tcDataAddressOk_warp32 (L : Launch) (g : Nat) {col : Nat} (hc : col < 512) :
    tcDataAddressOk L g .s32x32b (2 ^ 16 * laneBase L g + col) = true := by
  have hfield : (65536 * laneBase L g + col) / 65536 = laneBase L g := by omega
  simp [tcDataAddressOk, TcShape.splitOk, TcShape.lanes, hfield, tmemLaneFieldOk]

/-- A 32x32b transfer names the lane of its issuing thread and consecutive columns. -/
theorem tcDataCell_warp32 (L : Launch) (g j : Nat) {col : Nat} (hc : col < 512) :
    tcDataCell L g .s32x32b (2 ^ 16 * laneBase L g + col) j =
      ⟨g / L.block, laneBase L g + laneOf L g, col + j⟩ := by
  have hcol : col < 65536 := by omega
  simp [tcDataCell, TcShape.base, TcShape.lanes, TcShape.laneIn, TcShape.columnIn,
    chunkOffset, hcol]

end PTX.Kernels.TmlFa4Fwd
