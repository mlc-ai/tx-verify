-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Geometry.Maps
import Lemmas.Flow.TcTmpl
import Lemmas.Flow.TensorLoadFacts
import Lemmas.Flow.TensorIssue
import Lemmas.Tensor.TensorSwizzle

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaDataTrace
open PTX PTX.Flow PTX.Proof Wg1Mma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option maxRecDepth 100000

abbrev keyWord (L : Launch) (i : Nat) (k : Fin 16) : Nat :=
  descLo (kvBase L i) + qkBDelta k.val + 4611756662049538048

abbrev valueWord (L : Launch) (i : Nat) (k : Fin 8) : Nat :=
  descLo (kvBase L i) + pvBDelta k.val + 4611756662083026944

abbrev probabilityWord (L : Launch) (k : Fin 8) : Nat :=
  descLo (L.sharedBase + 204800) + 128 * (k.val / 2) + 70403108110336

/-- The K-major descriptor of the selected contraction chunk, in bytes. -/
def keyDescriptor (L : Launch) (i : Nat) (k : Fin 16) : TcShared.Descriptor :=
  ⟨kvBase L i + 16 * qkBDelta k.val, 16, 1024, 0, false, false, .b128⟩

/-- The MN-major descriptor selects the corresponding value chunk and output half. -/
def valueDescriptor (L : Launch) (i : Nat) (k : Fin 8) : TcShared.Descriptor :=
  ⟨kvBase L i + 16 * pvBDelta k.val, 8192, 1024, 0, false, false, .b128⟩

/-- The unswizzled P operand descriptor for the selected 16 slots. -/
def probabilityDescriptor (L : Launch) (k : Fin 8) : TcShared.Descriptor :=
  ⟨L.sharedBase + 204800 + 2048 * (k.val / 2), 1024, 128, 0, false, false, .none⟩

private theorem decode_start_add {n x : Nat} {d : TcShared.Descriptor}
    (hn : n < 2 ^ 15) (hx : x % 2 ^ 15 = 0) (hb : x + 2 ^ 15 ≤ 2 ^ 64)
    (hd : TcShared.decode x = some d) :
    TcShared.decode (n + x) = some { d with start := 16 * n } := by
  have hlo : (n + x) % 2 ^ 15 = n := by omega
  have hbase : (n + x) / 2 ^ 15 = x / 2 ^ 15 := by omega
  have hfld (s : Nat) (hs : 15 ≤ s) : (n + x) / 2 ^ s = x / 2 ^ s := by
    have he : 2 ^ s = 2 ^ 15 * 2 ^ (s - 15) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hs]
    rw [he, ← Nat.div_div_eq_div_mul, hbase, Nat.div_div_eq_div_mul]
  have hn64 : n + x < 2 ^ 64 := by omega
  have hx64 : x < 2 ^ 64 := by omega
  have he : TcShared.decode (n + x) =
      (TcShared.decode x).map (fun d => { d with start := 16 * n }) := by
    unfold TcShared.decode
    simp only [hfld 61 (by decide), hfld 15 (by decide), hfld 31 (by decide),
      hfld 46 (by decide), hfld 54 (by decide), hfld 16 (by decide), hfld 32 (by decide),
      hfld 49 (by decide), hfld 52 (by decide), hfld 53 (by decide),
      hlo, hn64, hx64, true_and]
    split
    · rfl
    · split <;> simp [Nat.mul_comm n 16]
  rw [he, hd]
  rfl

private theorem decode_key_start {n : Nat} (hn : n < 2 ^ 15) :
    TcShared.decode (n + 4611756662049538048) =
      some ⟨16 * n, 16, 1024, 0, false, false, .b128⟩ := by
  exact decode_start_add (x := 4611756662049538048) (d := ⟨0, 16, 1024, 0, false, false, .b128⟩)
    hn (by decide) (by decide) (by decide)

private theorem decode_value_start {n : Nat} (hn : n < 2 ^ 15) :
    TcShared.decode (n + 4611756662083026944) =
      some ⟨16 * n, 8192, 1024, 0, false, false, .b128⟩ := by
  exact decode_start_add (x := 4611756662083026944) (d := ⟨0, 8192, 1024, 0, false, false, .b128⟩)
    hn (by decide) (by decide) (by decide)

private theorem decode_probability_start {n : Nat} (hn : n < 2 ^ 15) :
    TcShared.decode (n + 70403108110336) =
      some ⟨16 * n, 1024, 128, 0, false, false, .none⟩ := by
  exact decode_start_add (x := 70403108110336) (d := ⟨0, 1024, 128, 0, false, false, .none⟩)
    hn (by decide) (by decide) (by decide)

private theorem mma_base {c : Nat} (hc : c < 2 ^ 18)
    (hal : c % 16 = 0) : 16 * descLo c = c := by
  unfold descLo
  have hsmall : c / 16 < 2 ^ 14 := by omega
  rw [Nat.mod_eq_of_lt hsmall]
  omega

private theorem hShared (hpre : Pre P L mem0) : L.sharedBase + 222952 < 2 ^ 18 := by
  have h := hpre.sharedRange
  rw [hpre.sharedBase]
  change P.sharedBase + 223232 ≤ 2 ^ 18 at h
  omega

private theorem hShared16 (hpre : Pre P L mem0) : L.sharedBase % 16 = 0 := by
  have h := hpre.sharedAlignment
  rw [hpre.sharedBase]
  omega

theorem decode_keyDescriptor (hpre : Pre P L mem0) (i : Nat) (k : Fin 16) :
    TcShared.decode (keyWord L i k) = some (keyDescriptor L i k) := by
  have hx := hShared hpre
  have ha := hShared16 hpre
  have hp : 16 * descLo (kvBase L i) = kvBase L i :=
    mma_base (by unfold kvBase; omega) (by unfold kvBase; omega)
  have hk : qkBDelta k.val < 4096 := by unfold qkBDelta; omega
  have hlo : descLo (kvBase L i) < 2 ^ 14 := Nat.mod_lt _ (by decide)
  rw [decode_key_start (by omega)]
  unfold keyDescriptor
  congr 2
  omega

theorem decode_valueDescriptor (hpre : Pre P L mem0) (i : Nat) (k : Fin 8) :
    TcShared.decode (valueWord L i k) = some (valueDescriptor L i k) := by
  have hx := hShared hpre
  have ha := hShared16 hpre
  have hp : 16 * descLo (kvBase L i) = kvBase L i :=
    mma_base (by unfold kvBase; omega) (by unfold kvBase; omega)
  have hk : pvBDelta k.val < 4096 := by unfold pvBDelta; omega
  have hlo : descLo (kvBase L i) < 2 ^ 14 := Nat.mod_lt _ (by decide)
  rw [decode_value_start (by omega)]
  unfold valueDescriptor
  congr 2
  omega

theorem decode_probabilityDescriptor (hpre : Pre P L mem0) (k : Fin 8) :
    TcShared.decode (probabilityWord L k) = some (probabilityDescriptor L k) := by
  have hx := hShared hpre
  have ha := hShared16 hpre
  have hp : 16 * descLo (L.sharedBase + 204800) = L.sharedBase + 204800 :=
    mma_base (by omega) (by omega)
  rw [decode_probability_start (by omega)]
  unfold probabilityDescriptor
  congr 2
  omega

/-- Both parts of the QK operand spec use the issuer's CTA, with A in Q's TMEM columns. -/
def qkOperands (L : Launch) (g i : Nat) (k : Fin 16) : TcMma.OperandSpec :=
  ⟨qkDescriptor, keyDescriptor L i k, keyDescriptor L i k, ctaOf L g, ctaOf L g,
    some (qkACol k), {}⟩

/-- Both P and V are shared operands for PV, in the issuer's CTA. -/
def pvOperands (L : Launch) (g i : Nat) (k : Fin 8) : TcMma.OperandSpec :=
  ⟨pvDescriptor, probabilityDescriptor L k, valueDescriptor L i k,
    ctaOf L g, ctaOf L g, none, {}⟩

/-- The first QK chunk overwrites the previous contents of the QK destination. -/
def qkAccum (k : Fin 16) : Bool := k.val != 0

/-- Each PV destination starts fresh in block zero and otherwise accumulates its old value. -/
def pvAccum (i : Nat) (k : Fin 8) : Bool := i != 0 || decide (2 ≤ k.val)
private theorem qk_valid : TcMma.Valid qkDescriptor := qkIdesc_valid
private theorem pv_valid : TcMma.Valid pvDescriptor := pvIdesc_valid

/-- QK contraction depth in the original 512-element query/key row. -/
def qkFeature (issue : Fin 16) (col : Fin 128) (k : Fin 16) : Nat :=
  128 * (issue.val / 4) + 64 * (col.val / 64) + 16 * (issue.val % 4) + k.val

/-- The probability and value tiles share this token coordinate for a PV contraction. -/
def pvSlot (issue : Fin 8) (k : Fin 16) : Nat := 16 * (issue.val / 2) + k.val

/-- The 256 columns of each PV issue belong to its output half. -/
def pvFeature (issue : Fin 8) (col : Fin 256) : Nat := 256 * (issue.val % 2) + col.val

/-- The address of a logical element of the SW128 BF16 tile before applying the swizzle. -/
def kvLinearByte (L : Launch) (i slot feature byte : Nat) : Nat :=
  kvBase L i + 128 * slot + 8192 * (feature / 64) + 2 * (feature % 64) + byte

/-- A key operand byte addresses the KV token and feature selected by the QK issue. -/
theorem qkKeyByte (L : Launch) (g i : Nat) (issue : Fin 16) (col : Fin 128)
    (k : Fin 16) (b : Fin 2) :
    (qkOperands L g i issue).byteLoc .b (2 * (col.val * 16 + k.val) + b.val) =
      some ⟨.shared, ctaOf L g, TcShared.Swizzle.offset .b128
        (kvLinearByte L i (col.val % 64) (qkFeature issue col k) b.val)⟩ := by
  let n := 2 * (col.val * 16 + k.val) + b.val
  have hrow : n / 32 = col.val := by dsimp [n]; omega
  have hk : n / 2 % 16 = k.val := by dsimp [n]; omega
  have hb : n % 2 = b.val := by dsimp [n]; omega
  have hcol : col.val < 128 := col.isLt
  have hb' : b.val < 2 := b.isLt
  have hv := qk_valid
  simp only [qkDescriptor] at hv
  change (qkOperands L g i issue).byteLoc .b n = _
  simp [TcMma.OperandSpec.byteLoc, qkOperands, TcMma.Kind.width, TcMma.Kind.k,
    TcMma.Operand.extent, TcMma.Operand.major, qkDescriptor, hv, hrow, hk, hb,
    hcol, hb', CtaGroup.size, keyDescriptor, TcShared.byteAddress, TcShared.linear,
    TcShared.Swizzle.sectors, kvLinearByte, qkFeature, qkBDelta]
  congr 2
  omega

/-- A value operand byte addresses the same logical KV tile as dequantization, with the
PV issue selecting the token slice and which 256 output features it updates. -/
theorem pvValueByte (L : Launch) (g i : Nat) (issue : Fin 8) (col : Fin 256)
    (k : Fin 16) (b : Fin 2) :
    (pvOperands L g i issue).byteLoc .b (2 * (col.val * 16 + k.val) + b.val) =
      some ⟨.shared, ctaOf L g, TcShared.Swizzle.offset .b128
        (kvLinearByte L i (pvSlot issue k) (pvFeature issue col) b.val)⟩ := by
  let n := 2 * (col.val * 16 + k.val) + b.val
  have hrow : n / 32 = col.val := by dsimp [n]; omega
  have hk : n / 2 % 16 = k.val := by dsimp [n]; omega
  have hb : n % 2 = b.val := by dsimp [n]; omega
  have hcol : col.val < 256 := col.isLt
  have hb' : b.val < 2 := b.isLt
  have hv := pv_valid
  simp only [pvDescriptor] at hv
  change (pvOperands L g i issue).byteLoc .b n = _
  simp [TcMma.OperandSpec.byteLoc, pvOperands, TcMma.Kind.width, TcMma.Kind.k,
    TcMma.Operand.extent, TcMma.Operand.major, pvDescriptor, hv, hrow, hk, hb,
    hcol, hb', CtaGroup.size, valueDescriptor, TcShared.byteAddress, TcShared.linear,
    TcShared.Swizzle.sectors, kvLinearByte, pvFeature, pvSlot, pvBDelta]
  congr 2
  omega

/-- The PV issue covering row group `r` and feature step `s` of a dequantization tile. -/
def pvDequantIssue (r : Fin 4) (s : Fin 8) : Fin 8 :=
  ⟨2 * r.val + s.val / 4, by
    have hr := r.isLt
    have hs := s.isLt
    omega⟩

/-- The B-operand index of a byte written by a dequantization lane in feature step `s`. -/
def pvDequantIndex (lane : Fin 128) (s : Fin 8) (b : Fin 16) : Nat :=
  let col := 64 * (s.val % 4) + 8 * (lane.val % 8) + b.val / 2
  2 * (col * 16 + lane.val / 8) + b.val % 2

theorem pvDequantIndex_lt (lane : Fin 128) (s : Fin 8) (b : Fin 16) :
    pvDequantIndex lane s b < TcMma.Operand.b.bytes pvDescriptor := by
  have hl := lane.isLt
  have hb := b.isLt
  change pvDequantIndex lane s b < 8192
  dsimp only [pvDequantIndex]
  omega

/-- The SW128 byte offset within the dequantization tile. -/
def pvDequantByteOffset (lane : Fin 128) (r : Fin 4) (s : Fin 8) (b : Fin 16) : Nat :=
  8192 * s.val + 128 * (16 * r.val + lane.val / 8) +
    16 * ((lane.val % 8) ^^^ (lane.val / 8 % 8)) + b.val

/-- The indexed PV B byte addresses exactly the corresponding byte of the dequantized tile. -/
theorem pvDequantByteLoc (hpre : Pre P L mem0) (block : Nat)
    (lane : Fin 128) (r : Fin 4) (s : Fin 8) (b : Fin 16) :
    (pvOperands L g block (pvDequantIssue r s)).byteLoc .b (pvDequantIndex lane s b) =
      some ⟨.shared, ctaOf L g, kvBase L block + pvDequantByteOffset lane r s b⟩ := by
  have hl := lane.isLt
  have hb := b.isLt
  let col : Fin 256 := ⟨64 * (s.val % 4) + 8 * (lane.val % 8) + b.val / 2, by omega⟩
  let depth : Fin 16 := ⟨lane.val / 8, by omega⟩
  let sub : Fin 2 := ⟨b.val % 2, by omega⟩
  let base := kvBase L block + 8192 * s.val
  let row := 16 * r.val + lane.val / 8
  let chunk := lane.val % 8
  let addr := base + 128 * row + 16 * chunk + b.val
  have h := pvValueByte L g block (pvDequantIssue r s) col depth sub
  have hlin :
      kvLinearByte L block (pvSlot (pvDequantIssue r s) depth)
        (pvFeature (pvDequantIssue r s) col) sub.val = addr := by
    simp only [kvLinearByte, pvSlot, pvFeature, pvDequantIssue, col, depth, sub,
      addr, base, row, chunk]
    omega
  change (pvOperands L g block (pvDequantIssue r s)).byteLoc .b
    (pvDequantIndex lane s b) = _ at h
  rw [hlin] at h
  have halign : base % 1024 = 0 := by
    have hbase : L.sharedBase % 1024 = 0 := hpre.sharedBase ▸ hpre.sharedAlignment
    simp only [base, kvBase]
    omega
  have hrow : addr / 128 % 8 = lane.val / 8 % 8 := by dsimp [addr, row, chunk]; omega
  have hchunk : addr / 16 % 8 = chunk := by dsimp [addr, chunk]; omega
  have hbyte : addr % 16 = b.val := by dsimp [addr, chunk]; omega
  have hprefix : 128 * (addr / 128) = base + 128 * row := by dsimp [addr, chunk]; omega
  have hswizzle : TcShared.Swizzle.offset .b128 addr =
      kvBase L block + pvDequantByteOffset lane r s b := by
    simp [TcShared.Swizzle.offset, TensorSwizzle.offset, TensorSwizzle.chunk,
      TensorSwizzle.mask, TensorSwizzle.sectors, hrow, hchunk, hbyte, hprefix, base, row, chunk,
      pvDequantByteOffset, Nat.add_assoc]
  rwa [hswizzle] at h

/-- An un-swizzled shared P word is indexed by logical head and token. Both datapath
lanes that represent a given head read that head's single packet. -/
def pLinearByte (L : Launch) (head slot byte : Nat) : Nat :=
  L.sharedBase + 204800 + 16 * head + 1024 * (slot / 8) + 2 * (slot % 8) + byte

theorem pvProbabilityByte (L : Launch) (g i : Nat) (issue : Fin 8) (row : Fin 128)
    (k : Fin 16) (b : Fin 2) :
    (pvOperands L g i issue).byteLoc .a (2 * (row.val * 16 + k.val) + b.val) =
      some ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) (pvSlot issue k) b.val⟩ := by
  let n := 2 * (row.val * 16 + k.val) + b.val
  have hrow : n / 32 = row.val := by dsimp [n]; omega
  have hk : n / 2 % 16 = k.val := by dsimp [n]; omega
  have hb : n % 2 = b.val := by dsimp [n]; omega
  have hr : row.val < 128 := row.isLt
  have hb' : b.val < 2 := b.isLt
  have hv := pv_valid
  simp only [pvDescriptor] at hv
  change (pvOperands L g i issue).byteLoc .a n = _
  simp [TcMma.OperandSpec.byteLoc, pvOperands, TcMma.Kind.width, TcMma.Kind.k,
    TcMma.Operand.extent, TcMma.Operand.major, pvDescriptor, hv, hrow, hk, hb,
    hr, hb', CtaGroup.size, probabilityDescriptor, TcShared.byteAddress, TcShared.linear,
    TcShared.Swizzle.sectors, TcShared.Swizzle.offset, TensorSwizzle.offset_none,
    pLinearByte, pvSlot]
  omega

/-- QK's query A byte comes from the named query-copy lane and the contraction word within it. -/
theorem qkQueryByte (L : Launch) (g i : Nat) (issue : Fin 16) (row : Fin 128)
    (k : Fin 16) (b : Fin 2) :
    TcMma.aCell (qkOperands L g i issue) (2 * (row.val * 16 + k.val) + b.val) =
      some (⟨ctaOf L g, row.val, qkACol issue + k.val / 2⟩, 2 * (k.val % 2) + b.val) := by
  let n := 2 * (row.val * 16 + k.val) + b.val
  have hrow : n / 32 = row.val := by dsimp [n]; omega
  have hword : n % 32 / 4 = k.val / 2 := by dsimp [n]; omega
  have hbyte : n % 32 % 4 = 2 * (k.val % 2) + b.val := by dsimp [n]; omega
  have hr : row.val < 128 := row.isLt
  have hs : qkACol issue < 65536 := by dsimp [qkACol, tmemQ]; omega
  have hc : qkACol issue + 8 ≤ 512 := by dsimp [qkACol, tmemQ]; omega
  change TcMma.aCell (qkOperands L g i issue) n = _
  simp [TcMma.aCell, qkOperands, qkDescriptor, TcMma.Operand.rows,
    TcMma.Kind.width, TcMma.Kind.k, TcMma.halfDatapath, CtaGroup.size,
    hrow, hword, hbyte, hr, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs]
  exact ⟨qk_valid, by omega, hs⟩

/-- The QK tile has one TMEM cell per head, token, and datapath half. -/
theorem qkResultCell (L : Launch) (g i : Nat) (issue : Fin 16) (row : Fin 64) (col : Fin 128) :
    TcMma.resultCell (qkOperands L g i issue) tmemP row.val col.val =
      some ⟨ctaOf L g, row.val + 64 * (col.val / 64), tmemP + col.val % 64⟩ := by
  simp [TcMma.resultCell, qkOperands, qkDescriptor, CtaGroup.size, tmemP,
    TcMma.resultColumns, TcMma.LaneAligned, TcMma.halfDatapath, TcMma.columnBlocks,
    row.isLt, col.isLt, Nat.mod_eq_of_lt row.isLt]
  exact qk_valid

/-- The PV tile uses the alternating O destinations and two lanes per head. -/
theorem pvResultCell (L : Launch) (g i : Nat) (issue : Fin 8) (row : Fin 64) (col : Fin 256) :
    TcMma.resultCell (pvOperands L g i issue) (pvDest issue) row.val col.val =
      some ⟨ctaOf L g, row.val + 64 * (col.val / 128), pvDest issue + col.val % 128⟩ := by
  have hs : pvDest issue < 65536 := by dsimp [pvDest, tmemO]; omega
  have hc : pvDest issue + 128 ≤ 512 := by dsimp [pvDest, tmemO]; omega
  simp [TcMma.resultCell, pvOperands, pvDescriptor, CtaGroup.size,
    TcMma.resultColumns, TcMma.LaneAligned, TcMma.halfDatapath, TcMma.columnBlocks,
    row.isLt, col.isLt, Nat.mod_eq_of_lt row.isLt, Nat.mod_eq_of_lt hs, Nat.div_eq_of_lt hs, hc]
  exact pv_valid

private def qkAReg (k : Fin 16) : Nat :=
  if k.val = 0 then 858 else if k.val = 1 then 861 else 861 + k.val

private def pvDReg (k : Fin 8) : Nat := if k.val % 2 = 0 then 860 else 882

private def mmaZeroMask : List Opnd := [.imm 0, .imm 0, .imm 0, .imm 0]

private def qkInstr (k : Fin 16) : TcMmaInstr :=
  { TcMmaInstr.dense .one true .f16 857 (.tmem (qkAReg k) 0) (.reg (3077 + k.val))
      (.reg 859) mmaZeroMask (.reg (4091 + k.val)) with zeroColumnMask := some (.imm 0) }

private def pvInstr (k : Fin 8) : TcMmaInstr :=
  { TcMmaInstr.dense .one true .f16 (pvDReg k) (.smem (.reg (3093 + 3 * (k.val / 2))))
      (.reg (3094 + 3 * (k.val / 2) + k.val % 2)) (.reg 880) mmaZeroMask (.reg (4108 + k.val))
      with zeroColumnMask := some (.imm 0) }

private theorem qkInstr_code (k : Fin 16) :
    kernel.code[(Site.qkMma k).pc]? = some ⟨none, .tcMma (qkInstr k)⟩ := by
  fin_cases k
  · exact Flow.code_mma_0
  · exact Flow.code_mma_1
  · exact Flow.code_mma_2
  · exact Flow.code_mma_3
  · exact Flow.code_mma_4
  · exact Flow.code_mma_5
  · exact Flow.code_mma_6
  · exact Flow.code_mma_7
  · exact Flow.code_mma_8
  · exact Flow.code_mma_9
  · exact Flow.code_mma_10
  · exact Flow.code_mma_11
  · exact Flow.code_mma_12
  · exact Flow.code_mma_13
  · exact Flow.code_mma_14
  · exact Flow.code_mma_15

private theorem pvInstr_code (k : Fin 8) :
    kernel.code[(Site.pvMma k).pc]? = some ⟨none, .tcMma (pvInstr k)⟩ := by
  fin_cases k
  · exact Flow.code_mma_16
  · exact Flow.code_mma_17
  · exact Flow.code_mma_18
  · exact Flow.code_mma_19
  · exact Flow.code_mma_20
  · exact Flow.code_mma_21
  · exact Flow.code_mma_22
  · exact Flow.code_mma_23

private theorem mma_reg {site : Wg1Mma.Site} {i : Nat} {t : TState} {r : Nat}
    (h : (Wg1Mma.code P L g).AtD ⟨site, i⟩ t) (hr : r ∈ Flow.live site.pc) :
    t.regs r = some (Wg1Mma.valueOf P L g ⟨site, i⟩ r) :=
  holds_mem h.2.2.2.2 (mem_factsFrom hr)

private theorem qk_regs (i : Nat) (k : Fin 16) {t : TState}
    (h : (Wg1Mma.code P L g).AtD ⟨.qkMma k, i⟩ t) :
    t.regs 857 = some (b32 tmemP) ∧ t.regs (qkAReg k) = some (b32 (qkACol k)) ∧
    t.regs (3077 + k.val) = some (b64 (keyWord L i k)) ∧
    t.regs 859 = some (b32 qkIdesc) ∧ t.regs (4091 + k.val) = some (.pred (qkAccum k)) := by
  refine ⟨mma_reg h (by fin_cases k <;> decide +kernel),
    ?_, ?_, mma_reg h (by fin_cases k <;> decide +kernel), ?_⟩
  · fin_cases k <;> exact mma_reg h (by decide +kernel)
  · fin_cases k <;> exact mma_reg h (by decide +kernel)
  · fin_cases k <;> exact mma_reg h (by decide +kernel)

private theorem pv_regs (i : Nat) (k : Fin 8) {t : TState}
    (h : (Wg1Mma.code P L g).AtD ⟨.pvMma k, i⟩ t) :
    t.regs (pvDReg k) = some (b32 (pvDest k)) ∧
    t.regs (3093 + 3 * (k.val / 2)) = some (b64 (probabilityWord L k)) ∧
    t.regs (3094 + 3 * (k.val / 2) + k.val % 2) = some (b64 (valueWord L i k)) ∧
    t.regs 880 = some (b32 pvIdesc) ∧ t.regs (4108 + k.val) = some (.pred (pvAccum i k)) := by
  refine ⟨?_, ?_, ?_, mma_reg h (by fin_cases k <;> decide +kernel), ?_⟩
  · fin_cases k <;> exact mma_reg h (by decide +kernel)
  · fin_cases k <;> exact mma_reg h (by decide +kernel)
  · fin_cases k <;> exact mma_reg h (by decide +kernel)
  · fin_cases k <;> simp [pvAccum] <;> exact mma_reg h (by decide +kernel)

private theorem mma_ctaGroup {c : Nat} (hpre : Pre P L mem0) (hc : c < L.grid) :
    L.ctaGroup c .one = some [c] := by
  have hsz (k : Nat) : L.clusterSizeAt k = 1 := by
    simp [Launch.clusterSizeAt, hpre.clusterPlaces, gridPlace, Dim3.prod]
  have hloc (n k x : Nat) : L.locate n k x = (k + x, 0) := by
    rw [Launch.locate_regular (fun k => by
      change L.clusterSizeAt k = L.clusterSize.val
      rw [hsz, hpre.clusterSize]), hpre.clusterSize, Nat.div_one, Nat.mod_one]
  have hstart (k : Nat) : L.clusterStart k = k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Launch.clusterStart, ih, hsz]
  rw [Launch.ctaGroup_one]
  simp [Launch.peerCta, Launch.rankOfCta, Launch.clusterOfCta, Launch.clusterSizeOf, hloc,
    hstart, hsz, hc]

/-- Each launched issuer has exactly its local CTA in the kernel's CTA group one. -/
theorem mma_group_thread (hpre : Pre P L mem0) (h : g < L.threads) :
    L.ctaGroup (g / L.block) .one = some [g / L.block] := by
  apply mma_ctaGroup hpre
  unfold Launch.threads at h
  rw [hpre.block] at h ⊢
  omega

private theorem qkWord_lt (L : Launch) (i : Nat) (k : Fin 16) : keyWord L i k < 2 ^ 64 := by
  dsimp [keyWord, descLo, qkBDelta]
  omega

private theorem pvWord_lt (L : Launch) (i : Nat) (k : Fin 8) : valueWord L i k < 2 ^ 64 := by
  dsimp [valueWord, descLo, pvBDelta]
  omega

private theorem pWord_lt (L : Launch) (k : Fin 8) : probabilityWord L k < 2 ^ 64 := by
  dsimp [probabilityWord, descLo]
  omega

private theorem mmaMask (L : Launch) (g : Nat) (t : TState) :
    mmaZeroMask.mapM (readBits L g t 32) =
      .ok ([0, 0, 0, 0] : List (BitVec 64)) := rfl

section
variable {t : TState}

private theorem mmaTmem_formula {d a b id en : Nat} {dd aa bb ii : BitVec 64} {q : Nat}
    {db : TcShared.Descriptor} {md : TcMma.Descriptor} {s : TcMma.OperandSpec} {acc : Bool}
    (hg : g < L.threads) (hd : readBits L g t 32 (.reg d) = .ok dd)
    (ha : readBits L g t 32 (.reg a) = .ok aa) (hb : readBits L g t 64 (.reg b) = .ok bb)
    (hi : readBits L g t 32 (.reg id) = .ok ii) (hq : tmemOffset aa.toNat 0 = .ok q)
    (hen : mmaEnable t (.reg en) = .ok acc) (hdb : TcShared.decode bb.toNat = some db)
    (hmd : TcMma.decode .one true .f16 ii.toNat = some md) (hA : md.transposeA = false)
    (hs : TcMma.makeOperands L (g / L.block) md db db = some s) :
    mmaTmemTmpl L g t .one true .f16 d a 0 (.reg b) (.reg id) mmaZeroMask (.reg en)
      (some (.imm 0)) {} =
      .tc (.mma dd.toNat { s with aTmem := some q, collector := {} } acc [0, 0, 0, 0])
        (PTX.next t) := by
  simp only [mmaTmemTmpl, hg, ↓reduceIte, hd, ha, hb, hi, mmaMask, bind, Except.bind, hq, hen,
    show mmaZeroMask.length = 4 * CtaGroup.one.size by rfl,
    zeroColumnMaskOk, show readBits L g t 64 (.imm 0) = .ok 0 by rfl,
    show zeroColumnMaskNone (0 : BitVec 64).toNat = true by rfl,
    hdb, hmd, hA, Bool.false_eq_true, hs, pure, Except.pure, ofExec]
  rfl

private theorem mmaSmem_formula {d a b id en : Nat} {dd aa bb ii : BitVec 64}
    {da db : TcShared.Descriptor} {md : TcMma.Descriptor} {s : TcMma.OperandSpec} {acc : Bool}
    (hg : g < L.threads) (hd : readBits L g t 32 (.reg d) = .ok dd)
    (ha : readBits L g t 64 (.reg a) = .ok aa) (hb : readBits L g t 64 (.reg b) = .ok bb)
    (hi : readBits L g t 32 (.reg id) = .ok ii) (hen : mmaEnable t (.reg en) = .ok acc)
    (hda : TcShared.decode aa.toNat = some da) (hdb : TcShared.decode bb.toNat = some db)
    (hmd : TcMma.decode .one true .f16 ii.toNat = some md)
    (hs : TcMma.makeOperands L (g / L.block) md da db = some s) :
    mmaSmemTmpl L g t .one true .f16 d (.reg a) (.reg b) (.reg id) mmaZeroMask (.reg en)
      (some (.imm 0)) {} =
      .tc (.mma dd.toNat { s with collector := {} } acc [0, 0, 0, 0]) (PTX.next t) := by
  simp only [mmaSmemTmpl, hg, ↓reduceIte, hd, ha, hb, hi, mmaMask, bind, Except.bind, hen,
    show mmaZeroMask.length = 4 * CtaGroup.one.size by rfl,
    zeroColumnMaskOk, show readBits L g t 64 (.imm 0) = .ok 0 by rfl,
    show zeroColumnMaskNone (0 : BitVec 64).toNat = true by rfl,
    hda, hdb, hmd, hs, pure, Except.pure, ofExec]
  rfl

/-- The sixteen emitted QK issues write P, read the exact Q/K operands and clear only on chunk 0. -/
theorem qkMma_template (hpre : Pre P L mem0) (hg : g < L.threads) (i : Nat) (k : Fin 16)
    {t : TState} {ins : Instr} (ha : (Wg1Mma.code P L g).AtD ⟨.qkMma k, i⟩ t)
    (hc : kernel.code[(Site.qkMma k).pc]? = some ins) :
    eventTmpl asms L g t ins.op = .tc (.mma tmemP (qkOperands L g i k) (qkAccum k) [0, 0, 0, 0])
        (PTX.next t) := by
  obtain rfl := Option.some.inj (hc.symm.trans (qkInstr_code k))
  obtain ⟨hd, hq, hb, hi, he⟩ := qk_regs i k ha
  have h16 : qkACol k < 2 ^ 16 := by dsimp [qkACol, tmemQ]; omega
  have hq32 : qkACol k < 2 ^ 32 := by omega
  have hq64 : qkACol k < 2 ^ 64 := by omega
  have hreadD := readBits_b32 (L := L) (g := g) hd (by decide)
  have hreadA := readBits_b32 (L := L) (g := g) hq hq32
  have hreadB := readBits_b64 (L := L) (g := g) hb (qkWord_lt L i k)
  have hreadI := readBits_b32 (L := L) (g := g) hi (by decide : qkIdesc < 2 ^ 32)
  have hen : mmaEnable t (.reg (4091 + k.val)) = .ok (qkAccum k) := by
    simp [mmaEnable, readReg, he, bind, Except.bind, pure, Except.pure]
  have hoff : tmemOffset (BitVec.ofNat 64 (qkACol k)).toNat 0 = .ok (qkACol k) := by
    rw [Proof.toNat_ofNat_lt hq64]
    have hcast : (qkACol k : Int) < 65536 := by exact_mod_cast h16
    have hmod : (qkACol k : Int) % 65536 = qkACol k :=
      Int.emod_eq_of_lt (by positivity) hcast
    simp [tmemOffset, hmod, hcast, pure, Except.pure]
    exact h16
  have hB : TcShared.decode (BitVec.ofNat 64 (keyWord L i k)).toNat =
      some (keyDescriptor L i k) := by
    rw [Proof.toNat_ofNat_lt (qkWord_lt L i k)]
    exact decode_keyDescriptor hpre i k
  have hI : TcMma.decode .one true .f16 (BitVec.ofNat 64 qkIdesc).toNat = some qkDescriptor := by
    rw [Proof.toNat_ofNat_lt (by decide : qkIdesc < 2 ^ 64)]
    exact qkIdesc_decode
  have hmake : TcMma.makeOperands L (g / L.block) qkDescriptor (keyDescriptor L i k)
      (keyDescriptor L i k) = some { qkOperands L g i k with aTmem := none } := by
    simp only [TcMma.makeOperands, qkDescriptor, mma_group_thread hpre hg]
    rfl
  change mmaTmemTmpl L g t .one true .f16 857 (qkAReg k) 0 (.reg (3077 + k.val)) (.reg 859)
    mmaZeroMask (.reg (4091 + k.val)) (some (.imm 0)) {} = _
  rw [mmaTmem_formula hg hreadD hreadA hreadB hreadI hoff hen hB hI rfl hmake]
  rfl

/-- A fired qkMma operation records the checked template and advances the thread. -/
theorem fires_qkMma (hpre : Pre P L mem0) (hg : g < L.threads) (i : Nat) (k : Fin 16)
    {t u : TState} {e : Event} {ins : Instr} (ha : (Wg1Mma.code P L g).AtD ⟨.qkMma k, i⟩ t)
    (hc : kernel.code[(Site.qkMma k).pc]? = some ins)
    (hf : Fires (Site.qkMma k).pc (eventTmpl asms L g t ins.op) e (some u)) :
    e.kind = .tc (.mma tmemP (qkOperands L g i k) (qkAccum k) [0, 0, 0, 0]) ∧
      u = PTX.next t := by
  rw [qkMma_template hpre hg i k ha hc] at hf
  exact ⟨congrArg Event.kind hf.1, Option.some.inj hf.2⟩

/-- The eight emitted PV issues read P/V, with two alternating accumulator destinations. -/
theorem pvMma_template (hpre : Pre P L mem0) (hg : g < L.threads) (i : Nat) (k : Fin 8)
    {t : TState} {ins : Instr} (ha : (Wg1Mma.code P L g).AtD ⟨.pvMma k, i⟩ t)
    (hc : kernel.code[(Site.pvMma k).pc]? = some ins) :
    eventTmpl asms L g t ins.op =
      .tc (.mma (pvDest k) (pvOperands L g i k) (pvAccum i k) [0, 0, 0, 0]) (PTX.next t) := by
  obtain rfl := Option.some.inj (hc.symm.trans (pvInstr_code k))
  obtain ⟨hd, hp, hv, hi, he⟩ := pv_regs i k ha
  have h32 : pvDest k < 2 ^ 32 := by dsimp [pvDest, tmemO]; omega
  have h64 : pvDest k < 2 ^ 64 := by omega
  have hreadD := readBits_b32 (L := L) (g := g) hd h32
  have hreadA := readBits_b64 (L := L) (g := g) hp (pWord_lt L k)
  have hreadB := readBits_b64 (L := L) (g := g) hv (pvWord_lt L i k)
  have hreadI := readBits_b32 (L := L) (g := g) hi (by decide : pvIdesc < 2 ^ 32)
  have hen : mmaEnable t (.reg (4108 + k.val)) = .ok (pvAccum i k) := by
    simp [mmaEnable, readReg, he, bind, Except.bind, pure, Except.pure]
  have hA : TcShared.decode (BitVec.ofNat 64 (probabilityWord L k)).toNat =
      some (probabilityDescriptor L k) := by
    rw [Proof.toNat_ofNat_lt (pWord_lt L k)]
    exact decode_probabilityDescriptor hpre k
  have hB : TcShared.decode (BitVec.ofNat 64 (valueWord L i k)).toNat =
      some (valueDescriptor L i k) := by
    rw [Proof.toNat_ofNat_lt (pvWord_lt L i k)]
    exact decode_valueDescriptor hpre i k
  have hI : TcMma.decode .one true .f16 (BitVec.ofNat 64 pvIdesc).toNat = some pvDescriptor := by
    rw [Proof.toNat_ofNat_lt (by decide : pvIdesc < 2 ^ 64)]
    exact pvIdesc_decode
  have hmake : TcMma.makeOperands L (g / L.block) pvDescriptor (probabilityDescriptor L k)
      (valueDescriptor L i k) = some (pvOperands L g i k) := by
    simp only [TcMma.makeOperands, pvDescriptor, mma_group_thread hpre hg]
    rfl
  change mmaSmemTmpl L g t .one true .f16 (pvDReg k) (.reg (3093 + 3 * (k.val / 2)))
    (.reg (3094 + 3 * (k.val / 2) + k.val % 2)) (.reg 880) mmaZeroMask (.reg (4108 + k.val))
    (some (.imm 0)) {} = _
  rw [mmaSmem_formula hg hreadD hreadA hreadB hreadI hen hA hB hI hmake,
    Proof.toNat_ofNat_lt h64]
  rfl

/-- A fired pvMma operation records the checked template and advances the thread. -/
theorem fires_pvMma (hpre : Pre P L mem0) (hg : g < L.threads) (i : Nat) (k : Fin 8)
    {t u : TState} {e : Event} {ins : Instr} (ha : (Wg1Mma.code P L g).AtD ⟨.pvMma k, i⟩ t)
    (hc : kernel.code[(Site.pvMma k).pc]? = some ins)
    (hf : Fires (Site.pvMma k).pc (eventTmpl asms L g t ins.op) e (some u)) :
    e.kind = .tc (.mma (pvDest k) (pvOperands L g i k) (pvAccum i k) [0, 0, 0, 0]) ∧
      u = PTX.next t := by
  rw [pvMma_template hpre hg i k ha hc] at hf
  exact ⟨congrArg Event.kind hf.1, Option.some.inj hf.2⟩

private def queryDReg (k : Fin 16) : Nat :=
  if k.val = 0 then 820 else if k.val < 8 then 828 + k.val
  else if k.val = 8 then 822 else 827 + k.val

private theorem queryInstr_code (k : Fin 16) :
    kernel.code[(Site.qCopy k).pc]? =
      some ⟨none, .tcCp .one .s128x256b (queryDReg k) (.reg (3060 + k.val)) none⟩ := by
  fin_cases k
  · exact Flow.code_tmemCopy_0
  · exact Flow.code_tmemCopy_1
  · exact Flow.code_tmemCopy_2
  · exact Flow.code_tmemCopy_3
  · exact Flow.code_tmemCopy_4
  · exact Flow.code_tmemCopy_5
  · exact Flow.code_tmemCopy_6
  · exact Flow.code_tmemCopy_7
  · exact Flow.code_tmemCopy_8
  · exact Flow.code_tmemCopy_9
  · exact Flow.code_tmemCopy_10
  · exact Flow.code_tmemCopy_11
  · exact Flow.code_tmemCopy_12
  · exact Flow.code_tmemCopy_13
  · exact Flow.code_tmemCopy_14
  · exact Flow.code_tmemCopy_15

private theorem query_regs (i : Nat) (k : Fin 16) {t : TState}
    (h : (Wg1Mma.code P L g).AtD ⟨.qCopy k, i⟩ t) :
    t.regs (queryDReg k) = some (b32 (qCopyCol k)) ∧
    t.regs (3060 + k.val) = some (b64 (keyWord L 0 k)) := by
  constructor
  · fin_cases k <;> exact mma_reg h (by decide +kernel)
  · fin_cases k <;> exact mma_reg h (by decide +kernel)

/-- A query copy writes eight columns at the QK A address, with the same layout as the
K descriptor over the query tile, and covers all 128 datapath lanes. -/
def queryCopySpec (L : Launch) (g : Nat) (k : Fin 16) : TcCopy.Spec :=
  ⟨qCopyCol k, keyDescriptor L 0 k, .s128x256b, [ctaOf L g], none⟩

private theorem copy_formula {ta sd : Nat} {aa ss : BitVec 64} {desc : TcShared.Descriptor}
    {ctas : List Nat} (hg : g < L.threads) (ha : readBits L g t 32 (.reg ta) = .ok aa)
    (hs : readBits L g t 64 (.reg sd) = .ok ss) (hok : TcCopy.AddressOk .s128x256b aa.toNat)
    (hdesc : TcShared.decode ss.toNat = some desc)
    (hctas : L.ctaGroup (g / L.block) .one = some ctas) :
    tcTmpl L g t (.tcCp .one .s128x256b ta (.reg sd) none) =
      .tc (.cp ⟨aa.toNat, desc, .s128x256b, ctas, none⟩) (PTX.next t) := by
  rw [tcTmpl_tcCp_eq]
  simp only [hg, ↓reduceIte, ha, hs, hok, hdesc, hctas, bind, Except.bind, ofExec,
    pure, Except.pure]
end

/-- The exact Q shared-to-TMEM copy operation of the compiled QK prologue. -/
theorem qCopy_template (hpre : Pre P L mem0) (hg : g < L.threads) (i : Nat) (k : Fin 16)
    {t : TState} {ins : Instr} (ha : (Wg1Mma.code P L g).AtD ⟨.qCopy k, i⟩ t)
    (hc : kernel.code[(Site.qCopy k).pc]? = some ins) :
    eventTmpl asms L g t ins.op = .tc (.cp (queryCopySpec L g k)) (PTX.next t) := by
  obtain rfl := Option.some.inj (hc.symm.trans (queryInstr_code k))
  obtain ⟨hd, hb⟩ := query_regs i k ha
  have h16 : qCopyCol k < 2 ^ 16 := by dsimp [qCopyCol, tmemQ]; omega
  have h32 : qCopyCol k < 2 ^ 32 := by omega
  have h64 : qCopyCol k < 2 ^ 64 := by omega
  have hreadD := readBits_b32 (L := L) (g := g) hd h32
  have hreadB := readBits_b64 (L := L) (g := g) hb (qkWord_lt L 0 k)
  have hB : TcShared.decode (BitVec.ofNat 64 (keyWord L 0 k)).toNat =
      some (keyDescriptor L 0 k) := by
    rw [Proof.toNat_ofNat_lt (qkWord_lt L 0 k)]
    exact decode_keyDescriptor hpre 0 k
  have hok : TcCopy.AddressOk .s128x256b (BitVec.ofNat 64 (qCopyCol k)).toNat := by
    rw [Proof.toNat_ofNat_lt h64]
    unfold TcCopy.AddressOk
    rw [Nat.div_eq_of_lt h16, Nat.mod_eq_of_lt h16]
    refine ⟨rfl, ?_⟩
    change qCopyCol k + 8 ≤ 512
    dsimp [qCopyCol, tmemQ]
    omega
  change tcTmpl L g t (.tcCp .one .s128x256b (queryDReg k) (.reg (3060 + k.val)) none) = _
  rw [copy_formula hg hreadD hreadB hok hB (mma_group_thread hpre hg), Proof.toNat_ofNat_lt h64]
  rfl

/-- A fired qCopy operation records the checked template and advances the thread. -/
theorem fires_qCopy (hpre : Pre P L mem0) (hg : g < L.threads) (i : Nat) (k : Fin 16)
    {t u : TState} {e : Event} {ins : Instr} (ha : (Wg1Mma.code P L g).AtD ⟨.qCopy k, i⟩ t)
    (hc : kernel.code[(Site.qCopy k).pc]? = some ins)
    (hf : Fires (Site.qCopy k).pc (eventTmpl asms L g t ins.op) e (some u)) :
    e.kind = .tc (.cp (queryCopySpec L g k)) ∧ u = PTX.next t := by
  rw [qCopy_template hpre hg i k ha hc] at hf
  exact ⟨congrArg Event.kind hf.1, Option.some.inj hf.2⟩

/-- The shared Q byte read by a query copy, indexed by its logical head and contraction feature. -/
theorem queryCopyByteLoc (L : Launch) (g : Nat) (issue : Fin 16) (row : Fin 128)
    (k : Fin 16) (b : Fin 2) :
    let spec := queryCopySpec L g issue
    TcCopy.byteLoc spec.shape spec.src (ctaOf L g) (2 * (row.val * 16 + k.val) + b.val) =
      some ⟨.shared, ctaOf L g, TcShared.Swizzle.offset .b128
        (kvLinearByte L 0 (row.val % 64) (qkFeature issue row k) b.val)⟩ := by
  let n := 2 * (row.val * 16 + k.val) + b.val
  have hrow : n / 32 = row.val := by dsimp [n]; omega
  have hword : n % 32 = 2 * k.val + b.val := by dsimp [n]; omega
  have hlim : n < 4096 := by dsimp [n]; omega
  change TcCopy.byteLoc .s128x256b (keyDescriptor L 0 issue) (ctaOf L g) n = _
  simp [TcCopy.byteLoc, TcCpShape.sourceBytes, TcCpShape.rowBytes, TcCpShape.rows,
    hlim, hrow, hword, keyDescriptor, TcShared.byteAddress, TcShared.linear,
    TcShared.Swizzle.sectors, kvLinearByte, qkFeature, qkBDelta]
  apply congrArg (TcShared.Swizzle.offset .b128)
  omega

private def queryTmaDReg (k : Fin 8) : Nat := if k.val = 0 then 810 else 811 + 2 * k.val
private def queryTmaXReg (k : Fin 8) : Nat := 812 + 2 * k.val

private def queryTmaOp (k : Fin 8) : Op :=
  .cpTensor true false (queryTmaDReg k) 0 (.reg 3058)
    [.reg (queryTmaXReg k), .reg 812, .reg 459, .reg 460] 811 0 none .tile
    (some (.reg 3059))

private theorem queryTma_code (k : Fin 8) :
    kernel.code[(Site.qLoad k).pc]? = some ⟨none, queryTmaOp k⟩ := by
  fin_cases k
  · exact Flow.code_tensorCopy_4
  · exact Flow.code_tensorCopy_5
  · exact Flow.code_tensorCopy_6
  · exact Flow.code_tensorCopy_7
  · exact Flow.code_tensorCopy_8
  · exact Flow.code_tensorCopy_9
  · exact Flow.code_tensorCopy_10
  · exact Flow.code_tensorCopy_11

private theorem queryTma_regs (i : Nat) (k : Fin 8) {t : TState}
    (h : (Wg1Mma.code P L g).AtD ⟨.qLoad k, i⟩ t) :
    t.regs (queryTmaDReg k) = some (b32 (L.sharedBase + qDstOff k)) ∧
    t.regs (queryTmaXReg k) = some (b32 (qCoord k)) ∧
    t.regs 812 = some (b32 0) ∧ t.regs 459 = some (b32 (queryOf L g)) ∧
    t.regs 460 = some (b32 (batchOf L g)) ∧ t.regs 811 = some (b32 (qTmaAddr L)) ∧
    t.regs 3058 = some (b64 (P.param1Base + qMapOff)) := by
  fin_cases k <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact mma_reg h (by decide +kernel)

/-- The eight query TMA loads use the launch Q map and contiguous 8192-byte shared frames. -/
def queryTmaSpec (P : Params) (L : Launch) (g : Nat) (k : Fin 8) : TensorCopy.Spec :=
  ⟨⟨3, mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass,
    ![(qCoord k : Int), 0, (queryOf L g : Int), (batchOf L g : Int)],
    ⟨.shared, ctaOf L g, L.sharedBase + qDstOff k⟩, none⟩,
    ⟨.shared, ctaOf L g, qTmaAddr L⟩, true, .one⟩

private theorem queryTma_mapAddress {t : TState}
    (hpre : Pre P L mem0) (hr : t.regs 3058 = some (b64 (P.param1Base + qMapOff))) :
    tensorMapAddress L g t (.reg 3058) = .ok (P.param1Base + qMapOff) := by
  have ha : P.param1Base + qMapOff < 2 ^ 64 := by
    have h := hpre.param1Range
    unfold qMapOff
    omega
  have hrb := readBits_b64 (L := L) (g := g) hr ha
  simp only [tensorMapAddress, readValue, readReg, hr, bind, Except.bind, pure, Except.pure, b64]
  rw [hrb]
  exact congrArg Except.ok (Proof.toNat_ofNat_lt ha)

private theorem queryTma_dst {t : TState} (hpre : Pre P L mem0) (k : Fin 8)
    (hr : t.regs (queryTmaDReg k) = some (b32 (L.sharedBase + qDstOff k))) :
    sharedEffAddr L g t true (queryTmaDReg k) 0 =
      .ok ⟨.shared, ctaOf L g, L.sharedBase + qDstOff k⟩ := by
  have ha : L.sharedBase + qDstOff k < 2 ^ 32 := by
    have hb := sharedBase_lt hpre
    unfold qDstOff
    omega
  have hrb := readBits_b32 (L := L) (g := g) hr ha
  have htr : (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + qDstOff k) +
      BitVec.ofInt 64 0)).toNat = L.sharedBase + qDstOff k := by
    have h64 : L.sharedBase + qDstOff k < 2 ^ 64 := by omega
    simp only [BitVec.ofInt_ofNat, BitVec.add_zero, truncBits_ofNat ha (by decide),
      Proof.toNat_ofNat_lt h64]
  simp only [sharedEffAddr, readReg, hr, b32, bind, Except.bind, hrb, htr, pure, Except.pure]
  rfl

/-- The Q descriptor, shared tile, and four frozen coordinates give a defined load template. -/
theorem qLoad_template (hpre : Pre P L mem0) (hg : g < L.threads) (i : Nat) (k : Fin 8)
    {t : TState} {ins : Instr} (ha : (Wg1Mma.code P L g).AtD ⟨.qLoad k, i⟩ t)
    (hc : kernel.code[(Site.qLoad k).pc]? = some ins) :
    eventTmpl asms L g t ins.op =
      .tensorIssue (P.param1Base + qMapOff) (queryTmaSpec P L g k) (PTX.next t) := by
  obtain rfl := Option.some.inj (hc.symm.trans (queryTma_code k))
  let addr := P.param1Base + qMapOff
  let cs : List Opnd := [.reg (queryTmaXReg k), .reg 812, .reg 459, .reg 460]
  let spec := queryTmaSpec P L g k
  let desc : TensorDescriptor.Descriptor 3 :=
    mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass
  let origin : Fin 4 → Int := spec.origin
  let vs := [BitVec.ofNat 64 (qCoord k), 0, BitVec.ofNat 64 (queryOf L g),
    BitVec.ofNat 64 (batchOf L g)]
  obtain ⟨hd, hx, hz, hq, hb, hm, hmap⟩ := queryTma_regs i k ha
  have hPolicyReg : t.regs 3059 = some (b64 qCachePolicy) := by
    fin_cases k <;> exact mma_reg ha (by decide +kernel)
  have hPolicy : cachePolicyRead L g t (some (.reg 3059)) = .ok () := by
    simp [cachePolicyRead, readBits_b64 hPolicyReg (by decide), bind, Except.bind,
      pure, Except.pure]
  have hMapAddr : tensorMapAddress L g t (.reg 3058) = .ok addr :=
    queryTma_mapAddress hpre hmap
  have hAlign : addr % 64 = 0 := by
    have hp := hpre.param1Align
    dsimp [addr, qMapOff]
    omega
  have hDescriptor : L.tensorMaps addr = some ⟨3, desc⟩ := hpre.mapQBind
  have hValid : TensorDescriptor.Valid desc := Geometry.mapQ_valid_of_pre hpre
  have hTensorMap : tensorMap L g t (.reg 3058) cs .tile =
      .ok (addr, ⟨3, desc⟩) := by
    simp [tensorMap, hMapAddr, hAlign, hDescriptor, cs, TensorMode.coordinates,
      bind, Except.bind, pure, Except.pure]
    exact hValid
  have hDst : sharedEffAddr L g t true (queryTmaDReg k) 0 = .ok spec.sharedBase :=
    queryTma_dst hpre k hd
  have hDstAlign : spec.sharedBase.addr % 128 = 0 := by
    have hbase : L.sharedBase % 1024 = 0 := by rw [hpre.sharedBase]; exact hpre.sharedAlignment
    change (L.sharedBase + qDstOff k) % 128 = 0
    unfold qDstOff
    omega
  have hmLt : L.sharedBase + 222776 < 2 ^ 32 := by have hh := sharedBase_lt hpre; omega
  have hmAlign : (L.sharedBase + 222776) % 8 = 0 := by have hh := hShared16 hpre; omega
  rw [qTmaAddr_eq] at hm
  have hMbar : mbarClusterLoc L g t 811 0 = .ok spec.mbar := by
    change mbarClusterLoc L g t 811 0 = .ok ⟨.shared, ctaOf L g, qTmaAddr L⟩
    rw [qTmaAddr_eq]
    exact mbarClusterLoc_b32 hm hmLt hmAlign
  have hq31 : queryOf L g < 2 ^ 31 := (queryOf_lt hpre hg).trans hpre.sqLt
  have hb31 : batchOf L g < 2 ^ 31 := (batchOf_lt hpre hg).trans hpre.bLt
  have hx31 : qCoord k < 2 ^ 31 := by dsimp [qCoord]; omega
  have hRead : cs.mapM (readBits L g t 32) = .ok vs := by
    simp only [cs, vs, List.mapM_cons, List.mapM_nil, readBits_b32 hx (by omega),
      readBits_b32 hz (by decide), readBits_b32 hq (by omega), readBits_b32 hb (by omega),
      bind, Except.bind, pure, Except.pure]
    rfl
  have hOrigin : (fun axis : Fin 4 => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt) =
      origin := by
    have fromNat (n : Nat) (hn : n < 2 ^ 31) :
        (BitVec.ofNat 32 (BitVec.ofNat 64 n).toNat).toInt = n := by
      rw [Proof.toNat_ofNat_lt (by omega : n < 2 ^ 64)]
      exact toInt_ofNat_lt32 hn
    funext a
    fin_cases a
    · exact fromNat _ hx31
    · rfl
    · exact fromNat _ hq31
    · exact fromNat _ hb31
  have hBox : requireBoxAligned desc origin = .ok () := by
    apply (requireBoxAligned_eq_ok _ _).mpr
    change ((qCoord k : Nat) : Int) * 2 % 16 = 0
    unfold qCoord
    omega
  have hCopy :
      tensorLoadCopy L g t true false (queryTmaDReg k) 0 (.reg 3058) cs 811 0 .tile =
        .ok (addr, spec) := by
    simp only [tensorLoadCopy, hTensorMap, hDst, hDstAlign, hMbar, hRead, TensorMode.transfer,
      TensorMode.rowCoordinates, hOrigin, bind, Except.bind, pure, Except.pure, ↓reduceIte]
    rw [hBox]
    rfl
  have hcta : ctaOf L g < L.grid :=
    (Nat.div_lt_iff_lt_mul (by rw [hpre.block]; decide)).mpr hg
  have hself : CtaInCluster L (ctaOf L g) (ctaOf L g) := ⟨hcta, hcta, rfl⟩
  have hRoute : TensorRoute L (g / L.block) spec.clusterAddress spec.group spec.sharedBase
      spec.mbar :=
    ⟨hpre.launchValid.1, rfl, rfl, hself, hself, fun _ => ⟨rfl, rfl⟩,
      (sameCtaGroup_iff ..).mpr ⟨hself, rfl⟩⟩
  change tensorTmpl L g t (.cpTensor true false (queryTmaDReg k)
    0 (.reg 3058) cs 811 0 none .tile (some (.reg 3059))) = _
  simp only [tensorTmpl, ofExec, hPolicy, hCopy, hRoute, bind, Except.bind, pure, Except.pure,
    ↓reduceIte]
  rfl

/-- A recorded Q tile issue names that exact query map, coordinate and destination frame. -/
theorem fires_qLoad (hpre : Pre P L mem0) (hg : g < L.threads) (i : Nat) (k : Fin 8)
    {t u : TState} {e : Event} {ins : Instr} (ha : (Wg1Mma.code P L g).AtD ⟨.qLoad k, i⟩ t)
    (hc : kernel.code[(Site.qLoad k).pc]? = some ins)
    (hf : Fires (Site.qLoad k).pc (eventTmpl asms L g t ins.op) e (some u)) :
    e.kind = .tensorIssue (P.param1Base + qMapOff) (queryTmaSpec P L g k) ∧ u = PTX.next t := by
  rw [qLoad_template hpre hg i k ha hc] at hf
  exact ⟨congrArg Event.kind hf.1, Option.some.inj hf.2⟩


end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaDataTrace
