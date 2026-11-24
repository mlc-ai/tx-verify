-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPvInputLayout
public import Kernels.TmlFa4Fwd.Proof.MmaQueryCoverage
import Lemmas.Flow.Store
import Lemmas.Tcgen05.MmaOperandObservations

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow

noncomputable section

/-- The shared bank occupied by a Q, K or V operand byte. -/
structure SharedOperandRange (l : Launch) (g : Nat) (loc : Loc) : Prop where
  space : loc.space = .shared
  cta : loc.cta = g/l.block
  lower : l.sharedBase+3072 ≤ loc.addr
  upper : loc.addr < l.sharedBase+166912

private theorem operandCoordinate {index : Nat} (hi : index < 4096) :
    ∃ row k byte, row < 128 ∧ k < 16 ∧ byte < 2 ∧ index = qkByteIndex row k byte := by
  refine ⟨index/32,(index/2)%16,index%2,by omega,by omega,by omega,?_⟩
  unfold qkByteIndex
  omega

variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
include hp

/-- Each byte accepted by one of the shared QK descriptors stays in its CTA's Q or cache bank. -/
theorem qkOperandBankRange (g : Nat) (block : Fin 4) (step : Fin 8) (use : Nat) {op : TcMma.Operand}
    {index : Nat} {loc : Loc} (hLoc : (qkOperands l g block step use).byteLoc op index = some loc) :
    SharedOperandRange l g loc ∧
      qkInputStart l block use op + 16384 * qkPlane step ≤ loc.addr ∧
      loc.addr < qkInputStart l block use op + 16384 * (qkPlane step + 1) := by
  have hSite := TcMma.OperandSpec.byteLoc_index_lt hLoc
  have hIndex : index < 4096 := by
    cases op <;> simpa [qkOperands,qkDescriptor,TcMma.Operand.rows,TcMma.Operand.extent,
      TcMma.Kind.k,TcMma.Kind.width] using hSite
  obtain ⟨row,k,byte,hRow,hK,hByte,hIndex⟩ := operandCoordinate hIndex
  rw [hIndex,qkInputByteLoc l g block step use op hRow hK hByte] at hLoc
  obtain rfl := Option.some.inj hLoc.symm
  let raw := qkInputStart l block use op + qkFragment step + 128*row + 2*k + byte
  have hAlign := hp.shared.1
  have hBase : (l.sharedBase+3072) % 128 = 0 ∧ (l.sharedBase+166912) % 128 = 0 := by omega
  have hParts : step.val / 4 < 2 ∧ step.val % 4 < 4 := by
    have := step.isLt
    omega
  have hRaw : l.sharedBase+3072 ≤ raw ∧ raw < l.sharedBase+166912 := by
    have hStage := (qkStage block).isLt
    have hSlot : kvSlot use < 3 := Nat.mod_lt _ (by decide)
    cases op <;> dsimp only [raw,qkInputStart,qStart,kvStart,qkFragment] <;> omega
  have hOffset := swizzle_offset_bounds .b128 0 raw
  have hBankAlign : (qkInputStart l block use op + 16384 * qkPlane step) % 128 = 0 := by
    cases op <;> simp only [qkInputStart, qStart, kvStart, qkPlane] <;> omega
  have hBankLo : qkInputStart l block use op + 16384 * qkPlane step ≤ raw := by
    simp only [raw, qkPlane, qkFragment]
    omega
  have hBankHi : raw < qkInputStart l block use op + 16384 * (qkPlane step + 1) := by
    simp only [raw, qkPlane, qkFragment]
    omega
  refine ⟨⟨rfl,rfl,?_,?_⟩,?_,?_⟩
  · change l.sharedBase + 3072 ≤ TensorSwizzle.offset .b128 0 raw
    omega
  · change TensorSwizzle.offset .b128 0 raw < l.sharedBase + 166912
    omega
  · change qkInputStart l block use op + 16384 * qkPlane step ≤ TensorSwizzle.offset .b128 0 raw
    omega
  · change TensorSwizzle.offset .b128 0 raw <
      qkInputStart l block use op + 16384 * (qkPlane step + 1)
    omega

/-- Every shared QK operand byte lies in the Q or cache banks of its CTA. -/
theorem qkOperandRange (g : Nat) (block : Fin 4) (step : Fin 8) (use : Nat) {op : TcMma.Operand}
    {index : Nat} {loc : Loc} (hLoc : (qkOperands l g block step use).byteLoc op index = some loc) :
    SharedOperandRange l g loc := (qkOperandBankRange hp g block step use hLoc).1

/-- A shared PV byte belongs to the value cache within the data banks of its CTA. -/
theorem pvOperandBankRange (g : Nat) (block : Fin 4) (step : Fin 8) (use : Nat) {op : TcMma.Operand}
    {index : Nat} {loc : Loc} (hLoc : (pvOperands l g block step use).byteLoc op index = some loc) :
    SharedOperandRange l g loc ∧ l.sharedBase + 68608 ≤ loc.addr := by
  cases op with
  | a => simp [TcMma.OperandSpec.byteLoc,pvOperands] at hLoc
  | b =>
    have hIndex : index < 4096 := by
      simpa [pvOperands,pvDescriptor,TcMma.Operand.rows,TcMma.Operand.extent,
        TcMma.Kind.k,TcMma.Kind.width] using TcMma.OperandSpec.byteLoc_index_lt hLoc
    obtain ⟨col,k,byte,hCol,hK,hByte,hIndex⟩ := operandCoordinate hIndex
    rw [hIndex,pvValueByteLoc l g block step use hp.shared.1 hCol hK hByte] at hLoc
    simp only [Nat.add_assoc] at hLoc
    obtain rfl := Option.some.inj hLoc.symm
    let key := pvKeyRow step k
    let lane := 8*(key%8)+(col%64)/8
    let off := 2*(col%8)+byte
    have hKey : key < 128 := by have := step.isLt; dsimp [key,pvKeyRow]; omega
    have hOff : off < 16 := by dsimp [off]; omega
    have hSlot : kvSlot use < 3 := Nat.mod_lt _ (by decide)
    have hRange := kvCopyAddress_range (stage := kvSlot use) (lane := lane)
      (group := key/8) (upper := decide (64 ≤ col)) (byte := off) hp.shared.1 hSlot
      (by omega) hOff
    refine ⟨⟨rfl,rfl,?_,?_⟩,?_⟩
    · change l.sharedBase+3072 ≤ kvCopyAddress l.sharedBase (kvSlot use) lane (key/8)
        (decide (64 ≤ col))+off
      omega
    · change kvCopyAddress l.sharedBase (kvSlot use) lane (key/8)
        (decide (64 ≤ col))+off < l.sharedBase+166912
      omega

    · change l.sharedBase+68608 ≤ kvCopyAddress l.sharedBase (kvSlot use) lane (key/8)
        (decide (64 ≤ col))+off
      exact hRange.1

/-- A shared QK A byte belongs to the selected physical query plane. -/
theorem QueryOperandFragment.operandBankRange {g index : Nat} {stage : Fin 2} {step : Fin 8}
    {op : TcMma.OperandSpec} {loc : Loc} (hQuery : QueryOperandFragment l g stage step op)
    (hLoc : op.byteLoc .a index = some loc) :
    SharedOperandRange l g loc ∧
      qStart l stage + 16384 * qkPlane step ≤ loc.addr ∧
      loc.addr < qStart l stage + 16384 * (qkPlane step + 1) := by
  let block : Fin 4 := ⟨stage.val,stage.isLt.trans (by decide)⟩
  have hStage : qkStage block = stage := Fin.ext (Nat.mod_eq_of_lt stage.isLt)
  have hSame : op.byteLoc .a index = (qkOperands l g block step 0).byteLoc .a index := by
    simp only [TcMma.OperandSpec.byteLoc,qkOperands,hStage,hQuery.descriptor,hQuery.address,
      hQuery.ctaLow,hQuery.ctaHigh,hQuery.shared]
  simpa only [qkInputStart, hStage] using
    qkOperandBankRange hp g block step 0 (hSame.symm.trans hLoc)

/-- The A byte of any actual QK query snapshot is within the allocated Q region. -/
theorem QueryOperandFragment.operandRange {g index : Nat} {stage : Fin 2} {step : Fin 8}
    {op : TcMma.OperandSpec} {loc : Loc} (hQuery : QueryOperandFragment l g stage step op)
    (hLoc : op.byteLoc .a index = some loc) : SharedOperandRange l g loc :=
  (hQuery.operandBankRange hp hLoc).1

/-- The physical shared banks used by MMA operands are backed for every launched thread. -/
theorem SharedOperandRange.allocated {g : Nat} (hg : g < l.threads) {loc : Loc}
    (h : SharedOperandRange l g loc) : m loc ≠ none := by
  have hCta : g/l.block < l.grid := by
    change g < l.grid*l.block at hg
    rw [hp.block] at hg ⊢
    omega
  let offset := loc.addr-l.sharedBase
  have hLo := h.lower
  have hHi := h.upper
  have hOffset : offset < 232448 := by dsimp [offset]; omega
  have hLocation : loc = ⟨.shared,g/l.block,l.sharedBase+offset⟩ := by
    obtain ⟨space,cta,addr⟩ := loc
    simp only [Loc.mk.injEq]
    exact ⟨h.space,h.cta,by dsimp [offset] at *; omega⟩
  rw [hLocation]
  exact hp.shared.2.2 _ hCta offset hOffset

end
end PTX.Kernels.TmlFa4Fwd.Mma
