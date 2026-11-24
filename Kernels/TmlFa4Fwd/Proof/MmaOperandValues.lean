-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkKeyLayout
public import Lemmas.Tcgen05.MmaOperandObservations
public import Lemmas.Tcgen05.MmaReadSources
public import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX

noncomputable section

/-- The physical byte in an operand is supplied by an ordered write of its buffer generation. -/
structure OperandByteSource (l : Launch) (X : Execution) (issue : EvId)
    (isB : Bool) (index : Nat) (loc : Loc) (value : Byte) : Prop where
  source : ∃ (write : AsyncCopy.Ref) (footprint : Acc) (written : List Byte),
    X.MemWrites write footprint written ∧ footprint.Covers loc ∧
    wbyte footprint written loc = some value ∧
    modelCausality l X loc write (.async issue (.mmaRead isB index)) ∧
    ∀ other acc data, X.MemWrites other acc data → acc.Covers loc →
      other = write ∨ modelCausality l X loc other write ∨
        modelCausality l X loc (.async issue (.mmaRead isB index)) other

theorem operandByte_observed {K : Kernel} {A : List Assumption} {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l K A m X) {issue : EvId} {d : Nat}
    {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} {operands : AsyncCopy.MmaOperands}
    (hi : X.MmaIssue issue d s acc mask) (ho : X.async.mmaOperands issue = some operands)
    {isB : Bool} {index : Nat} {loc : Loc} {value : Byte}
    (hl : s.byteLoc (if isB then .b else .a) index = some loc)
    (hs : OperandByteSource l X issue isB index loc value) :
    (if isB then operands.b else operands.a)[index]? = some (some value) := by
  obtain ⟨write, footprint, written, hw, hc, hByte, hv, hOrder⟩ := hs.source
  obtain ⟨seen, hr, hRead⟩ := hX.mma_read_exists hi ho hl
  have hLoc : loc.at 0 = loc := by cases loc; simp [Loc.at]
  have h := read_byte_of_ordered_reuse hX hr.memReads (k := 0) Nat.one_pos hw
    (by change footprint.Covers (loc.at 0); rw [hLoc]; exact hc)
    (by change modelCausality l X (loc.at 0) write _; rw [hLoc]; exact hv)
    (by simpa only [hLoc] using hOrder)
  have hs : seen = some value := by
    simpa only [List.getElem?_cons_zero, hLoc, hByte, Option.some.injEq] using h
  rw [hRead, hs]

/-- Assemble the two consecutive observed bytes of an ideal BF16 element. -/
theorem idealBf16Element_of_bytes {op : TcMma.Operand} {bytes : List (Option Byte)}
    {row k : Nat} {x : ℝ}
    (lo : bytes[qkByteIndex row k 0]? = some (some ((Value.float .bf16 x).byteAt 0)))
    (hi : bytes[qkByteIndex row k 1]? = some (some ((Value.float .bf16 x).byteAt 1))) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) op bytes row k = .ok x := by
  have hIdx : qkByteIndex row k 0 = 2 * (row * 16 + k) := by unfold qkByteIndex; omega
  have hSucc : qkByteIndex row k 1 = qkByteIndex row k 0 + 1 := rfl
  rw [hSucc] at hi
  have h := TcMma.take_two lo hi
  rw [hIdx] at h
  unfold Assumption.idealMmaElement
  simp only [TcMma.elementBytes, TcMma.Kind.k, TcMma.Kind.width, Nat.mul_comm]
  rw [h]
  simp [rebuild, Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes, valFloat,
    List.range_succ]
  rfl

/-- A zero-source-size ordinary copy supplies BF16 positive zero. -/
theorem idealBf16Element_of_zeroBytes {op : TcMma.Operand} {bytes : List (Option Byte)}
    {row k : Nat}
    (lo : bytes[qkByteIndex row k 0]? = some (some AsyncCopy.zeroByte))
    (hi : bytes[qkByteIndex row k 1]? = some (some AsyncCopy.zeroByte)) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) op bytes row k = .ok 0 := by
  have hIdx : qkByteIndex row k 0 = 2 * (row * 16 + k) := by unfold qkByteIndex; omega
  have hSucc : qkByteIndex row k 1 = qkByteIndex row k 0 + 1 := rfl
  rw [hSucc] at hi
  have h := TcMma.take_two lo hi
  rw [hIdx] at h
  unfold Assumption.idealMmaElement
  simp only [TcMma.elementBytes, TcMma.Kind.k, TcMma.Kind.width, Nat.mul_comm]
  rw [h]
  have hr : rebuild 1 [some AsyncCopy.zeroByte, some AsyncCopy.zeroByte] =
      .ok (.bits 16 0) := by
    simp [AsyncCopy.zeroByte, Value.byteAt, rebuild, Value.bytes, rebuild.halves]
    rfl
  rw [hr]
  change valFloat .bf16 (.bits 16 0) = .ok 0
  exact (valFloat_of_classify (x := .zero false) (fun _ _ h => by cases h)
    (by rfl)).trans (by rfl)

/-- Each Q byte comes from the logical row of its TMA box, or from its descriptor's zero fill. -/
theorem qkQueryByteSource {p : Params} {l : Launch} {m : Mem0} {A : List Assumption}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel A m X)
    (hFrame : OutputFootprint p X) (g : Nat) (block : Fin 4) (step : Fin 8)
    (absoluteRow head : Nat) (hh : head < p.heads) (barrier : Loc) (clusterAddress : Bool)
    {row k byte : Nat} (hr : row < 128) (hk : k < 16) (hb : byte < 2)
    {mma copy : EvId} {o : TensorCopy.Observation} (ho : X.tensor copy = some o)
    (hn : o.effects.notified = true) :
    let slot := qkQSlot p step hr hk hb
    let spec := qInputSpec p (64 * qkPlane step) absoluteRow head
      ⟨.shared, g / l.block, qStart l (qkStage block) + 16384 * qkPlane step⟩ barrier clusterAddress
    let write := AsyncCopy.Ref.async copy (.write (.load slot.1.val row byte))
    let read := AsyncCopy.Ref.async mma (.mmaRead false (qkByteIndex row k byte))
    let loc := spec.sharedLoc slot
    o.spec = spec →
    modelCausality l X loc write read →
    (∀ other acc data, X.MemWrites other acc data → acc.Covers loc →
      other = write ∨ modelCausality l X loc other write ∨
        modelCausality l X loc read other) →
    OperandByteSource l X mma false (qkByteIndex row k byte) loc
      ((Value.float .bf16 (if absoluteRow + row < p.totalQ then
        p.q (absoluteRow + row) head (64 * qkPlane step + qkPlaneColumn step k)
        else 0)).byteAt byte)
  := by
  dsimp only
  intro hs hv hOrder
  rcases o with ⟨spec, effects⟩
  dsimp only at hs
  subst spec
  have hCol := qkPlaneColumn_lt step hk
  have hPlane : qkPlane step < 2 := by unfold qkPlane; have := step.isLt; omega
  have hWrite := qInputSlotWritten hp hX (fun w a bs loc hw hc hl => by
    rcases hFrame w a bs loc hw hc hl with hO | ⟨q, hq, h, hH, j, hj, rfl⟩
    · exact .inl hO
    · exact .inr (lseByte_in hq hH hj)) ho hn rfl (qkQSlot p step hr hk hb)
    (by change 64 * qkPlane step + qkPlaneColumn step k < 128; omega) hh
  refine ⟨_, _, _, hWrite, ?_, ?_, hv, hOrder⟩
  · exact ⟨rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
  · simp [wbyte, qkQSlot]
    rfl

end
end PTX.Kernels.TmlFa4Fwd.Mma
