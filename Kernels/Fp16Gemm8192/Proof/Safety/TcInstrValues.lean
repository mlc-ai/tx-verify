-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TcWrites
public import Kernels.Fp16Gemm8192.Proof.Safety.MemoryAccess
public import Kernels.Fp16Gemm8192.Proof.Support.Numerics
public import Lemmas.Protocol.Region
public import Lemmas.Tcgen05.MmaReadSources
public import Lemmas.Tensor.TensorReadSources
public import Lemmas.Tcgen05.MmaOperandObservations
public import Lemmas.Tensor.TensorAddress

@[expose] public section

/-! # The MMAs' operand elements are FP16 values, from the interface

The two bytes of an MMA operand element are the two bytes of element `(x, y)` of one tensor
load's box, each read from that load's write (`OperandCopies`, `mma_read_of_tensor_write`). A
tensor load reads the `A` or the `B` map (`ThreadFacts.tensor_issue`, `Memory.operand_base`)
inside its box (`ThreadFacts.tensor_bounds`): element `(x, y)` is the matrix element at the
box's origin plus `(x, y)` (`copy_readLoc`). No write reaches the input matrices
(`Memory.global_access`), so the load copies their initial bytes: the two bytes of one FP16
value (`Pre.inputA`, `Pre.inputB`, `copy_element`). So every operand element of an MMA that read
its operands is an FP16 value (`operand_elements`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX PTX.Flow TcMma TensorDescriptor

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The slot of element `(x, y)`, byte `z` of an operand map's box. -/
def boxSlot (b : Nat) (cls : AllocationClass) {x y z : Nat} (hx : x < 64) (hy : y < 128)
    (hz : z < 2) : TensorTransfer.Slot (Fp16Gemm8192.mapA b cls) :=
  ⟨⟨x, by simpa [Fp16Gemm8192.mapA, encodeTiled, TensorTile.count, TensorTile.step] using hx⟩,
    ⟨y, by simpa [Fp16Gemm8192.mapA, encodeTiled, TensorTile.rows, TensorTile.rowsOf,
      TensorTile.count, TensorTile.step] using hy⟩,
    ⟨z, by simpa [Fp16Gemm8192.mapA, encodeTiled, Format.bytes] using hz⟩⟩

/-- A tensor load through an operand map writes only the elements `(x, y)` of its box. -/
theorem copy_slot {b : Nat} {cls : AllocationClass} {origin : Fin 2 → Int} {cta st : Nat}
    {mb : Loc} {ca : Bool} {grp : CtaGroup} {x y z : Nat} {o : TensorCopy.Observation}
    (hs : o.spec = stageCopy (Fp16Gemm8192.mapA b cls) origin cta st mb ca grp) {v : Byte}
    (hw : TensorCopy.writeByte o x y z = some v) : x < 64 ∧ y < 128 ∧ z < 2 := by
  obtain ⟨spec, eff⟩ := o
  simp only at hs
  subst hs
  obtain ⟨slot, hsl, -⟩ := Option.bind_eq_some_iff.mp hw
  unfold TensorTransfer.slotAt at hsl
  split_ifs at hsl with h1 h2 h3
  simp only [stageCopy, Fp16Gemm8192.mapA, encodeTiled, TensorTile.count, TensorTile.step,
    TensorTile.rows, TensorTile.rowsOf, Format.bytes] at h1 h2 h3
  exact ⟨by simpa using h1, by simpa using h2, h3⟩

/-- A tensor load through an operand map reads, at element `(x, y)` of its box inside the map,
the matrix element at the box's origin plus `(x, y)`. -/
theorem copy_readLoc {b : Nat} {cls : AllocationClass} {origin : Fin 2 → Int} {x y z : Nat}
    (hno : ¬ TensorHasOob (Fp16Gemm8192.mapA b cls) origin none) (hx : x < 64) (hy : y < 128)
    (hz : z < 2) :
    ∃ row col : Nat, row < 8192 ∧ col < 8192 ∧ (row : Int) = origin 1 + y ∧
      (col : Int) = origin 0 + x ∧ ∀ cta st mb ca grp,
      TensorCopy.readLoc (stageCopy (Fp16Gemm8192.mapA b cls) origin cta st mb ca grp) x y z =
        some ((elementLoc b row col).at z) := by
  have hslot : TensorTransfer.slotAt (Fp16Gemm8192.mapA b cls) x y z =
      some (boxSlot b cls hx hy hz) := by
    simp [TensorTransfer.slotAt, boxSlot, Fp16Gemm8192.mapA, encodeTiled, TensorTile.count,
      TensorTile.step, TensorTile.rows, TensorTile.rowsOf, Format.bytes, hx, hy, hz]
  have hin := not_exists.mp hno (boxSlot b cls hx hy hz)
  rw [not_not] at hin
  have h0 := hin 0
  have h1 := hin (Fin.succ 0)
  simp only [TensorTransfer.coord, TensorTransfer.index, TensorTile.coord, TensorTile.indexOf,
    geometry, Fp16Gemm8192.mapA, encodeTiled, boxSlot, Fin.cases_succ, Fin.cases_zero] at h0 h1
  simp [TensorTile.step, TensorTile.unflatten] at h0 h1
  refine ⟨(origin 1 + y).toNat, (origin 0 + x).toNat, by omega, by omega, by omega, by omega,
    fun cta st mb ca grp => ?_⟩
  have hga : (stageCopy (Fp16Gemm8192.mapA b cls) origin cta st mb ca grp).globalAddress
      (boxSlot b cls hx hy hz) =
      some (b + 2 * (8192 * (origin 1 + y).toNat + (origin 0 + x).toNat) + z) := by
    change TensorAddress.lookup (geometry (Fp16Gemm8192.mapA b cls))
      (TensorTransfer.coord (Fp16Gemm8192.mapA b cls) origin none (boxSlot b cls hx hy hz)) z = _
    rw [TensorAddress.lookup_some_iff]
    refine ⟨hin, by simpa [Fp16Gemm8192.mapA, encodeTiled, geometry, Format.bytes] using hz, ?_⟩
    simp only [TensorAddress.byteAddress, Fin.sum_univ_succ, Fin.sum_univ_zero, geometry,
      Fp16Gemm8192.mapA, encodeTiled, TensorTransfer.coord, TensorTransfer.index,
      TensorTile.coord, TensorTile.indexOf, boxSlot, Fin.cases_succ, Fin.cases_zero, Format.bytes]
    simp [TensorTile.step, TensorTile.unflatten]
    omega
  rw [TensorCopy.readLoc_source]
  refine Option.bind_eq_some_iff.mpr ⟨boxSlot b cls hx hy hz, hslot, ?_⟩
  unfold TensorCopy.source
  erw [hga]
  simp only [elementLoc, Loc.at]

/-- **A tensor load copies FP16 elements.** The two bytes a tensor load writes at element
`(x, y)` of its box are the two bytes of one FP16 value. -/
theorem copy_element (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {copy : EvId} {o : TensorCopy.Observation} {x y : Nat}
    (hobs : X.tensor copy = some o) (hw : ∀ z, z < 2 → ∃ v, TensorCopy.writeByte o x y z = some v) :
    ∃ val : ℝ, ∀ z, z < 2 →
      TensorCopy.writeByte o x y z = some ((Value.float .f16 val).byteAt z) := by
  obtain ⟨addr, hTI⟩ := (hX.tensor copy o hobs).1
  obtain ⟨pc, hget⟩ := hTI
  have hg := Frame.lt_of_get hX hget
  obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget nofun
  obtain ⟨lw, bw, jw, -, -, -, ⟨base, cls, origin, hsp, hmap, hpar⟩, -⟩ :=
    ht.tensor_issue hg hget hσ rfl
  have hno := ht.tensor_bounds hg hget hσ rfl
  rw [hsp] at hno
  obtain ⟨v0, hv0⟩ := hw 0 (by decide)
  obtain ⟨hx, hy, -⟩ := copy_slot hsp hv0
  obtain ⟨row, col, hr, hc, hre, hce, -⟩ := copy_readLoc (z := 0) hno hx hy (by decide)
  -- no write reaches an input matrix byte
  have hn : ∀ z, z < 2 → base = P.aBase ∨ base = P.bBase →
      ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers ((elementLoc base row col).at z) := by
    intro z hz hb w dst bytes hwr hcov
    have hint := Execution.MemWrites.intent hwr
    rcases Memory.global_access hpre hX ht hint hcov (by simp [elementLoc, Loc.at]) with
      ⟨h, -⟩ | ⟨-, ⟨-, -, h1, h2⟩, -⟩
    · cases h
    · have hdA := hpre.outputDisjointA
      have hdB := hpre.outputDisjointB
      simp only [elementLoc, Loc.at, matrixBytes] at h1 h2 hdA hdB
      rcases hb with rfl | rfl <;> omega
  -- byte `z` of the element is its initial byte
  have hbyte : ∀ z, z < 2 → ∀ v value, TensorCopy.writeByte o x y z = some v →
      mem0 ((elementLoc base row col).at z) = some (some value) →
      base = P.aBase ∨ base = P.bBase → v = value := by
    intro z hz v value hv hm hb
    obtain ⟨row', col', -, -, hre', hce', hrl⟩ := copy_readLoc hno hx hy hz
    obtain rfl : row' = row := by omega
    obtain rfl : col' = col := by omega
    exact tensor_writeByte_of_initial hX hobs ⟨pc, hget⟩ (by rw [hsp]; exact hrl _ _ _ _ _) hv hm
      (hn z hz hb)
  rcases Memory.operand_base hpre hmap hpar with rfl | rfl
  · refine ⟨P.a row col, fun z hz => ?_⟩
    obtain ⟨v, hv⟩ := hw z hz
    rw [hv, hbyte z hz v _ hv (hpre.inputA row hr col hc z hz) (.inl rfl)]
  · refine ⟨P.b row col, fun z hz => ?_⟩
    obtain ⟨v, hv⟩ := hw z hz
    rw [hv, hbyte z hz v _ hv (hpre.inputB row hr col hc z hz) (.inr rfl)]

/-- Two consecutive entries of a list are its two entries from the first. -/
theorem take_two {α : Type} {bs : List α} {n : Nat} {a b : α} (ha : bs[n]? = some a)
    (hb : bs[n + 1]? = some b) : (bs.drop n).take 2 = [a, b] := by
  apply List.ext_getElem?
  intro i
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i <;> simp [List.getElem?_drop, ha, hb]
  · simp [show ¬ i < 2 by omega]

/-- **An MMA's operand elements are FP16 values.** Each element of either operand of an MMA that
read its operands is an FP16 value. -/
theorem operand_elements (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hoc : OperandCopies L X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {ops : AsyncCopy.MmaOperands} (hi : X.MmaIssue i d s acc mask)
    (hops : X.async.mmaOperands i = some ops) (isB : Bool) {row k : Nat} (hrow : row < 256)
    (hk : k < 16) :
    ∃ val, Assumption.idealMmaElement (.f16 .f16 .f32) (if isB then .b else .a)
      (if isB then ops.b else ops.a) row k = .ok val := by
  obtain ⟨copy, o, x, y, hobs, hz⟩ := hoc i d s acc mask hi isB (row * 16 + k) (by omega)
  obtain ⟨val, hval⟩ := copy_element hpre hX ht hobs fun z hz' => (hz z hz').choose_spec.2.2.1
  have hb : ∀ z, z < 2 → (if isB then ops.b else ops.a)[2 * (row * 16 + k) + z]? =
      some (some ((Value.float .f16 val).byteAt z)) := by
    intro z hz'
    obtain ⟨l, hbl, hwl, -, hvis, hord⟩ := hz z hz'
    obtain ⟨observed, hr, hget⟩ := hX.tma.2.1.mma_read_exists hi hops hbl
    obtain ⟨addr, hTI⟩ := (hX.tensor copy o hobs).1
    rw [hget, mma_read_of_tensor_write hX hr hobs hTI hwl (hval z hz') hvis hord]
  have hl := take_two (hb 0 (by decide)) (hb 1 (by decide))
  simp only [Nat.add_zero] at hl
  have he : Assumption.idealMmaElement (.f16 .f16 .f32) .a (if isB then ops.b else ops.a) row k =
      .ok val :=
    idealMmaElement_of_bytes (by rw [hl]; simp [Value.toBytes, Value.bytes, FloatFmt.bytes,
      List.range_succ])
  refine ⟨val, ?_⟩
  cases isB
  · exact he
  · exact he

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
