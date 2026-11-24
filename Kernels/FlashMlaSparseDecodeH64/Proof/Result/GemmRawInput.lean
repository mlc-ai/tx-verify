-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.CacheGatherGeometry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GlobalFrame
import Lemmas.Tensor.TensorSwizzle
import Lemmas.Tensor.TensorReadSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawTmaDequant
import Lemmas.Flow.TensorCoords

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.RawGather

open PTX.Proof

noncomputable section

/-- A valid paged index's physical row lies inside that cache's tensor-map extent. -/
theorem rowOf_lt {blocks stride page : Nat} {idx : Int} (hp : 0 < page)
    (hpage : page ≤ stride / 528) (hidx : idx.toNat < blocks * page) :
    rowOf stride page idx < blocks * (stride / 528) := by
  have hblock : idx.toNat / page < blocks := (Nat.div_lt_iff_lt_mul hp).2 hidx
  have hlocal := Nat.mod_lt idx.toNat hp
  change idx.toNat / page * (stride / 528) + idx.toNat % page < blocks * (stride / 528)
  calc
    _ < (idx.toNat / page + 1) * (stride / 528) := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

/-- A valid coordinate fits the signed 32-bit gather operand without truncation. -/
theorem signed_row {blocks stride page : Nat} {idx : Int} (hp : 0 < page)
    (hpage : page ≤ stride / 528) (hidx : idx.toNat < blocks * page)
    (hcache : blocks * (stride / 528) < 2 ^ 31) :
    (BitVec.ofNat 32 (rowOf stride page idx)).toInt = rowOf stride page idx :=
  PTX.Flow.toInt_ofNat_lt32 ((rowOf_lt hp hpage hidx).trans hcache)

/-- An observed in-bounds gather byte copies the corresponding initial cache byte,
provided that byte has no program writer. -/
theorem writeByte_of_initial {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {o : TensorCopy.Observation} {address base blocks stride : Nat}
    {cls : TensorDescriptor.AllocationClass} {dst : Loc} {oy : Int} {rows : Fin 4 → Int}
    (ho : X.tensor i = some o) (hi : X.TensorIssue i address o.spec)
    (hs : o.spec.toTensorBox = box base blocks stride cls dst oy rows)
    (row : Fin 4) (x : Fin 144) (b : Fin 4) {value initial : Byte} {r : Nat}
    (hr : rows row = r) (hrow : r < blocks * (stride / 528)) (hx : x.val < 132)
    (hw : TensorCopy.writeByte o x.val row.val b.val = some value)
    (hm : mem0 ⟨.global, 0, base + r * 528 + 4 * x.val + b.val⟩ = some (some initial))
    (hn : ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers ⟨.global, 0, base + r * 528 + 4 * x.val + b.val⟩) :
    value = initial := by
  have ha := globalAddress (base := base) (cls := cls) dst oy rows row x b hr hrow hx
  have hl : TensorCopy.readLoc o.spec x.val row.val b.val =
      some ⟨.global, 0, base + r * 528 + 4 * x.val + b.val⟩ := by
    unfold TensorCopy.readLoc TensorTransfer.sourceLoc
    change (do
      let s ← TensorTransfer.slotAt o.spec.toTensorBox.descriptor x.val row.val b.val
      let a ← o.spec.toTensorBox.globalAddress s
      some (Loc.mk .global 0 a)) = _
    rw [hs]
    change ((TensorTransfer.slotAt (encodeKv base blocks stride cls).fourRows
      x.val row.val b.val).bind fun s =>
        ((box base blocks stride cls dst oy rows).globalAddress s).bind
          (fun a => some (Loc.mk .global 0 a))) = _
    rw [slotAt, Option.bind_some, ha]
    rfl
  exact tensor_writeByte_of_initial hX ho hi hl hw hm hn

private theorem cacheByte_lt {r blocks stride : Nat} (x : Fin 144) (b : Fin 4)
    (hrow : r < blocks * (stride / 528)) (hx : x.val < 132) :
    r * 528 + 4 * x.val + b.val < cacheBytes blocks stride := by
  have hd := Nat.div_mul_le_self stride 528
  have hm := Nat.mul_le_mul_left blocks hd
  unfold cacheBytes
  rw [← Nat.mul_assoc] at hm
  omega

section
variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} (hpre : Pre P L mem0)
    (hs : GlobalWrites.SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hs hX

/-- Neither output tensor can replace a source byte of a gather. -/
theorem cacheByte_noWrite {base blocks stride r : Nat} (x : Fin 144) (b : Fin 4)
    (hrow : r < blocks * (stride / 528)) (hx : x.val < 132)
    (ho : base + cacheBytes blocks stride ≤ P.outBase ∨ P.outBase + tensorBytes P ≤ base)
    (hl : base + cacheBytes blocks stride ≤ P.lseBase ∨ P.lseBase + lseBytes P ≤ base) :
    ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ⟨.global, 0, base + r * 528 + 4 * x.val + b.val⟩ := by
  have hr := cacheByte_lt x b hrow hx
  intro w a bytes hw hc
  rcases actual_global_write_range hpre hs hX hw hc rfl with hos | hls
  · rcases ho <;> dsimp only at hos <;> omega
  · rcases hl <;> dsimp only at hls <;> omega

/-- An observed main-cache gather write contains the matching byte of the logical raw row. -/
theorem writeByte_main {i : EvId} {o : TensorCopy.Observation} {address : Nat} {dst : Loc}
    {oy : Int} {rows : Fin 4 → Int} (ho : X.tensor i = some o) (hi : X.TensorIssue i address o.spec)
    (hb : o.spec.toTensorBox = box P.kvBase P.numBlocks P.blockStride P.kvClass dst oy rows)
    (row : Fin 4) (x : Fin 144) (b : Fin 4) {value : Byte} {r : Nat} (hr : rows row = r)
    (hrow : r < P.numBlocks * (P.blockStride / 528)) (hx : x.val < 132)
    (hw : TensorCopy.writeByte o x.val row.val b.val = some value) :
    value = (.bits 8 (BitVec.ofNat 64 (P.kvByte r (4 * x.val + b.val))), 0) := by
  have hm := hpre.kvInput r hrow (4 * x.val + b.val) (by omega)
  have hmem : mem0 ⟨.global, 0, P.kvBase + r * 528 + (4 * x.val + b.val)⟩ =
      some (some (.bits 8 (BitVec.ofNat 64 (P.kvByte r (4 * x.val + b.val))), 0)) := by
    simpa only [Nat.add_assoc] using hm
  refine writeByte_of_initial hX ho hi hb row x b hr hrow hx hw ?_ ?_
  · simpa only [Nat.add_assoc] using hmem
  · exact cacheByte_noWrite hpre hs hX x b hrow hx hpre.kvApartO hpre.kvApartLse

/-- An observed extra-cache gather write contains the matching byte of the logical raw row. -/
theorem writeByte_extra {i : EvId} {o : TensorCopy.Observation} {address : Nat} {dst : Loc}
    {oy : Int} {rows : Fin 4 → Int} (ho : X.tensor i = some o) (hi : X.TensorIssue i address o.spec)
    (hb : o.spec.toTensorBox =
      box P.extraKvBase P.extraNumBlocks P.extraBlockStride P.extraKvClass dst oy rows)
    (hne : P.extra_topk ≠ 0) (row : Fin 4) (x : Fin 144) (b : Fin 4) {value : Byte} {r : Nat}
    (hr : rows row = r) (hrow : r < P.extraNumBlocks * (P.extraBlockStride / 528))
    (hx : x.val < 132) (hw : TensorCopy.writeByte o x.val row.val b.val = some value) :
    value = (.bits 8 (BitVec.ofNat 64 (P.extraKvByte r (4 * x.val + b.val))), 0) := by
  have hmem := hpre.extraKvInput r hrow (4 * x.val + b.val) (by omega)
  refine writeByte_of_initial hX ho hi hb row x b hr hrow hx hw ?_ ?_
  · simpa only [Nat.add_assoc] using hmem
  · exact cacheByte_noWrite hpre hs hX x b hrow hx
      (hpre.extraKvApartO.resolve_left hne) (hpre.extraKvApartLse.resolve_left hne)
end

/-- An observed gather write for an invalid sparse index is the typed zero-fill byte. -/
theorem writeByte_invalid {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {o : TensorCopy.Observation} {base blocks stride : Nat}
    {cls : TensorDescriptor.AllocationClass} {dst : Loc} {oy : Int} {rows : Fin 4 → Int}
    (ho : X.tensor i = some o)
    (hb : o.spec.toTensorBox = box base blocks stride cls dst oy rows)
    (row : Fin 4) (x : Fin 144) (b : Fin 4) {value : Byte}
    (hr : rows row = -1) (hw : TensorCopy.writeByte o x.val row.val b.val = some value) :
    value = (.bits 32 0, b.val) := by
  have haddr := invalidAddress (base := base) (blocks := blocks) (stride := stride)
    (cls := cls) dst oy rows row x b hr
  have hslot : ∃ s : TensorTransfer.Slot o.spec.descriptor,
      TensorTransfer.slotAt o.spec.descriptor x.val row.val b.val = some s ∧
      TensorCopy.source o.spec s = .fill .zero .u32 b.val := by
    change ∃ s : TensorTransfer.Slot o.spec.toTensorBox.descriptor,
      TensorTransfer.slotAt o.spec.toTensorBox.descriptor x.val row.val b.val = some s ∧
      (match o.spec.toTensorBox.globalAddress s with
      | some a => TensorTransfer.Source.global a
      | none =>
        .fill o.spec.toTensorBox.descriptor.fill o.spec.toTensorBox.descriptor.format s.2.2.val)
        = .fill .zero .u32 b.val
    rw [hb]
    refine ⟨slot base blocks stride cls row x b, slotAt base blocks stride cls row x b, ?_⟩
    rw [haddr]
    rfl
  obtain ⟨s, hslot, hsrc⟩ := hslot
  simp only [TensorCopy.writeByte, hslot, Option.bind_some] at hw
  cases hwrite : o.effects.write s with
  | none =>
    simp [hwrite] at hw
  | some content =>
    have hcont := (hX.tensor _ _ ho).2.1.writes s content hwrite
    rw [hsrc] at hcont
    have hct : content = .filled .zero .u32 b.val := hcont
    rw [hwrite, hct] at hw
    exact (Option.some.inj hw).symm

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.RawGather
