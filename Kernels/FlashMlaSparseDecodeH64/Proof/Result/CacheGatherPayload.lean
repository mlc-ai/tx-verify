-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.CacheGatherCoordinates
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawGatherTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaCoordinateRef

@[expose] public section

/-! # The actual gather4 writes the selected raw row bytes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.RawGather

open PTX PTX.Flow Wg1Tma

private def fourRows (x : Σ n, TensorDescriptor.Descriptor n) :
    Σ n, TensorDescriptor.Descriptor n := ⟨x.1, x.2.fourRows⟩

/-- An observed gather byte is the logical cache byte chosen by the gather coordinate, or
the tensor map's typed zero fill for an invalid sparse slot. -/
theorem gathered_byte {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i address : Nat} {o : TensorCopy.Observation} {d : D} {k : Fin 16}
    {value : Byte} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hSite : d.site = .issue k)
    (ho : X.tensor (g, i) = some o) (hi : X.TensorIssue (g, i) address o.spec)
    (row : Fin 4) (col : Fin 144) (byte : Fin 4)
    (hCol : col.val < 132)
    (hw : TensorCopy.writeByte o col.val row.val byte.val = some value) :
    let pos := coordPos k.val row.val
    let extra := FlashMlaSparseDecodeH64.isExtraBlock d.block (P.topkLen (eOf L g))
    let slot := slotPos (P.topkLen (eOf L g)) d.block (pos / 2) (pos % 2)
    value = if validBit P L g d.block (pos / 2) (pos % 2) then
      (.bits 8 (BitVec.ofNat 64 (rowBytes P (eOf L g) (qOf L g) extra slot
        (4 * col.val + byte.val))), 0)
    else (.bits 32 0, byte.val) := by
  intro pos extra slot
  obtain ⟨tag, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  have hQuery : qOf L g < P.s_q := Wg1Mma.queryOf_lt hpre hg
  obtain ⟨hinv, ⟨desc, hDescBind, hDescEq⟩, hfirst, hcoord⟩ :=
    RawGatherTrace.gather_coordinates hpre hs hX hState hSite he rfl
      (TmaCoordinateRef.issue_words hpre hX hs hState hSite)
  have hBlock' : d.block <
      FlashMlaSparseDecodeH64.totalBlocks d.len0 d.len1 := by
    rcases hinv.block_le with hb | hb | hb
    · rw [hSite] at hb
      cases hb
    · rw [hSite] at hb
      cases hb
    · exact hb
  rw [hinv.len0, hinv.len1] at hBlock'
  obtain ⟨_, _, _, _, _, hDesc⟩ :=
    RawGatherTrace.gather_operands hpre hs hX hState hSite he rfl
  let rWords (r : Fin 4) := (BitVec.ofNat 32 (coordAt P L g d.block (coordPos k.val r.val))).toInt
  cases hv : validBit P L g d.block (pos / 2) (pos % 2)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hRow : rWords row = -1 := coord_signed_invalid hv
    rcases hDesc with hMain | ⟨_, hExtra⟩
    · obtain ⟨y, hb⟩ := canonicalBox (s := o.spec.toTensorBox) hMain hfirst hcoord
      exact writeByte_invalid hX ho hb row col byte hRow hw
    · obtain ⟨y, hb⟩ := canonicalBox (s := o.spec.toTensorBox) hExtra hfirst hcoord
      exact writeByte_invalid hX ho hb row col byte hRow hw
  · simp only [↓reduceIte]
    have hselected := coord_valid_slot hv
    by_cases hMain : d.block < FlashMlaSparseDecodeH64.numOrigBlocks d.len0
    · have hExtra' :
          FlashMlaSparseDecodeH64.isExtraBlock d.block (P.topkLen (eOf L g)) = false := by
        unfold FlashMlaSparseDecodeH64.isExtraBlock
        rw [← hinv.len0]
        exact decide_eq_false (by omega)
      rw [Wg1Tma.kvOff, ite_eq_left hMain, hpre.mapKVBind] at hDescBind
      have hD : (⟨o.spec.outer, o.spec.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
          ⟨1, (encodeKv P.kvBase P.numBlocks P.blockStride P.kvClass).fourRows⟩ := by
        rw [hDescEq]
        exact congrArg fourRows (Option.some.inj hDescBind).symm
      obtain ⟨oy, hb⟩ := canonicalBox (s := o.spec.toTensorBox) hD hfirst hcoord
      obtain ⟨hr, hlt⟩ := coord_signed_main hpre hinv.batch hQuery hBlock' hExtra' hv
      have hByte := writeByte_main hpre hs hX ho ⟨tag, he⟩ hb row col byte hr hlt hCol hw
      simpa [extra, hExtra', rowBytes] using hByte
    · have hExtra' :
          FlashMlaSparseDecodeH64.isExtraBlock d.block (P.topkLen (eOf L g)) = true := by
        unfold FlashMlaSparseDecodeH64.isExtraBlock
        rw [← hinv.len0]
        exact decide_eq_true (by omega)
      have hPositive : P.extra_topk ≠ 0 := by
        rw [hExtra'] at hselected
        have hLen : slot < P.extraTopkLen (eOf L g) := hselected.1
        have := Wg1Tma.extraLen_le hpre hinv.batch
        omega
      rw [Wg1Tma.kvOff, ite_eq_right hMain, hpre.mapExtraKvBind.resolve_left hPositive] at hDescBind
      have hD : (⟨o.spec.outer, o.spec.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
          ⟨1, (encodeKv P.extraKvBase P.extraNumBlocks P.extraBlockStride
            P.extraKvClass).fourRows⟩ := by
        rw [hDescEq]
        exact congrArg fourRows (Option.some.inj hDescBind).symm
      obtain ⟨oy, hb⟩ := canonicalBox (s := o.spec.toTensorBox) hD hfirst hcoord
      obtain ⟨hr, hlt⟩ := coord_signed_extra hpre hinv.batch hQuery hBlock' hExtra' hv
      have hByte := writeByte_extra hpre hs hX ho ⟨tag, he⟩ hb hPositive row col byte
        hr hlt hCol hw
      simpa [extra, hExtra', rowBytes] using hByte

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.RawGather
