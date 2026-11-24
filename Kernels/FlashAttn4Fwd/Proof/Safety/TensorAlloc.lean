-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Async
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # `TensorAllocationUnsafe`: every tensor transfer stays inside its map

The allocation class of a map matters only for a transfer that selects an element outside the
tensor (ERR-TENSOR-LARGE-OOB). No transfer of the kernel does, whatever the maps' classes:

* **Loads.** A copy is `copySpec` of its loader's earlier copies on its ring barrier
  (`RingCopies.copy`), for an item its loader started (`AsyncFacts.copy_started`), whose
  coordinates (batch, head, query block) are in range (`CoordsInRange`, the schedule's
  `coords_eq` and `coords_lt`). Its box (64 head-dimension columns by 128 rows of Q or V, by 64
  rows of K; one head, one batch) starts at column 0 or 64 and at a row that leaves room for it:
  `seqlen_q` is a multiple of 512 and `seqlen_k` of 128 (`copy_in_bounds`, `tile_in_bounds`).
* **Stores.** The epilogue's boxes are inside the O map (`AsyncFacts.store_bounds`).
* **Prefetches.** The kernel issues none (`AsyncFacts.no_prefetch`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof TensorDescriptor

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The coordinates the code computes for a work item below the item count are in range (from
the schedule protocol: `Schedule.coords_eq`, `Schedule.coords_lt`). -/
def CoordsInRange (P : Params) (L : Launch) : Prop :=
  ∀ {w : Nat}, w < totOf L →
    (coordsOf L w).1 < P.b ∧ (coordsOf L w).2.1 < P.h ∧ (coordsOf L w).2.2 < P.blocks

/-- Every element of a box of a kernel map whose origin leaves room for it is inside the
tensor. -/
theorem tile_in_bounds {base rows heads batch boxRows : Nat} {fill : Fill}
    {cls : AllocationClass} {x0 y0 hd bt : Nat} (hx : x0 + 64 ≤ 128) (hy : y0 + boxRows ≤ rows)
    (hh : hd < heads) (hb : bt < batch) :
    ¬ TensorHasOob (FlashAttn4Fwd.encodeTiled base rows heads batch boxRows fill cls)
      ![(x0 : Int), (y0 : Int), (hd : Int), (bt : Int)] none := by
  rintro ⟨slot, hn⟩
  apply hn
  have hcol : slot.1.val < 64 := by
    simp [FlashAttn4Fwd.encodeTiled, TensorTile.count, TensorTile.step]
  have hrow : slot.2.1.val < boxRows := by
    simpa [FlashAttn4Fwd.encodeTiled, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step] using slot.2.1.isLt
  have hidx : TensorTransfer.index slot =
      ![slot.1.val, slot.2.1.val % boxRows, 0, slot.2.1.val / boxRows] := by
    funext axis
    fin_cases axis <;>
      simp [TensorTransfer.index, TensorTile.indexOf, TensorTile.unflatten, TensorTile.count,
        TensorTile.step, FlashAttn4Fwd.encodeTiled] <;>
      first | rfl | exact Nat.mod_one _
  have hq : slot.2.1.val / boxRows = 0 := Nat.div_eq_of_lt hrow
  intro axis
  simp only [TensorTransfer.coord, hidx]
  fin_cases axis <;>
    simp [geometry, FlashAttn4Fwd.encodeTiled, TensorTile.coord, TensorTile.step, hq,
      Nat.mod_eq_of_lt hrow] <;> omega

/-- The KV blocks of an item are `seqlen_k / 128`. -/
theorem kvBlocks_eq (hpre : Pre P L mem0) : 128 * kvBlocks P = P.sk := by
  have := hpre.skDiv128
  unfold kvBlocks
  omega

/-- The query blocks of a head are `seqlen_q / 512`. -/
theorem blocks_eq (hpre : Pre P L mem0) : 512 * P.blocks = P.sq := by
  have := hpre.sqDiv512
  unfold Params.blocks
  omega

/-- **A copy of a started item stays inside its map.** -/
theorem copy_in_bounds (hpre : Pre P L mem0) (hco : CoordsInRange P L) {g : Nat} {b : FBar}
    (hb : b.isFull) (cnt : Nat) (hw : workOf L g (useItem P b (cnt / b.copies)) < totOf L) :
    ¬ TensorHasOob (copySpec P L g b cnt).descriptor (copySpec P L g b cnt).origin
      (copySpec P L g b cnt).rows := by
  obtain ⟨h1, h2, h3⟩ := hco hw
  have hr : ctaOf L g % 2 < 2 := Nat.mod_lt _ (by decide)
  have hsk := kvBlocks_eq hpre
  have hsq := blocks_eq hpre
  have hskp := hpre.skPos
  cases b with
  | qFull st =>
    have hj : cnt % 2 < 2 := Nat.mod_lt _ (by decide)
    have hst := st.isLt
    simp only [copySpec, copyMap, copyOrigin, FBar.copies] at h1 h2 h3 ⊢
    exact tile_in_bounds (by omega) (by omega) h2 h1
  | kvFull s =>
    by_cases hs : s.val % 2 = 0
    · have hj : cnt % 2 < 2 := Nat.mod_lt _ (by decide)
      simp only [copySpec, copyMap, copyOrigin, FBar.copies, hs, ↓reduceIte] at h1 h2 h3 ⊢
      refine tile_in_bounds (by omega) ?_ h2 h1
      simp only [useBlock]
      omega
    · simp only [copySpec, copyMap, copyOrigin, FBar.copies, hs, ↓reduceIte] at h1 h2 h3 ⊢
      refine tile_in_bounds (by omega) ?_ h2 h1
      simp only [useBlock]
      omega
  | _ => cases hb

/-- **Every tensor load of the kernel stays inside its map.** -/
theorem load_in_bounds (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (hcp : RingCopies P L X) (ha : AsyncFacts P L X)
    (hco : CoordsInRange P L) {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue a sp⟩) :
    ¬ TensorHasOob sp.descriptor sp.origin sp.rows := by
  obtain ⟨g, k⟩ := i
  have hg := Frame.lt_of_get hX he
  obtain ⟨b, c, hring, hm⟩ := ha.copy_ring he
  have hfull := (hr.issue hg he hm hring).1
  have hsp := hcp.copy hg he hm hfull
  have hw := ha.copy_started hg he hm hfull
  subst hsp
  exact copy_in_bounds hpre hco hfull _ hw

/-- **No tensor transfer is out of bounds of a large-allocation map.** -/
theorem no_tensorAllocationUnsafe (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (hcp : RingCopies P L X) (ha : AsyncFacts P L X)
    (hco : CoordsInRange P L) : ¬ TensorAllocationUnsafe L mem0 X := by
  rintro ⟨i, ⟨a, s, ⟨pc, he⟩, -, hoob, -⟩ | ⟨a, s, hi, -, hoob, -⟩ | ⟨a, s, ⟨pc, he⟩, -⟩⟩
  · exact load_in_bounds hpre hX hr hcp ha hco he hoob
  · exact ha.store_bounds hi hoob
  · exact ha.no_prefetch he

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
