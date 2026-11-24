-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmQuery
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.OutputGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
public import Lemmas.Kernel.Frame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputTrace

@[expose] public section

/-! # Tensor copy bounds and store form -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Result Wg0 MmaDataTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem in_bounds_of_addresses (s : TensorBox)
    (hAddr : ∀ slot, (s.globalAddress slot).isSome = true) :
    ¬ TensorHasOob s.descriptor s.origin s.rows := by
  rintro ⟨slot, hOob⟩
  have h := hAddr slot
  unfold TensorBox.globalAddress TensorTransfer.globalAddress TensorAddress.lookup at h
  simp at h
  exact hOob h.1

/-- Every byte of every actual Q tile is indexed inside the Q descriptor. -/
theorem query_no_oob (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) (tile : Fin 8) :
    let s := queryTmaSpec P L g tile
    ¬ TensorHasOob s.descriptor s.origin s.rows := by
  refine in_bounds_of_addresses (queryTmaSpec P L g tile).toTensorBox ?_
  intro slot
  have ⟨hx, hh, hb⟩ := queryTile_shape P L g tile
  let x : Fin 64 := ⟨slot.1.val, hx ▸ slot.1.isLt⟩
  let h : Fin 64 := ⟨slot.2.1.val, hh ▸ slot.2.1.isLt⟩
  let b : Fin 2 := ⟨slot.2.2.val, hb ▸ slot.2.2.isLt⟩
  have hs : queryTileSlot P L g tile x h b = slot := by
    rcases slot with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
    rfl
  rw [← hs, queryTile_global hpre hg]
  rfl

/-- An elected output warp stays inside the O descriptor in each tile. -/
theorem output_no_oob {g : Nat} (hw : warpOf L g < 2) (hq : qOf L g < P.s_q)
    (he : eOf L g < P.b) (j : Fin 4) :
    let s := outputSpec P L g j
    ¬ TensorHasOob s.descriptor s.origin s.rows := by
  refine in_bounds_of_addresses (outputSpec P L g j).toTensorBox ?_
  intro slot
  have ⟨hx, hh, hb⟩ := outputShape P L g j
  let s : OutputSlot := ⟨⟨slot.1.val, hx ▸ slot.1.isLt⟩,
    ⟨slot.2.1.val, hh ▸ slot.2.1.isLt⟩, ⟨slot.2.2.val, hb ▸ slot.2.2.isLt⟩⟩
  have hs : tensorOutputSlot P L g j s = slot := by
    rcases slot with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩
    rfl
  rw [← hs, outputSlot_global P L g j s hw hq he]
  rfl

/-- The actual output effects use the plain store form, and there are no linear reductions. -/
theorem no_tensor_store_unsafe (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X) : ¬ TensorStoreUnsafe Assumptions.all X := by
  rintro (⟨i, o, red, x, y, ho, hr, _, _⟩ | h)
  · obtain ⟨a, hIssue⟩ := (hX.store i o ho).1
    obtain ⟨d, j, hd, hSite⟩ := GlobalWrites.outputTile_site hs hX ht hIssue
    have hg := Frame.lt_of_get hX hIssue.choose_spec
    have hSpec := (Wg0OutputTrace.tileSpec hpre hX (hs i.1 hg).machine hIssue hd hSite).2
    rw [hSpec] at hr
    cases hr
  · exact TensorStore.not_copyReduceNoRule_of_none
      (fun _ _ hc _ => (GlobalWrites.no_copy hX hc).elim) h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
