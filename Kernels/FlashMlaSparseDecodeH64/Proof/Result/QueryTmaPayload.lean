-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmQuery
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GlobalFrame
import Lemmas.Tensor.TensorReadSources
import Lemmas.Tensor.TensorCompleteConsistentRead

@[expose] public section

/-! # The actual Q TMA payload comes from the immutable launch tensor -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow AsyncCopy MmaDataTrace Wg1Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem query_address_range {g : Nat}
    (hpre : Pre P L mem0) (hg : g < L.threads) (tile : Fin 8) (x h : Fin 64) (b : Fin 2) :
    let addr := P.qBase + 2 * (((batchOf L g * P.s_q + queryOf L g) * 64 + h.val) * 512 +
      qCoord tile + x.val) + b.val
    P.qBase ≤ addr ∧ addr < P.qBase + tensorBytes P := by
  have hBatch := batchOf_lt hpre hg
  have hQuery := queryOf_lt hpre hg
  have hRow := Nat.mul_le_mul_right P.s_q (Nat.succ_le_of_lt hBatch)
  rw [Nat.succ_mul] at hRow
  have hFeature : qCoord tile + x.val < 512 := by dsimp [qCoord]; omega
  have hTotal : tensorBytes P = 65536 * (P.b * P.s_q) := by unfold tensorBytes; ring
  dsimp only
  rw [hTotal]
  have hHead := h.isLt
  have hByte := b.isLt
  omega

/-- A performed byte of an actual Q tile has the logical query value at its source coordinate. -/
theorem query_tile_write_byte {g i address : Nat} {a : Acc} {data : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (tile : Fin 8) (x h : Fin 64) (b : Fin 2)
    (hi : X.TensorIssue (g, i) address (queryTmaSpec P L g tile))
    (hw : X.MemWrites (.async (g, i) (.write (.load x.val h.val b.val))) a data) :
    data = [(.float .bf16 (P.q (batchOf L g) (queryOf L g) h.val (qCoord tile + x.val)),
      b.val)] := by
  obtain ⟨o, address', value, ho, hi', _, hv, _, rfl, _⟩ := hw
  have hg := Frame.lt_of_get hX hi.choose_spec
  have hSpec := (Kind.tensorIssue.inj
    (congrArg Event.kind (Option.some.inj (hi'.choose_spec.symm.trans hi.choose_spec)))).2
  let addr := P.qBase + 2 * (((batchOf L g * P.s_q + queryOf L g) * 64 + h.val) * 512 +
    qCoord tile + x.val) + b.val
  let loc : Loc := ⟨.global, 0, addr⟩
  let byte : Byte :=
    (.float .bf16 (P.q (batchOf L g) (queryOf L g) h.val (qCoord tile + x.val)), b.val)
  have hGlobal := queryTile_global hpre hg tile x h b
  have hSlot : TensorTransfer.slotAt (queryTmaSpec P L g tile).descriptor x.val h.val b.val =
      some (queryTileSlot P L g tile x h b) :=
    TensorCopy.slotAt_self (queryTileSlot P L g tile x h b)
  have hRead : TensorCopy.readLoc o.spec x.val h.val b.val = some loc := by
    rw [hSpec, TensorCopy.readLoc_source, hSlot]
    simp only [Option.bind_some, TensorCopy.source, hGlobal]
    rfl
  obtain ⟨src, hsAddr, hm⟩ := queryTile_initial hpre hg tile x h b
  have hSrc : src = addr := by
    simp only [TensorCopy.source, hGlobal] at hsAddr
    exact (TensorTransfer.Source.global.inj hsAddr).symm
  have hMem : mem0 loc = some (some byte) := by
    rw [hSrc] at hm
    exact hm
  have hRange : P.qBase ≤ addr ∧ addr < P.qBase + tensorBytes P :=
    query_address_range hpre hg tile x h b
  have hNo w dst bs (hWrite : X.MemWrites w dst bs) : ¬ dst.Covers loc := by
    intro hc
    rcases actual_global_write_range hpre hs hX hWrite hc rfl with ho | hl
    · rcases hpre.qApartO with hApart | hApart <;>
        change _ ≤ addr ∧ addr < _ at ho <;> omega
    · rcases hpre.inputApartLse with hApart | hApart <;>
        change _ ≤ addr ∧ addr < _ at hl <;> omega
  exact congrArg (fun v => [v]) (tensor_writeByte_of_initial hX ho hi' hRead hv hMem hNo)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
