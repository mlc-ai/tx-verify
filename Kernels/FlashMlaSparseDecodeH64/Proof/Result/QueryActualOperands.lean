-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.QueryCopyPayload
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmSums
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryOperandLifetime

@[expose] public section

/-! # The actual QK A operand contains the specified query values -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow AsyncCopy MmaDataTrace Wg1Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An actual QK issue observes the query row for the given head and contraction half. -/
theorem qk_query_operand {g j : Nat} {d : Wg1Mma.D} {issue : Fin 16}
    {ops : MmaOperands}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (hi : X.MmaIssue (g, j) tmemP (qkOperands L g d.i issue) (qkAccum issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)))
    (hsite : d.site = .qkMma issue) (hops : X.async.mmaOperands (g, j) = some ops)
    (head : Fin 64) (col : Fin 128) :
    Bf16Operand ops.a (head.val + 64 * (col.val / 64)) fun k =>
      P.q (batchOf L g) (queryOf L g) head.val (qkDepthAt col issue.val k) := by
  obtain ⟨i, e, q, u, he, hq, hqsite, hf, hcopy, hdone, hread⟩ :=
    Protocol.QueryOperandLifetime.query_copy_read_source hpre hX hs hi hd hsite
  have hstarted := hX.tma.2.1.2 (g, i) hdone
  obtain ⟨copyOps, hcopyOps⟩ : ∃ copyOps, X.async.mmaOperands (g, i) = some copyOps := by
    cases hcopyOps : X.async.mmaOperands (g, i) with
    | none => simp [Snapshot.mmaStarted, hcopyOps] at hstarted
    | some obs => exact ⟨obs, rfl⟩
  have hhead := head.isLt
  have hcol := col.isLt
  let row : Fin 128 := ⟨head.val + 64 * (col.val / 64), by omega⟩
  have hmod : row.val % 64 = head.val := by dsimp [row]; omega
  have hdiv : row.val / 64 = col.val / 64 := by dsimp [row]; omega
  have hval := query_copy_payload hpre hX hs he hq hqsite hf hcopyOps row
  simpa only [row, hmod, hdiv, qkDepthAt] using
    queryA_from_copy hX hcopy hi hcopyOps hops hval (hread row)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
