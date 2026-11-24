-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
import Lemmas.Flow.NotBulk
import Lemmas.Flow.NotBulkPrefetch
import Lemmas.Flow.NotMatrix
import Lemmas.Flow.NotRmw
import Lemmas.Flow.OpPcsFast

public section

/-! # Write forms absent from the frozen sparse-decode kernel -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.GlobalWrites
open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Soundness of the executed thread machines for this launch. -/
abbrev SoundThreads (P : Params) (L : Launch) : Prop :=
  ∀ g < L.threads, (Machine.code P L g).Sound

set_option maxRecDepth 100000 in
private theorem no_instructions :
    OpPcsFast kernel.code (fun op => atomicOp op || bulkOp op || clcOp op) [] = true := by
  decide +kernel

variable (hX : Consistent L kernel Assumptions.all mem0 X)
include hX

private theorem excluded_event {i : EvId} {e : Event} {p : Op → Bool} (he : X.get i = some e)
    (hub : ∀ f, e.kind ≠ .ub f)
    (hfire : ∀ t (ins : Instr) o s, Fires s (eventTmpl Assumptions.all L i.1 t ins.op) e o →
      p ins.op = true) (himpl : ∀ op, p op = true → (atomicOp op || bulkOp op || clcOp op) = true)
    : False := by
  rcases Flow.get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · exact hub f hf
  · exact List.not_mem_nil (OpPcsFast.mem no_instructions hc (himpl _ (hfire t ins o _ hf)))

/-- The instruction stream contains no linear copy. -/
theorem no_copy {i : EvId} {s : AsyncCopy.Spec} (hc : X.Copy i s) : False := by
  obtain ⟨site, he⟩ := hc
  exact excluded_event hX (p := bulkOp) he (by simp)
    (fun _ _ _ _ hf => fires_bulk_op hf rfl) (by simp +contextual)

omit hX in
set_option maxRecDepth 100000 in
private theorem no_bulk_prefetch_site : OpPcsFast kernel.code bulkPrefetchOp [] = true := by
  decide +kernel

/-- The instruction stream contains no linear prefetch. -/
theorem no_bulk_prefetch {i : EvId} {a : Acc} (hi : X.BulkPrefetch i a) : False := by
  obtain ⟨_, he⟩ := hi
  rcases PTX.Flow.get_source hX he with ⟨_, h⟩ | ⟨_, _, _, _, hc, hf⟩
  · cases h
  · exact List.not_mem_nil (OpPcsFast.mem no_bulk_prefetch_site hc (fires_bulkPrefetch_op hf rfl))

/-- The instruction stream contains no cancellation request. -/
theorem no_clc {i : EvId} {s : Clc.Spec} {tg : List Nat} (hc : X.ClcIssue i s tg) : False := by
  obtain ⟨site, he⟩ := hc
  exact excluded_event hX (p := clcOp) he (by simp)
    (fun _ _ _ _ hf => fires_clcIssue_op hf rfl) (by simp +contextual)

/-- The instruction stream contains no atomic read-modify-write. -/
theorem no_rmw {i : EvId} {a : Acc} {old : List (Option Byte)} {new : Option (List Byte)}
    (hc : X.Rmw i a old new) : False := by
  obtain ⟨site, he⟩ := hc
  exact excluded_event hX (p := atomicOp) he (by simp)
    (fun _ _ _ _ hf => fires_rmw_op hf rfl) (by simp +contextual)

omit hX in
set_option maxRecDepth 100000 in
private theorem no_matrix_instruction :
    kernel.code.all (fun ins => !matrixOp ins.op) = true := by
  decide +kernel

/-- Frozen sparse decode uses Tensor Core operations and has no warp matrix event. -/
theorem no_matrix {i : EvId} {e : Event} (he : X.get i = some e) : isMatrix e = false :=
  no_matrix_of_code hX no_matrix_instruction he

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.GlobalWrites
