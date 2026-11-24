-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Flow.NotBulk
import Lemmas.Flow.NotClc
import Lemmas.Flow.OpPcsFast

public section

/-! # Collective forms absent from the frozen kernel -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.StaticCollectiveEvents

open PTX PTX.Flow

variable {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 100000 in
private theorem cluster_sites : OpPcsFast kernel.code clusterOp [] = true := by
  decide +kernel

/-- No thread issues a cluster barrier arrival or wait. -/
theorem no_cluster (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {tag : Nat} {op : ClusterOp}
    (he : X.get i = some ⟨tag, .cluster op⟩) : False := by
  rcases PTX.Flow.get_source hX he with ⟨_, h⟩ | ⟨_, _, _, _, hc, hf⟩
  · cases h
  · exact List.not_mem_nil (OpPcsFast.mem cluster_sites hc (by rw [fires_cluster_op hf rfl]; rfl))

private def barArriveOp : Op → Bool
  | .barArrive .. => true
  | _ => false

set_option maxRecDepth 100000 in
private theorem bar_arrive_sites : OpPcsFast kernel.code barArriveOp [] = true := by
  decide +kernel

private theorem sync_template {g tag id : Nat} {count : Option Nat} {t : TState}
    {o : Option TState} {operand : Opnd} {n : Option Opnd}
    (hf : Fires tag (barTmpl L g t operand n .sync) ⟨tag, .bar id count .arrive⟩ o) : False := by
  unfold barTmpl at hf
  repeat' (first | split at hf | cases hf.1)

/-- All named-barrier events are synchronization operations. -/
theorem no_bar_arrive (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {tag id : Nat} {count : Option Nat}
    (he : X.get i = some ⟨tag, .bar id count .arrive⟩) : False := by
  rcases PTX.Flow.get_source hX he with ⟨_, h⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases h
  have hBar := fires_bar_op hf rfl
  have hArrive : barArriveOp ins.op = false := by
    cases hb : barArriveOp ins.op
    · rfl
    · exact (List.not_mem_nil (OpPcsFast.mem bar_arrive_sites hc hb)).elim
  cases hop : ins.op <;> simp only [hop, barOp, barArriveOp, Bool.false_eq_true] at hBar hArrive
  all_goals try contradiction
  all_goals rw [hop, eventTmpl] at hf
  all_goals exact sync_template hf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.StaticCollectiveEvents
