-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsRead
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocal
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasRead
import Kernels.TmlFa4Fwd.Proof.GlobalWrites
import Lemmas.Flow.NotNc

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow

/-- An ordinary read of the shared TMEM allocation result by the MMA role. -/
def AllocationResultRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨1911, .rd a bytes⟩

/-- The softmax role's ordinary read of a Bias vector element. -/
def BiasVectorRead (X : Execution) (i : EvId) (repeated : Bool) (vector : Fin 16)
    (a : Acc) (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨Softmax.biasReadPc repeated vector, .rd a bytes⟩

private def biasSites (repeated : Bool) : List Nat :=
  List.ofFn fun i : Fin 16 => Softmax.biasReadPc repeated i

private def statsObservations : List (Fin 2 × Correction.StatsKind) :=
  [(0, .alpha), (1, .alpha), (0, .sum), (0, .maximum), (1, .sum), (1, .maximum)]

private def statsSites : List Nat :=
  statsObservations.map fun (stage, kind) => Correction.statsPc stage kind

private theorem sharedReadSitesAudit :
    OpPcsFast kernel.code (fun op => loadSpace op == some .shared)
      ([1911] ++ biasSites false ++ biasSites true ++ statsSites) = true := by
  decide +kernel

/-- The allocator result, Bias vectors and correction statistics account for all
ordinary shared-memory reads. -/
theorem sharedReadObservation {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {a : Acc}
    {bytes : List (Option Byte)} (he : X.Reads i a bytes) (hShared : a.loc.space = .shared) :
    AllocationResultRead X i a bytes ∨
      (∃ repeated vector, BiasVectorRead X i repeated vector a bytes) ∨
      ∃ stage kind, Correction.StatisticsRead X i stage kind a bytes := by
  obtain ⟨site, ins, he, hc, hSpace, _⟩ := Loader.sharedReadInstruction hX he hShared
  have hSites := OpPcsFast.mem sharedReadSitesAudit hc (by simp only [hSpace, beq_self_eq_true])
  have fromBias {repeated : Bool} (h : site ∈ biasSites repeated) :
      ∃ repeated vector, BiasVectorRead X i repeated vector a bytes := by
    obtain ⟨vector, rfl⟩ := List.mem_ofFn.mp h
    exact ⟨repeated, vector, he⟩
  simp only [List.mem_append, List.mem_singleton] at hSites
  rcases hSites with (((rfl | h) | h) | h)
  · exact .inl he
  · exact .inr (.inl (fromBias h))
  · exact .inr (.inl (fromBias h))
  · obtain ⟨⟨stage, kind⟩, _, rfl⟩ := List.mem_map.mp h
    exact .inr (.inr ⟨stage, kind, he⟩)

/-- The assumptions of the frozen kernel enable no non-coherent load. -/
theorem noNoncoherentRead {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {a : Acc}
    {bytes : List (Option Byte)} (hRead : X.NcReads i a bytes) : False := by
  obtain ⟨_, he⟩ := hRead
  rcases get_source hX he with ⟨_, hf⟩ | ⟨t, _, _, _, _, hf⟩
  · cases hf
  exact fires_not_nc (show Assumptions.all.any (·.ncLoads t.pc) = false from rfl) hf rfl

end PTX.Kernels.TmlFa4Fwd.Thread
