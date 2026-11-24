-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.NamedBarriers
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasBarrierProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX Thread Prologue Epilogue

/-- A Bias wait can release as soon as the four softmax warps have arrived at its generation. -/
theorem synchronizationFrontier {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g : Nat} (hg : g < l.threads) (stage : Fin 2)
    (hWait : BarrierArrival X (g,(X.tr g).length - 1) (11 + stage.val) (some 128) .sync) :
    (∃ lane < l.block, lane / 32 ∈ biasParticipants stage ∧
      (X.tr (g / l.block * l.block + lane)).countP (Execution.isBarId (11 + stage.val)) ≤
        observedBarrierOrdinal X (g,(X.tr g).length - 1) (11 + stage.val)) ∨
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Step.Released l Y g := by
  classical
  by_cases hArrivals : ∀ lane < l.block, lane / 32 ∈ biasParticipants stage →
      observedBarrierOrdinal X (g,(X.tr g).length - 1) (11 + stage.val) <
        (X.tr (g / l.block * l.block + lane)).countP (Execution.isBarId (11 + stage.val))
  · right
    refine releaseSynchronization hMax (fun Y hY _ hWrites => ?_) hg (biasBarrierShape hp stage)
      (biasBarrierSources hp hMax.1 stage) hWait hArrivals
    exact noActualNamedBarrierFault hp hY (fun i hi k hk ref a bytes hWrite =>
      hCuQ i hi k hk ref a bytes (hWrites ▸ hWrite))
  · left
    push Not at hArrivals
    exact hArrivals

/-- At the first Bias generation of a working CTA, any participant that still owes an arrival
has not exited. Reaching all arrivals releases the synchronization. -/
theorem firstSynchronizationFrontier {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g : Nat} (hg : g < l.threads) (stage : Fin 2)
    (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hWait : BarrierArrival X (g,(X.tr g).length - 1) (11 + stage.val) (some 128) .sync)
    (hFirst : observedBarrierOrdinal X (g,(X.tr g).length - 1) (11 + stage.val) = 0) :
    (∃ lane < l.block, lane / 32 ∈ biasParticipants stage ∧
      let peer := g / l.block * l.block + lane
      ¬ Exited X peer ∧ (X.tr peer).countP (Execution.isBarId (11 + stage.val)) = 0) ∨
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Step.Released l Y g := by
  rcases synchronizationFrontier hp hMax hCuQ hg stage hWait with hLag | hRelease
  · obtain ⟨lane, hLane, hMember, hCount⟩ := hLag
    rw [hFirst] at hCount
    have hMissing := Nat.eq_zero_of_le_zero hCount
    refine .inl ⟨lane, hLane, hMember, ?_, hMissing⟩
    intro hExit
    let peer := g / l.block * l.block + lane
    have hLaneCta := NamedBar.lane_cta (c := g/l.block)
      (NamedBar.block_pos_of_thread_lt hg) hLane
    have hWarp : warpIndex l peer ∈ biasParticipants stage := by
      unfold warpIndex
      rw [show peer % l.block = lane from hLaneCta.2]
      exact hMember
    obtain ⟨hSoftmax, hStage⟩ := (biasParticipantIff stage _).mp hWarp
    obtain ⟨j, hReached⟩ := firstBiasArrivalOfActiveExit hp hMax.1 hCuQ
      (hLaneCta.1.symm ▸ hWork) hSoftmax hExit
    rw [hStage] at hReached
    have hArrived := barrierArrivalExtent hReached
    exact (Nat.not_lt_zero _) (hMissing ▸ hArrived)
  · exact .inr hRelease

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
