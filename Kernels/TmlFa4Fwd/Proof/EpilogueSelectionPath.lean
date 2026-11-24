-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueSelectionObservations
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionPath
public import Lemmas.Flow.TauFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The zero relative index skips the exclusive-prefix shuffle and retains the initialized zero. -/
theorem selectFirstRequest (l : Launch) (g : Nat) {t : TState} {F : List (Nat × Value)}
    (ht : At t 2892 F) (hZero : (294, .pred true) ∈ F) :
    ∃ u, run kernel [] l g 1 t = some u ∧ At u 2896 F :=
  run_bra Flow.code_2892 true ht (holds_mem ht.2.2.2.2 hZero) (by simp)

/-- The nonzero relative index takes the fall-through and names the preceding lane. -/
theorem selectPreviousLane (l : Launch) (g : Nat) {t : TState} {F : List (Nat × Value)}
    {n : Nat} (hn : 0 < n) (hn32 : n < 32) (ht : At t 2892 F)
    (hNonzero : (294, .pred false) ∈ F) (hRelative : (1208, b32 n) ∈ F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ 2353) :
    ∃ u, run kernel [] l g 2 t = some u ∧ At u 2894 ((2353, b32 (n - 1)) :: F) := by
  obtain ⟨v, hVRun, hV⟩ :=
    run_bra (K := kernel) (A := []) (L := l) (g := g)
      Flow.code_2892 false ht (holds_mem ht.2.2.2.2 hNonzero) (by simp)
  obtain ⟨u, hRun, hU⟩ := previousPrefixIndex l g hn hn32 v
    (hV.mono ⟨holds_mem hV.2.2.2.2 hRelative, trivial⟩)
  have hKeep := schedulerOneStepFrame hV hU Flow.code_2893 hRun (fun pair hm => by
    simpa [writesRegs] using hFresh pair hm)
  exact ⟨u, run_comp hVRun hRun, hKeep⟩

/-- The decoded multiplication converts the exclusive tile prefix to the CTA work prefix. -/
theorem selectPreviousWork {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {t : TState} {F : List (Nat × Value)} {first batch : Nat}
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ 7225)
    (hHeads : (7138, b32 p.heads) ∈ F) :
    let sum := ∑ lane ∈ Finset.range (batch - first), groupLaneTiles p first lane
    At t 2895 ((2354, b32 sum) :: F) →
    ∃ u, run kernel [] l g 1 t = some u ∧ At u 2896 ((7225, b32 (sum * p.heads)) :: F) := by
  dsimp only
  intro ht
  let sum := ∑ lane ∈ Finset.range (batch - first), groupLaneTiles p first lane
  have hTotal := hp.prefixWork_signed (Nat.le_of_lt hBatch)
  have hPrev := precedingGroupWork p hFirst hBatch hGroup
  have hWork : sum * p.heads < 2 ^ 32 := by
    change tilePrefix p first * p.heads + sum * p.heads = _ at hPrev
    omega
  have hPositive : 0 < p.heads := by
    unfold Params.heads
    have := hp.shape.2.2.1
    omega
  have hSum := lt_of_le_of_lt (Nat.le_mul_of_pos_right sum hPositive) hWork
  have hh := lt_trans hp.heads_signed (by decide : 2 ^ 31 < 2 ^ 32)
  have hAt : At t 2895 [(2354, b32 sum), (7138, b32 p.heads)] :=
    ht.mono ⟨ht.2.2.2.2.1, holds_mem ht.2.2.2.2.2 hHeads, trivial⟩
  obtain ⟨u, hRun, hU⟩ := scalePreviousPrefix l g hSum hh hWork t hAt
  exact ⟨u, hRun, schedulerOneStepFrame (ht.mono ht.2.2.2.2.2) hU Flow.code_2895 hRun
    (fun pair hm => by simpa [writesRegs] using hFresh pair hm)⟩

/-- The scheduler's indexed exchange and its source lane's event at the same ordinal. -/
structure IndexedSchedulerShuffle (X : Execution) (l : Launch) (g pc index : Nat)
    (argument source : Value) where
  eventIndex : Nat
  peerEventIndex : Nat
  ordinal : Nat
  peerIndex : Nat
  recv : Value
  peerRecv : Value
  ok : Bool
  peerOk : Bool
  event : X.get (g, eventIndex) = some ⟨pc, .shfl .idx argument index 31 recv ok⟩
  instanceOrdinal : X.ShflK (g, eventIndex) ordinal
  peerEvent : X.get (g - laneOf l g + index, peerEventIndex) =
    some ⟨pc, .shfl .idx source peerIndex 31 peerRecv peerOk⟩
  peerOrdinal : X.ShflK (g - laneOf l g + index, peerEventIndex) ordinal
  peerLive : ¬ ShflExited X (g - laneOf l g + index) ordinal

/-- Choose the exclusive prefix and tile count using the actual indexed shuffle events. -/
theorem selectedRequestPath {p : Params} {l : Launch} {m : Mem0} {A : List Assumption}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel A m X)
    {g first batch : Nat} {t : TState} {F : List (Nat × Value)}
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ 2353 ∧ pair.1 ≠ 2354 ∧ pair.1 ≠ 7225 ∧
      pair.1 ≠ 7146 ∧ pair.1 ≠ 7155 ∧ pair.1 ≠ 2355)
    (hHeads : (7138, b32 p.heads) ∈ F) :
    let n := batch - first
    let part := fun lane => ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i
    let count := groupLaneTiles p first
    let previous := (∑ i ∈ Finset.range n, count i) * p.heads
    At t 2892 ([(294, .pred (decide (batch = first))), (7225, b32 0),
      (1208, b32 n), (7220, b32 (count (laneOf l g))), (7221, b32 (part (laneOf l g)))] ++ F) →
    (first < batch → IndexedSchedulerShuffle X l g 2894 (n - 1)
      (b32 (part (laneOf l g))) (b32 (part (n - 1)))) →
    (finish : IndexedSchedulerShuffle X l g 2898 n
      (b32 (count (laneOf l g))) (b32 (count n))) →
    ∃ events u, Run kernel [] l g t events (some u) ∧
      At u 2899 ([(2355, b32 (requestTiles p batch)), (7146, b32 p.batch),
        (7155, b32 800), (7225, b32 previous)] ++ F) ∧
      events.getLast? = X.get (g, finish.eventIndex) := by
  dsimp only
  intro ht hPrevious finish
  let n := batch - first
  let part := fun lane => ∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i
  let count := groupLaneTiles p first
  let previous := (∑ i ∈ Finset.range n, count i) * p.heads
  let base := [(294, .pred (decide (batch = first))), (1208, b32 n),
    (7220, b32 (count (laneOf l g))), (7221, b32 (part (laneOf l g)))] ++ F
  let ready := (7225, b32 previous) :: base
  let finEv : Event := ⟨2898, .shfl .idx (b32 (count (laneOf l g))) n 31 finish.recv finish.ok⟩
  have hBase : At t 2892 base := by
    refine ht.mono ?_
    exact ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.2⟩
  have hFreeBase : ∀ pair ∈ base, pair.1 ≠ 2353 ∧ pair.1 ≠ 2354 ∧ pair.1 ≠ 7225 ∧
      pair.1 ≠ 7146 ∧ pair.1 ≠ 7155 ∧ pair.1 ≠ 2355 := by
    intro pair hm
    simp only [base, List.cons_append, List.nil_append, List.mem_cons] at hm
    rcases hm with rfl | rfl | rfl | rfl | hIn
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact hFresh pair hIn
  have hFinish (u : TState) (hu : At u 2896 ready) :
      ∃ v w, run kernel [] l g 2 u = some v ∧ EStep kernel [] l g v finEv (some w) ∧
        At w 2899 ([(2355, b32 (requestTiles p batch)), (7146, b32 p.batch),
          (7155, b32 800), (7225, b32 previous)] ++ F) := by
    have hFree : ∀ pair ∈ ready, pair.1 ≠ 7155 ∧ pair.1 ≠ 7146 ∧ pair.1 ≠ 2355 := by
      intro pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact of_decide_eq_true rfl
      obtain ⟨_, _, _, hB, hC, hR⟩ := hFreeBase pair hm
      exact ⟨hC, hB, hR⟩
    obtain ⟨v, w, hv, hw, hW⟩ := selectedParametersObserved hp hX hFirst hGroup hBatch hu
      (by simp [ready, base, n]) (by simp [ready, base, count]) hFree
      finish.event finish.instanceOrdinal finish.peerEvent finish.peerOrdinal finish.peerLive
    refine ⟨v, w, hv, hw, hW.mono ?_⟩
    have hs := hW.2.2.2.2
    exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.2.2.2.2⟩
  by_cases hEq : batch = first
  · have hZero : previous = 0 := by simp [previous, n, hEq]
    have hReady : At t 2892 ((294, .pred true) :: ready) := ht.mono (by
      refine ⟨?_, ?_, hBase.2.2.2.2⟩
      · simpa only [hEq, decide_true] using ht.2.2.2.2.1
      · simpa only [hZero] using ht.2.2.2.2.2.1)
    obtain ⟨u, hU, hu⟩ := selectFirstRequest l g hReady (by simp)
    obtain ⟨v, w, hV, hW, hw⟩ := hFinish u (hu.mono hu.2.2.2.2.2)
    exact ⟨[finEv], w, .step (run_rtg (run_comp hU hV)) hW (.nil w),
      hw, finish.event.symm⟩
  · have hLT : first < batch := by omega
    let prior := hPrevious hLT
    let priorEv : Event :=
      ⟨2894, .shfl .idx (b32 (part (laneOf l g))) (n - 1) 31 prior.recv prior.ok⟩
    obtain ⟨u, hU, hu⟩ := selectPreviousLane l g (n := n) (by omega) (by omega) hBase
      (by simp [base, hEq]) (by simp [base]) (fun pair hm => (hFreeBase pair hm).1)
    have hIndexFree : ∀ pair ∈ (2353, b32 (n - 1)) :: base, pair.1 ≠ 2354 := by
      intro pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact of_decide_eq_true rfl
      exact (hFreeBase pair hm).2.1
    obtain ⟨v, hV, hv⟩ := previousPrefixObserved hp hX hLT hGroup hu
      (by simp [n]) (by simp [base, part]) hIndexFree prior.event
      prior.instanceOrdinal prior.peerEvent prior.peerOrdinal prior.peerLive
    have hvBase : At v 2895
        ((2354, b32 (∑ i ∈ Finset.range n, count i)) :: base) :=
      hv.mono ⟨hv.2.2.2.2.1, hv.2.2.2.2.2.2⟩
    obtain ⟨w, hW, hw⟩ := selectPreviousWork hp g hFirst hGroup hBatch
      (fun pair hm => (hFreeBase pair hm).2.2.1) (by simp [base, hHeads]) hvBase
    obtain ⟨s, z, hS, hZ, hz⟩ := hFinish w hw
    exact ⟨[priorEv, finEv], z,
      .step (run_rtg hU) hV (.step (run_rtg (run_comp hW hS)) hZ (.nil z)),
      hz, finish.event.symm⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
