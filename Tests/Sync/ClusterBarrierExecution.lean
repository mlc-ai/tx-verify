-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Source.Decode

namespace PTX.Tests.ClusterExecution
noncomputable section

private def launch : Launch := { grid := 2, block := 1, clusterSize := 2, params := fun _ => none }
private def loc : Acc := { loc := ⟨.global, 0, 0⟩, size := 1 }
private def history : List (ClusterBarrier.Record EvId) := [
  .arrival 0 0 true [(0, (0, 1))], .arrival 1 0 true [(1, (1, 0))],
  .wait 0 0 [(0, (0, 2))], .wait 1 0 [(1, (1, 1))]]
private def execution : Execution := {
  tr := fun g => if g = 0 then
    [⟨0, .wr loc [(.bits 8 7, 0)]⟩, ⟨1, .cluster (.arrive true true)⟩,
      ⟨2, .cluster (.wait true)⟩, ⟨3, .exit⟩]
    else if g = 1 then
      [⟨0, .cluster (.arrive true true)⟩, ⟨1, .cluster (.wait true)⟩,
        ⟨2, .rd loc [some (.bits 8 7, 0)]⟩, ⟨3, .exit⟩]
    else []
  rf := fun _ _ => none
  clusters := fun c => if c = 0 then history else []
}

private def stateOf : ClusterBarrier.Outcome → ClusterBarrier.State
  | .done s => s
  | _ => {}
private def phaseOf : ClusterBarrier.Outcome → Option Nat
  | .done s => some s.phase
  | _ => none
private theorem done_of_phase {o : ClusterBarrier.Outcome} {p : Nat} (h : phaseOf o = some p) :
    o = .done (stateOf o) := by
  cases o <;> simp_all [phaseOf, stateOf]

-- A genuine checked history, with references to source events in both CTAs.
example : ClusterHistoryOk launch execution := by
  refine ⟨by decide, ?_, ?_⟩
  · intro c hc
    have hc' : c ≠ 0 := by change 1 ≤ c at hc; omega
    simp [execution, hc']
  · intro c hc
    have hc' : c = 0 := by change c < 1 at hc; omega
    subst c
    refine ⟨by decide, ?_, ?_⟩
    · intro r hr
      simp only [execution, ↓reduceIte, history, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp [ClusterSources, Execution.get, execution, launch] <;> decide
    · exact ⟨stateOf (ClusterBarrier.run 1 2 {} history),
        done_of_phase (p := 1) (by decide)⟩

private theorem arrival : ClusterBarrier.ArrivalOf 1 2 history (0, 1) 0 true := by
  refine ⟨0, {}, stateOf (ClusterBarrier.run 1 2 {} (history.take 1)),
    0, 0, [(0, (0, 1))], 0, rfl, rfl, by simp, rfl, ?_⟩
  exact done_of_phase (p := 0) (by decide)

private theorem waited : ClusterBarrier.WaitOf 1 2 history (1, 1) 0 := by
  let s := stateOf (ClusterBarrier.run 1 2 {} (history.take 3))
  let r : ClusterBarrier.Record EvId := .wait 1 0 [(1, (1, 1))]
  refine ⟨3, s, stateOf (r.perform 1 2 s), 1, 0, [(1, (1, 1))], 1,
    rfl, ?_, by simp, ?_, ?_⟩
  · exact done_of_phase (p := 1) (by decide)
  · rfl
  · exact done_of_phase (p := 1) (by decide)

private theorem synchronized : ClusterSync launch execution (0, 0) (1, 2) := by
  refine ⟨by unfold SameCluster; decide, 1, 1, ?_, by decide, by decide, by decide, by decide⟩
  exact ⟨0, arrival, waited⟩

-- This reaches the actual baseCausality definition, rather than a disconnected helper predicate.
example : baseCausality launch execution (0, 0) (1, 2) :=
  .single (.inr (.inr (.inr (.inl synchronized))))

-- A pending wait cannot be passed without a record of the wait in the cluster history.
example : ¬ Ready launch { execution with clusters := fun _ => [] } (0, 2) := by
  intro h
  have hn : Need.node (fun x => ∃ i, ∃ r : ClusterBarrier.Record EvId, ∃ y,
      ([] : List (ClusterBarrier.Record EvId))[i]? = some r ∧ (0, 2) ∈ r.refs ∧
      x = .thread y ∧ y.1 = 0 ∧ (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧
        ([] : List (ClusterBarrier.Record EvId))[j]? = some (ClusterBarrier.Record.exit g y))) ∈
      Needs launch { execution with clusters := fun _ => [] } (0, 2) := by
    simp [Needs, KindNeeds, clusterNeeds, clusterWarpNeeds, warpLanes, warpLane, execution,
      Execution.get, launch, warpSize, laneOf]
  obtain ⟨x, -, i, r, y, hr, -⟩ := h _ hn
  simp at hr

-- Events after arrival do not acquire the arrival's publishing guarantee.
example : ¬ ClusterSync launch execution (0, 2) (1, 2) := by
  rintro ⟨_, i, j, ⟨phase, ha, _⟩, _, hi, _⟩
  obtain ⟨k, s, t, c, w, lanes, g, hk, _, he, _⟩ := ha
  have hm := List.mem_of_getElem? hk
  change ClusterBarrier.Record.arrival c w true lanes ∈ history at hm
  simp only [history, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm | hm | hm
  · cases hm
    simp at he
    omega
  · cases hm
    simp at he
  · cases hm
  · cases hm

private def relaxedHistory : List (ClusterBarrier.Record EvId) := [
  .arrival 0 0 false [(0, (0, 1))], .arrival 1 0 false [(1, (1, 0))],
  .wait 0 0 [(0, (0, 2))], .wait 1 0 [(1, (1, 1))]]

-- Counter completion through relaxed arrivals is insufficient for generic visibility.
example : ¬ ClusterSync launch
    { execution with clusters := fun _ => relaxedHistory } (0, 0) (1, 2) := by
  rintro ⟨_, i, j, ⟨phase, ha, _⟩, _⟩
  obtain ⟨k, s, t, c, w, lanes, g, hk, _⟩ := ha
  have hm := List.mem_of_getElem? hk
  simp [relaxedHistory] at hm

private def badAligned : Execution := {
  tr := fun g => if g = 0 then [⟨0, .cluster (.arrive true true)⟩]
    else if g = 1 then [⟨1, .cluster (.arrive true true)⟩] else []
  rf := fun _ _ => none
}
private def oneCta : Launch := { launch with block := 2, grid := 1, clusterSize := 1 }
private theorem alignedMismatch (K : Kernel) : AlignedMismatch oneCta K badAligned := by
  refine ⟨.cluster, .inl ((AlignedClass.divergent_cluster_iff oneCta).2
    ⟨0, 1, 0, 0, 0, 1, .arrive true true, .arrive true true,
    ?_, rfl, rfl, rfl, Or.inl rfl, Or.inl (by decide)⟩)⟩
  unfold SameWarp SameCta
  decide

-- Alignment checking is wired to Unsafe, rather than only to history validation.
example : Unsafe oneCta { name := "k", params := [], code := [] } [] (fun _ => none) badAligned :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (alignedMismatch _)))))))))

private def env : Decode.Env := { classes := [], labels := [], params := [] }
example : Decode.op env "barrier.cluster.arrive.aligned" [] =
    .ok (.cluster (.arrive true true)) := rfl
example : Decode.op env "barrier.cluster.arrive.relaxed.aligned" [] =
    .ok (.cluster (.arrive false true)) := rfl
example : Decode.op env "barrier.cluster.wait.acquire" [] =
    .ok (.cluster (.wait false)) := rfl
example : eventTmpl [] launch 0 {} (.cluster (.arrive false true)) =
    .cluster (.arrive false true) { pc := 1 } := rfl
example : Fires 4 (.cluster (.wait true) { pc := 5 })
    ⟨4, .cluster (.wait true)⟩ (some { pc := 5 }) := ⟨rfl, rfl⟩

end
end PTX.Tests.ClusterExecution
