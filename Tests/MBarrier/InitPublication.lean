-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Source.Decode
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.MBarrier.MBarrierHistory
public import Lemmas.MBarrier.MBarrierInitOrder

namespace PTX.Tests.InitPublication
noncomputable section

private def L : Launch := { grid := 2, block := 1, clusterSize := ⟨2, by decide⟩, params := fun _ =>
                            none }
private def m : Loc := ⟨.shared, 0, 64⟩
private def history : List (ClusterBarrier.Record EvId) := [
  .arrival 0 0 false [(0, (0, 2))], .arrival 1 0 false [(1, (1, 0))],
  .wait 0 0 [(0, (0, 3))], .wait 1 0 [(1, (1, 1))]]
private def initialRecord : MBarrier.Record AsyncCopy.Ref :=
  ⟨.thread (0, 0), .init 1, ⟨some ⟨0, 1, 1, 0, true⟩, none, none⟩, none⟩
private def useRecord : MBarrier.Record AsyncCopy.Ref :=
  ⟨.thread (1, 2), .arrive 1 0, ⟨some ⟨1, 1, 1, 0, false⟩, none, none⟩, none⟩
private def X : Execution := {
  tr := fun g => if g = 0 then
    [⟨0, .mbInit m 1⟩, ⟨1, .fenceMbarInit⟩, ⟨2, .cluster (.arrive false true)⟩,
      ⟨3, .cluster (.wait true)⟩]
    else if g = 1 then [⟨0, .cluster (.arrive false true)⟩, ⟨1, .cluster (.wait true)⟩,
      ⟨2, .arrive m 0 1 true .cluster⟩] else []
  rf := fun _ _ => none
  clusters := fun c => if c = 0 then history else []
  objects := fun loc => if loc = m then [initialRecord, useRecord] else []
}

private def stateOf : ClusterBarrier.Outcome → ClusterBarrier.State
  | .done s => s | _ => {}
private def phaseOf : ClusterBarrier.Outcome → Option Nat
  | .done s => some s.phase | _ => none
private theorem done_of_phase {o : ClusterBarrier.Outcome} {p : Nat} (h : phaseOf o = some p) :
    o = .done (stateOf o) := by cases o <;> simp_all [phaseOf, stateOf]

private theorem arrival : ClusterBarrier.ArrivalOf 1 2 history (0, 2) 0 false := by
  refine ⟨0, {}, stateOf (ClusterBarrier.run 1 2 {} (history.take 1)),
    0, 0, [(0, (0, 2))], 0, rfl, rfl, by simp, rfl, ?_⟩
  exact done_of_phase (p := 0) (by decide)
private theorem waited : ClusterBarrier.WaitOf 1 2 history (1, 1) 0 := by
  let s := stateOf (ClusterBarrier.run 1 2 {} (history.take 3))
  let r : ClusterBarrier.Record EvId := .wait 1 0 [(1, (1, 1))]
  refine ⟨3, s, stateOf (r.perform 1 2 s), 1, 0, [(1, (1, 1))], 1,
    rfl, ?_, by simp, rfl, ?_⟩
  · exact done_of_phase (p := 1) (by decide)
  · exact done_of_phase (p := 1) (by decide)

/-- The cluster arrival of CTA 0 and the wait of CTA 1 observe each other: the two records
`arrival` and `waited` belong to one phase of the same cluster barrier. -/
private theorem observed : ∃ c phase,
    ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt c) (X.clusters c) (0, 2) phase false ∧
    ClusterBarrier.WaitOf L.block (L.clusterSizeAt c) (X.clusters c) (1, 1) phase :=
  ⟨0, 0, arrival, waited⟩

private theorem sync : InitFenceSync L X m (0, 0) (1, 1) :=
  ⟨1, (0, 1), (0, 2), 1, 2, false, true, 1, true, ⟨0, rfl⟩, rfl, rfl, rfl, rfl, by decide, rfl,
    by decide, rfl, rfl, observed⟩

private theorem waitBefore : baseCausality L X (1, 1) (1, 2) :=
  .single (.inl ⟨rfl, by decide, by decide, by decide⟩)

private theorem published : InitFencePublished L X (0, 0) (1, 2) m := ⟨(1, 1), sync, waitBefore⟩

-- A restricted release fence publishes initialization through a relaxed cluster arrival.
example : InitPublished L X (0, 0) (1, 2) m := Or.inr published

-- The publication is consumed by the actual object safety check.
example : ObjectPublished L X m useRecord := by
  apply Or.inr
  refine ⟨(0, 0), 1, ⟨0, rfl⟩, ?_, Or.inr published, ?_⟩
  · exact ⟨0, 1, initialRecord, useRecord, 1, rfl, rfl, rfl, rfl, rfl, rfl, by decide,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩
  · rintro ⟨g, j⟩ ⟨pc, hv⟩
    simp only [Execution.get, X] at hv
    split_ifs at hv <;> (rcases j with _ | _ | _ | _ | j) <;> simp at hv

-- The supplied object records are actual transitions, not fabricated successful replies.
example : MBarrier.replay none [(.thread (0, 0), .init 1), (.thread (1, 2), .arrive 1 0)] =
    .ok [initialRecord, useRecord] := rfl

-- A normal store or a different thread's instruction cannot be substituted for init.
example : ¬ InitFencePublished L X (1, 0) (1, 2) m := by
  rintro ⟨_, ⟨count, _, _, _, _, _, _, _, _, hi, _⟩, _⟩
  simp [Execution.MbInit, Execution.get, X] at hi

-- This instruction is not a generic/async proxy fence.
example : ¬ X.IsProxyFence (0, 1) (.async (some (.shared .cta))) none := by
  rintro ⟨pc, h⟩
  simp [Execution.get, X] at h

-- Nor does a relaxed arrival acquire generic data visibility from its preceding init fence.
example : ¬ ClusterSync L X (0, 0) (1, 2) := by
  rintro ⟨_, i, j, ⟨phase, ha, _⟩, _⟩
  obtain ⟨k, s, t, c, w, lanes, g, hk, _⟩ := ha
  have hm := List.mem_of_getElem? hk
  simp [L, X, Launch.clusterOfCta, history] at hm

example : Decode.op { classes := [], labels := [], params := [] }
    "fence.mbarrier_init.release.cluster" [] = .ok .fenceMbarInit := rfl
example : eventTmpl [] L 0 {} .fenceMbarInit = .fenceMbarInit (next {}) := rfl
example : Op.isLocal .fenceMbarInit = false := rfl

/-! ### Object order: the initialization precedes the peer CTA's use

The same events with the use recorded before the initialization in the object's history. With
the fence, `InitFenceOrdered` (a `Consistent` field) excludes this order; without the fence (the
thread executes `fence.proxy.async.shared::cta` in its place) it does not, and the relaxed
arrival publishes nothing. -/

private def withFence (fence : Kind) : Execution := {
  tr := fun g => if g = 0 then
    [⟨0, .mbInit m 1⟩, ⟨1, fence⟩, ⟨2, .cluster (.arrive false true)⟩, ⟨3, .cluster (.wait true)⟩]
    else if g = 1 then [⟨0, .cluster (.arrive false true)⟩, ⟨1, .cluster (.wait true)⟩,
      ⟨2, .arrive m 0 1 true .cluster⟩] else []
  rf := fun _ _ => none
  clusters := fun c => if c = 0 then history else []
  objects := fun loc => if loc = m then [useRecord, initialRecord] else []
}

private abbrev fenced : Execution := withFence .fenceMbarInit
private abbrev unfenced : Execution := withFence (.fenceProxy (.async (some (.shared .cta))) none)

private theorem fenced_sync : InitFenceSync L fenced m (0, 0) (1, 1) :=
  ⟨1, (0, 1), (0, 2), 1, 2, false, true, 1, true, ⟨0, rfl⟩, rfl, rfl, rfl, rfl, by decide, rfl,
    by decide, rfl, rfl, observed⟩

private theorem use_before_init (fence : Kind) :
    MBarrier.Before ((withFence fence).objects m) (.thread (1, 2)) (.thread (0, 0)) :=
  ⟨0, 1, useRecord, initialRecord, rfl, rfl, rfl, rfl, by decide⟩

-- With `fence.mbarrier_init`, the use after the peer's wait follows the initialization: the
-- history that places it first is not a possible execution.
example : ¬ InitFenceOrdered L fenced := fun h =>
  h m (0, 0) (1, 1) (.thread (1, 2)) fenced_sync
    (.single (.inr (.inl ⟨rfl, rfl, (1, 1), (1, 2), rfl, rfl,
      .single (.inl ⟨rfl, by decide, by decide, by decide⟩)⟩))) (use_before_init _)

-- Without it nothing orders the initialization before the use: the same history is allowed by
-- this rule, and the initialization is not published to the use.
example : InitFenceOrdered L unfenced := by
  rintro _ _ _ _ ⟨_, ⟨g, i⟩, _, _, _, _, _, _, _, _, -, -, h, -, -, -, -, -, -, -⟩ -
  simp only [Execution.get, withFence] at h
  split_ifs at h <;> (rcases i with _ | _ | _ | _ | i) <;> simp at h

example : ¬ InitFencePublished L unfenced (0, 0) (1, 2) m := by
  rintro ⟨_, ⟨_, ⟨g, i⟩, _, _, _, _, _, _, _, _, -, -, h, -, -, -, -, -, -, -⟩, -⟩
  simp only [Execution.get, withFence] at h
  split_ifs at h <;> (rcases i with _ | _ | _ | _ | i) <;> simp at h

-- The rule as used by kernel proofs: a published initialization is before the use in its
-- object's order in every possible execution.
example {K : Kernel} {A : List Assumption} {mem0 : Mem0} {Y : Execution}
    (hY : Consistent L K A mem0 Y) {init : EvId} {y : AsyncCopy.Ref}
    (hinit : ∃ c, Y.MbInit init m c) (h : InitPublished L Y init y.issuer m) :
    ¬ MBarrier.Before (Y.objects m) y (.thread init) :=
  object_not_before_of_published hY hinit h

end
end PTX.Tests.InitPublication
