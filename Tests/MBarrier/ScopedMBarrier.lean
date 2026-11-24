-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Source.Decode
public import Lemmas.MBarrier.MBarrierHistory

namespace PTX.Tests.ScopedMBarrier
noncomputable section

private def launch : Launch := { grid := 2, block := 384, clusterSize := 2, params := fun _ =>
                                 none }
private def m : Loc := ⟨.shared, 0, 128⟩
private def env : Decode.Env :=
  { classes := [⟨"r".toList, 1, 32⟩, ⟨"p".toList, 1, 1⟩], labels := [], params := [] }

example : Decode.op env "mbarrier.arrive.shared::cluster.b64"
    [.sink, .address [.register "r0"]] =
    .ok (.mbarArrive 0 0 (.imm 0) (.imm 1) true true .cta) := rfl
example : Decode.op env "mbarrier.arrive.release.cluster.shared::cluster.b64"
    [.sink, .address [.register "r0"], .literal "3"] =
    .ok (.mbarArrive 0 0 (.imm 0) (.imm 3) true true .cluster) := rfl
example : Decode.op env "mbarrier.arrive.expect_tx.shared::cluster.b64"
    [.sink, .address [.register "r0"], .literal "64"] =
    .ok (.mbarArrive 0 0 (.imm 64) (.imm 1) true true .cta) := rfl
example : Decode.op env "mbarrier.try_wait.parity.relaxed.cluster.shared::cta.b64"
    [.register "p0", .address [.register "r0"], .literal "0"] =
    .ok (.mbarWait 1 0 0 (.imm 0) false .cluster) := rfl

private def remote : TState := {
  regs := fun r => if r = 0 then some (.ptr 32 false (.shared 1 0) 128) else none
}
-- Remote addressing changes the object location; explicit count and scope survive into the event.
example : tmaTmpl launch 384 remote (.mbarArrive 0 0 (.imm 64) (.imm 3) true true .cluster) =
    .arrive m 64 (next remote) 3 true .cluster := rfl
-- A `.shared::cluster` pointer is not a `.shared::cta` operand: that use has no rule.
example : tmaTmpl launch 384 remote (.mbarArrive 0 0 (.imm 0) (.imm 1) false true .cta) =
    .ub .noRule := rfl

private def ops : List (AsyncCopy.Ref × MBarrier.Action) := [
  (.thread (0, 0), .init 1), (.thread (384, 1), .arrive 1 0), (.thread (0, 1), .pollParity 0 true)]
private def log : List (MBarrier.Record AsyncCopy.Ref) :=
  match MBarrier.replay none ops with | .ok xs => xs | .error _ => []
private theorem logChecked : MBarrier.CheckedLog log :=
  MBarrier.checkedLog_of_replay (ops := ops) (by rfl) (by decide)

private def execution (release acquire : Bool) (rs ws : MbarScope) : Execution := {
  tr := fun g => if g = 384 then
    [⟨0, .wr { loc := ⟨.global, 0, 0⟩, size := 1 } [(.bits 8 7, 0)]⟩,
      ⟨1, .arrive m 0 1 release rs⟩]
    else if g = 0 then [⟨0, .mbInit m 1⟩, ⟨1, .wait m 0 true acquire ws⟩,
      ⟨2, .rd { loc := ⟨.global, 0, 0⟩, size := 1 } [some (.bits 8 7, 0)]⟩]
    else []
  rf := fun _ _ => none
  objects := fun addr => if addr = m then log else []
}

example : AsyncCopy.objectAction (execution true true .cluster .cluster) {} m
    (.thread (384, 1)) = some (.arrive 1 0) := rfl
example : AsyncCopy.objectAction (execution false false .cta .cta) {} m
    (.thread (384, 1)) = some (.arrive 1 0) := rfl

private theorem matched : MBarrier.UpdateBeforeWait log (.thread (384, 1)) (.thread (0, 1)) :=
  ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩

private theorem sync : MSync launch (execution true true .cluster .cluster) (384, 0) (0, 2) := by
  refine ⟨(384, 1), (0, 1), m, .cluster, .cluster,
    ⟨0, 1, 1, rfl⟩, ⟨⟨1, 0, rfl⟩, matched⟩, ⟨?_, ?_⟩,
    rfl, by decide, by decide, rfl, by decide⟩
  · unfold MbarScopeIncludes SameCluster
    decide
  · unfold MbarScopeIncludes SameCluster
    decide

example : baseCausality launch (execution true true .cluster .cluster) (384, 0) (0, 2) :=
  .single (.inr (.inr (.inl sync)))

-- CTA scope does not include the peer, regardless of the object's shared::cluster address.
example : ¬ MbarScopeIncludes launch .cta 384 0 := by
  unfold MbarScopeIncludes SameCta
  decide

example (scope : MbarScope) : ¬ MbarRelease (execution false true .cluster .cluster) (384,
    1) m scope := by
  rintro ⟨tx, count, pc, hp⟩
  simp [Execution.get, execution] at hp

private theorem relaxed_not_acquire (addr : Loc) :
    ¬ (execution true false .cluster .cluster).AcquireWait (0, 1) addr := by
  rintro ⟨pc, parity, scope, hp⟩
  simp [Execution.get, execution] at hp

-- A relaxed successful poll cannot be used as an async completion visibility observation.
example (copy : EvId) (p : AsyncCopy.Part) (ws : MbarScope) :
    ¬ AsyncCopy.AsyncObserved (execution true false .cluster .cluster) copy p (0, 1) true ws := by
  rintro ⟨n, addr, -, ⟨pc, parity, hw⟩, -⟩
  exact relaxed_not_acquire addr ⟨pc, parity, ws, hw⟩

-- Failed polling is uncounted at every semantics and scope.
example : Event.counts ⟨0, .wait m 0 false true .cluster⟩ = false := rfl
example : Event.counts ⟨0, .wait m 0 false false .cta⟩ = false := rfl
example : Event.counts ⟨0, .wait m 0 true false .cluster⟩ = true := rfl

end
end PTX.Tests.ScopedMBarrier
