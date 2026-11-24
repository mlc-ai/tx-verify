-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Time
public import Kernels.FlashAttn4Fwd.Proof.Interface.Cluster

@[expose] public section

/-! # What the thread layer exports for the progress at the cluster barrier

Each thread makes two cluster-barrier operations, the prologue's arrival and wait
(`ClusterFacts`). The progress step at an unrecorded operation compares the time of the blocked
thread's state with the times of the lanes it waits for, and appends a record of the blocked
warp, which needs all lanes of the warp at one event. The fields are facts of each thread's own
events and states, from the prologue's run invariant (`Prologue.Run.clusters`: a prologue site
has made as many operations as it counts) and the roles' (a role state follows the wait):

* the time of a state is fixed by the number of operations before it (`state_time`): with the
  arrival made, it is at the wait's site; with both made, it is at a role state, at least at the
  time of the roles' `setmaxnreg`;
* a thread's current time (`endTime`, `end_time`) with no operation made is at most the
  arrival's time, and with only the arrival made at most the wait's;
* after a cluster-barrier operation the machine is at a state (`live`);
* the arrival is at PTX `clusterArrive_0` and the wait at `clusterWait_0` (`arrive_pc`,
  `wait_pc`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX

noncomputable section

/-- The thread layer's facts for the progress at the cluster barrier. -/
structure ClusterWaitFacts (L : Launch) (X : Execution) : Prop where
  /-- The time of a thread's state before its event `k` is fixed by its cluster-barrier
  operations before `k`: one, the wait's time; two, at least the roles' `setmaxnreg` time. -/
  state_time : ∀ {g k : Nat} {d : ThreadD}, g < L.threads → St L X g k = some (some d) →
    (((X.tr g).take k).countP PTX.isCluster = 1 → stateTime L g d = Progress.Time.clWaitT) ∧
    (((X.tr g).take k).countP PTX.isCluster = 2 → Progress.Time.regT ≤ stateTime L g d)
  /-- A thread's current time: with no cluster-barrier operation made, at most the arrival's
  time; with one, at most the wait's. -/
  end_time : ∀ {g : Nat}, g < L.threads →
    ((X.tr g).countP PTX.isCluster = 0 → endTime L X g ≤ Progress.Time.clArriveT) ∧
    ((X.tr g).countP PTX.isCluster = 1 → endTime L X g ≤ Progress.Time.clWaitT)
  /-- After a cluster-barrier operation the machine is at a state. -/
  live : ∀ {g k pc : Nat} {op : ClusterOp}, g < L.threads →
    X.get (g, k) = some ⟨pc, .cluster op⟩ → ∃ d, St L X g (k + 1) = some (some d)
  /-- Every cluster-barrier arrival is at PTX `clusterArrive_0`. -/
  arrive_pc : ∀ {g k pc : Nat} {rel al : Bool}, g < L.threads →
    X.get (g, k) = some ⟨pc, .cluster (.arrive rel al)⟩ → pc = Flow.clusterArrive_0
  /-- Every cluster-barrier wait is at PTX `clusterWait_0`. -/
  wait_pc : ∀ {g k pc : Nat} {al : Bool}, g < L.threads →
    X.get (g, k) = some ⟨pc, .cluster (.wait al)⟩ → pc = Flow.clusterWait_0

/-- The times around the cluster start barrier (`Sched.ClusterTimes`). -/
theorem ClusterWaitFacts.toTimes {L : Launch} {X : Execution} (hw : ClusterWaitFacts L X) :
    Sched.ClusterTimes (timed L) X Progress.Time.clArriveT Progress.Time.clWaitT Progress.Time.regT
      Flow.clusterArrive_0 Flow.clusterWait_0 :=
  ⟨hw.state_time, hw.end_time, hw.live, hw.arrive_pc, hw.wait_pc, by decide⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
