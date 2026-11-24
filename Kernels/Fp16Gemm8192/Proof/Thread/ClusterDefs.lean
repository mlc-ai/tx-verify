-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Machine

@[expose] public section

/-! # A thread's cluster barrier phase

The cluster barrier arrivals a thread has made (`clArrives`), the count its state implies
(`ThreadD.clPhase`), and the exit wait a thread past it has made (`ExitWaited`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX

noncomputable section

/-- A cluster barrier arrival. -/
def isClArrive (e : Event) : Bool := match e.kind with | .cluster (.arrive ..) => true | _ => false

/-- A thread's cluster barrier arrivals. -/
def clArrives (es : List Event) : Nat := es.countP isClArrive

/-- The cluster barrier arrivals before a state. -/
def ThreadD.clPhase : ThreadD → Nat
  | .inl p => match p.site with | .wait | .setMaxReg | .roleElect => 1 | _ => 0
  | .inr (.loader l) => match l.site with | .exitWait | .exit => 2 | _ => 1
  | .inr (.mma m) => match m.site with | .exitWait | .exit => 2 | _ => 1
  | .inr (.sched s) => match s.site with | .exitWait | .exit => 2 | _ => 1
  | .inr (.cons c) =>
    match c.site with | .exitWait | .relinquish | .ldBase | .dealloc | .exit => 2 | _ => 1

/-- A state after the exit's cluster wait. -/
def ThreadD.afterWait : ThreadD → Prop
  | .inr (.loader l) => l.site = .exit
  | .inr (.mma m) => m.site = .exit
  | .inr (.sched s) => s.site = .exit
  | .inr (.cons c) => c.site = .relinquish ∨ c.site = .ldBase ∨ c.site = .dealloc ∨ c.site = .exit
  | .inl _ => False

/-- The thread's exit wait: a cluster wait after its second arrival. -/
def ExitWaited (es : List Event) : Prop :=
  ∃ j pc al, es[j]? = some ⟨pc, .cluster (.wait al)⟩ ∧ clArrives (es.take j) = 2

/-- A thread's cluster barrier operations, arrivals and waits. -/
def clOps (es : List Event) : Nat := es.countP isCluster

/-- The cluster barrier operations before a state: the prologue's arrival and wait, then the
exit's arrival and wait. -/
def ThreadD.clOps : ThreadD → Nat
  | .inl p => match p.site with | .wait => 1 | .setMaxReg | .roleElect => 2 | _ => 0
  | .inr (.loader l) => match l.site with | .exitWait => 3 | .exit => 4 | _ => 2
  | .inr (.mma m) => match m.site with | .exitWait => 3 | .exit => 4 | _ => 2
  | .inr (.sched s) => match s.site with | .exitWait => 3 | .exit => 4 | _ => 2
  | .inr (.cons c) =>
    match c.site with | .exitWait => 3 | .relinquish | .ldBase | .dealloc | .exit => 4 | _ => 2

/-- A state at a cluster barrier operation. -/
def ThreadD.AtCluster : ThreadD → Prop
  | .inl p => p.site = .arrive ∨ p.site = .wait
  | .inr (.loader l) => l.site = .exitArrive ∨ l.site = .exitWait
  | .inr (.mma m) => m.site = .exitArrive ∨ m.site = .exitWait
  | .inr (.sched s) => s.site = .exitArrive ∨ s.site = .exitWait
  | .inr (.cons c) => c.site = .exitArrive ∨ c.site = .exitWait

/-- Every thread's `n`-th cluster barrier operation (from 0): the prologue's arrival and wait,
then the exit's. -/
def clEvent : Nat → Event
  | 0 => ⟨Flow.clusterArrive_0, .cluster (.arrive true true)⟩
  | 1 => ⟨Flow.clusterWait_0, .cluster (.wait true)⟩
  | 2 => ⟨Flow.clusterArrive_1, .cluster (.arrive true true)⟩
  | _ => ⟨Flow.clusterWait_1, .cluster (.wait true)⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
