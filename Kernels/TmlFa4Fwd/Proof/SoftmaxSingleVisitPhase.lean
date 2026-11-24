-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedScores
public import Kernels.TmlFa4Fwd.Proof.Protocol.SingleVisitReadyLimit
import Kernels.TmlFa4Fwd.Proof.MmaThirdReadyDemand
import Kernels.TmlFa4Fwd.Proof.Thread.Exit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof
open Epilogue (assignedCoordinates)

/-- A single visit cannot produce an event that requires the third K/V acquire. -/
theorem singleVisitNoLateSteadyEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {batch g j : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 = 1)
    {e : Event} (he : X.get (g,j) = some e) (hSite : 2355 ≤ e.pc ∧ e.pc < 2534) : False := by
  obtain ⟨k,hPoll⟩ := Mma.thirdReadyBeforeSteadyEvent hp hX he hSite
  exact Protocol.LoaderReady.singleVisitNoSlotTwoAcquire hp hX hDone hFrame hb hLo hHi hTrip hPoll

/-- A complete single visit takes the short route before any steady PV or QK issue. -/
theorem singleVisitNoSteadyEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {batch g j : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 = 1)
    {e : Event} (he : X.get (g,j) = some e) (hSite : 2295 ≤ e.pc ∧ e.pc < 2534) : False := by
  have hg := event_thread_lt hX he
  have hExit := (Thread.exitedOfComplete hX hDone hg).lastEvent hX hg
  obtain ⟨k,hPoll⟩ := Mma.thirdReadyOfFinishingSteadyEvent hp hX he hSite hExit
  exact Protocol.LoaderReady.singleVisitNoSlotTwoAcquire hp hX hDone hFrame hb hLo hHi hTrip hPoll

/-- A selected single-visit CTA's first score wait observes its initial QK commit. -/
theorem singleVisitFirstScorePhase {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X) (stage : Fin 2)
    {batch g wait : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 = 1)
    (hWait : X.get (g,wait) = some ⟨3425,.wait (waitLoc l g stage 1) 0 true true .cta⟩) :
    ∃ producer commit, FirstQkPhase l X stage producer g commit wait := by
  apply firstObservedInitialScorePhaseOfNoSteadyCommits hp hX stage hWait
  intro producer index spec pc hCta he hSite
  apply singleVisitNoLateSteadyEvent hp hX hDone hFrame hb
    (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hTrip) he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite
  rcases hSite with rfl | rfl
  · change 2355 ≤ 2418 ∧ 2418 < 2534
    decide
  · change 2355 ≤ 2519 ∧ 2519 < 2534
    decide

end PTX.Kernels.TmlFa4Fwd.Softmax
