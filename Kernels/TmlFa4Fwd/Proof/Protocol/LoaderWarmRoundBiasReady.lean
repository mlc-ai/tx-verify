-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundBiasBound
public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasEmptyGeneration
import all Kernels.TmlFa4Fwd.Proof.Protocol.BiasEmptyGeneration
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Kernels.TmlFa4Fwd.Proof.Protocol.BiasBoxGenerations

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.MBarrier PTX.AsyncCopy Thread.Loader

/-- Each Bias-empty phase needs one softmax return cohort, and a return of phase `q` follows
a Bias-ready observation that a Bias box of generation `q` completed. When every Bias box
of the stage in the CTA has generation at most `gen`, the Bias-empty phase is at most
`gen+1`. -/
theorem biasReusePhaseAtMost {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta gen : Nat} (stage : Fin 2)
    (bound : ∀ e half spec, e.1/l.block = cta → BiasSubbox p l X e stage half spec →
      biasTensorOrdinal l X stage half e ≤ gen)
    {s : State} (hs : stateBefore (X.objects (biasEmptyObject l cta stage))
      (X.objects (biasEmptyObject l cta stage)).length = some s) :
    s.phase ≤ gen+1 := by
  classical
  let loc := biasEmptyObject l cta stage
  let log := X.objects loc
  change stateBefore log log.length = some s at hs
  have ordered := X.objects_checked hX loc
  have noInv := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have shape {r : Record Ref} (hr : r ∈ log) (update : CounterUpdate r.action) :=
    Thread.Softmax.biasEmptyUpdate hp hX stage hr update
  have noIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr hKind
    obtain ⟨_,_,_,_,_,_,hAct⟩ := shape hr (hKind.symm ▸ trivial)
    rw [hKind] at hAct
    cases hAct
  have unit (i : Nat) (r : Record Ref) (units bytes : Nat) (hr : log[i]? = some r)
      (_ : r.fault = none) (ha : r.action = .arrive units bytes) : units = 1 := by
    obtain ⟨_,_,_,_,_,_,hAct⟩ := shape (List.mem_of_getElem? hr) (ha.symm ▸ trivial)
    exact (Action.arrive.inj (ha.symm.trans hAct)).1
  have init : PairTmaRing.InitFirst X loc 4 := by
    have hActive : log ≠ [] := by intro h; simp [h,stateBefore] at hs
    obtain ⟨r,hr⟩ := List.exists_mem_of_ne_nil log hActive
    exact biasEmptyInitialized hp hX stage hr
  by_contra! hNot
  have allReturns := ordered.card_unit_arrivals_phase (q := gen+1) noInv unit
    (fun _ _ _ h => PairTmaRing.expected_of_init hX init noInv h) noIncr le_rfl hs hNot
  have hExists : 0 <
      ((Finset.range log.length).filter (fun i => UnitArrivalIn log (gen+1) i)).card := by
    rw [allReturns]
    decide
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hExists
  obtain ⟨_,r,tx,hr,ha,_,hAt⟩ := Finset.mem_filter.mp hi
  obtain ⟨e,hId,hReturn,_,_,_,hAct⟩ := shape (List.mem_of_getElem? hr) (ha.symm ▸ trivial)
  have hGen := (biasEmptyReleaseGeneration hp hX stage hr hId hAct).2
  rw [hAt] at hGen
  have hOrd : biasArrivalOrdinal X loc e = gen+1 := (Option.some.inj hGen).symm
  obtain ⟨_,j,q,poll,hPoll,_,hOk,hSeen,hLower,_⟩ :=
    Thread.Softmax.biasReadyObservedOfReturn hp hX stage hReturn
  obtain ⟨stop,_,_,hBoxes,_⟩ := biasReadyObservedCredits hp hX stage hPoll hOk hSeen
  let ready := X.objects (biasReadyObject l cta stage)
  have hBoxes' : 0 < (pairTxPhaseRecords ready stop q (.completeTx 16384)).card := by
    rw [hBoxes]
    decide
  obtain ⟨b,hb⟩ := Finset.card_pos.mp hBoxes'
  obtain ⟨_,phase,box,atBox,_,action⟩ := memPairTxPhaseRecords.mp hb
  have hShape := biasReadyRecord hp hX stage (List.mem_of_getElem? atBox)
  have hq : q ≤ gen := by
    cases hShape with
    | init h => obtain ⟨_,he⟩ := h; rw [he] at action; cases action
    | poll h => obtain ⟨_,_,he⟩ := h; rw [he] at action; cases action
    | expect _ _ _ he => rw [he] at action; cases action
    | notify issue half spec hid owner issued _ =>
      have hExact := biasNotificationPhaseExact hp hX stage atBox hid owner issued action phase
      have := bound issue half spec owner issued
      omega
  change biasArrivalOrdinal X loc e ≤ q at hLower
  omega

/-- The softmax warps have completed at least `gen` phases of a stage's Bias-empty object. -/
def BiasEmptyReleased (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2) (gen : Nat) :
    Prop :=
  let log := X.objects (biasEmptyObject l cta stage)
  ∃ s, stateBefore log log.length = some s ∧ gen ≤ s.phase

/-- Warp 14's Bias-empty waits of warm round `round` pass once softmax has released the
round's previous generation of each stage. The phase cannot run ahead of the warp's own
Bias boxes, so a lower bound on the releases fixes the phase parity. -/
theorem warmBiasEmptyReadyOfReleases {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : Prologue.warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (Epilogue.assignedCoordinates p batch (g/l.block)).1)
    (hRound : round < warmRounds p l g batch)
    (hReleased : ∀ stage, BiasEmptyReleased l X (g/l.block) stage (round+1)) :
    WarmBiasEmptyReady l X g batch round := by
  intro stage F shuffles votes ends cur hRank hRegs hLower lane hl failed
  obtain ⟨s,hs,hGe⟩ := hReleased stage
  have hLe := biasReusePhaseAtMost hp hX stage
    (warmBiasOrdinalsAtMost hp hX hFrame hg hw hb hLo hHi hTrips hRound stage cur hRank hRegs
      hLower hl failed) hs
  refine ⟨s,hs,?_⟩
  have hEq : s.phase = round+1 := by omega
  rw [hEq]
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
