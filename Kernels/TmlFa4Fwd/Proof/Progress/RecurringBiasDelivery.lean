-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasGenerationCredits
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringBiasProgress
import all Kernels.TmlFa4Fwd.Proof.Protocol.BiasCredits
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReady
import Kernels.TmlFa4Fwd.Proof.InputActualSources
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.MbarOneShot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.MBarrier PTX.AsyncCopy Thread.Loader Protocol.Bias

/-- A sufficiently late expectation and both requested half notifications suffice.
An expectation in a later phase already witnesses the required advance. -/
theorem biasAdvancedOfIssuedHalves {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : OutputFootprint p X) {cta gen : Nat} {stage : Fin 2}
    (arrival : ∃ e, X.Arrive e (biasReadyObject l cta stage) 32768 1 true .cta ∧
      gen ≤ biasArrivalOrdinal X (biasReadyObject l cta stage) e)
    (halves : ∀ half : Fin 2, ∃ issue spec, issue.1/l.block = cta ∧
      BiasSubbox p l X issue stage half spec ∧ biasTensorOrdinal l X stage half issue = gen) :
    let log := X.objects (biasReadyObject l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ gen+1 ≤ s.phase := by
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  obtain ⟨e,expectation,age⟩ := arrival
  have event := expectation
  obtain ⟨_,he⟩ := event
  have ac : objectAction X X.async loc (.thread e) = some (.arrive 1 32768) := by
    simp [objectAction,he,loc]
  obtain ⟨i,r,hr,id,act⟩ := MbarOneShot.Hist.record_of_action hMax.1 ac
  obtain ⟨st,hs,rank,_,_⟩ :=
    biasExpectationStateWithGuard hp hMax.1 stage hr id expectation act
  have lower : gen ≤ st.phase := rank ▸ age
  by_cases later : gen+1 ≤ st.phase
  · have noInv := objects_noInval hMax.1.tma.2.2.1 (fun _ _ => noMbarInval hMax.1) loc
    obtain ⟨s,found,mono⟩ := (X.objects_checked hMax.1 loc).phase_mono noInv
      (List.getElem?_eq_some_iff.mp hr).1.le le_rfl hs
    exact ⟨s,found,later.trans mono⟩
  have exactPhase : st.phase = gen := by omega
  apply biasPhaseAdvancedOfHalves hp hMax.1 stage hr act
    (by simp only [phaseAt,hs,Option.map_some,exactPhase])
  unfold NotifiedHalves
  dsimp only
  intro half
  obtain ⟨issue,box,owner,hBox,hAge⟩ := halves half
  have done : (X.tensor issue).any (fun o => o.effects.notified) = true := by
    cases h : (X.tensor issue).any (fun o => o.effects.notified) with
    | true => rfl
    | false => exact (hMax.not_grows (Protocol.LoaderReady.pendingTensorInput hp hMax.1 frame
        hBox.1 h)).elim
  have bytes := actualTensorInputTxBytes hp hMax.1 hBox.1
  obtain ⟨_,issued⟩ := hBox.1
  have addr := hBox.2.1
  rw [owner] at addr
  have notify : objectAction X X.async loc (.async issue (.notify .load)) =
      some (.completeTx 16384) := by
    cases obs : X.tensor issue with
    | none => simp [obs] at done
    | some o =>
      have notified : o.effects.notified = true := by simpa [obs] using done
      simp [objectAction,issued,obs,addr,notified,bytes,bind,Option.bind,loc]
  obtain ⟨j,n,found,nid,nact⟩ := MbarOneShot.Hist.record_of_action hMax.1 notify
  have noInv := objects_noInval hMax.1.tma.2.2.1 (fun _ _ => noMbarInval hMax.1) loc
  obtain ⟨_,st,prior,_⟩ := PairTmaRing.state_of_init hMax.1
    (biasInitialized hp hMax.1 stage (List.mem_of_getElem? found)) noInv found
    (by intro n; rw [nact]; simp)
  have ph : phaseAt log j = some st.phase := by
    change stateBefore log j = some st at prior
    simp only [phaseAt,prior,Option.map_some]
  have exactAge := biasNotificationPhaseExact hp hMax.1 stage found nid owner hBox nact ph
  exact ⟨j,n,issue,box,found,nid,owner,hBox,nact,
    ph.trans (congrArg some (exactAge.symm.trans hAge))⟩

end PTX.Kernels.TmlFa4Fwd.Progress
