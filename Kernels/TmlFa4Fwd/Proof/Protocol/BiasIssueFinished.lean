-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasExitObservation
public import Kernels.TmlFa4Fwd.Proof.LoaderBiasIssueExtent
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasExitExtent
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.NamedBarLedger
import Lemmas.Protocol.MbarRingRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Thread.Loader Epilogue

private theorem issuedBiasHalfOfObservation {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {tensor : EvId} {stage half : Fin 2} {spec : TensorCopy.Spec}
    (hIssue : BiasSubbox p l X tensor stage half spec) {j : Nat} {r : Record Ref}
    (hGet : (X.objects (biasReadyObject l (tensor.1/l.block) stage))[j]? = some r)
    (hReply : r.reply.waited = some true)
    (hPhase : observedAt (X.objects (biasReadyObject l (tensor.1/l.block) stage)) j =
      some (biasTensorOrdinal l X stage half tensor)) :
    MbarObserved X (.async tensor (.notify .load)) r.id := by
  obtain ⟨landed,box,hOwner,hBox,hOrd,hObserved⟩ :=
    biasReadyObservedHalfOwner hp hX stage half hGet hReply hPhase
  obtain rfl := biasTensorOrdinalInjective hp hX hBox hIssue hOwner hOrd
  exact hObserved

/-- An issued Bias half is observed once an appropriate CTA lane has enough successful
acquires for the issue's own generation. A skipped phase still has its actual preceding
consumer, recovered through the loader's checked stage reuse. -/
theorem biasIssueObservedOfConsumerExtent {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {tensor : EvId} {stage half : Fin 2} {spec : TensorCopy.Spec}
    (hIssue : BiasSubbox p l X tensor stage half spec)
    {g : Nat} (hCta : g/l.block = tensor.1/l.block) (hWarp : Prologue.warpIndex l g < 8)
    (hStage : Prologue.warpIndex l g / 4 = stage.val)
    (hExtent : biasTensorOrdinal l X stage half tensor <
      okPolls (biasReadyObject l (tensor.1/l.block) stage) (X.tr g)) :
    ∃ wait, wait.1 / l.block = tensor.1/l.block ∧
      MbarObserved X (.async tensor (.notify .load)) (.thread wait) := by
  let cta := tensor.1/l.block
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  let phase := biasTensorOrdinal l X stage half tensor
  have hClean : ∀ r ∈ log, (∃ q ok, r.action = .pollParity q ok) → r.fault = none :=
    fun _ hr hq => actualInitOrPollClean hp hX hr (.inr hq)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨j,w,_,hw,hWId,_,hSuccess,_,hCount⟩ := MbarRing.Poll.record hX hClean hExtent
  have hSelected := objectThreadSelected_iff.mpr ⟨_,hWId⟩
  have hAlt := Thread.Softmax.biasReadySelectedAlternates hp hX stage hWarp hCta hStage hClean
  have hChecked := X.objects_checked hX loc
  obtain ⟨st,hState,hLower,_⟩ :=
    hChecked.selected_poll_phase_ge hNo (objectThreadSelected g) (by decide) hAlt
      hw hSelected hSuccess
  rw [hCount] at hLower
  have hPos : 0 < st.phase := by omega
  obtain ⟨s,q,hs,_,_,hCompleted⟩ := hChecked.okPoll hw hSuccess
  rw [hState] at hs
  obtain rfl := Option.some.inj hs
  let observed := st.phase-1
  have hObserved : observedAt log j = some observed := by
    change (log[j]?).bind (·.reply.completed) = some observed
    rw [hw,Option.bind_some,hCompleted,ite_eq_left hPos]
  have hLe : phase ≤ observed := by dsimp [observed]; omega
  rcases Nat.eq_or_lt_of_le hLe with hSame | hLater
  · rw [← hSame] at hObserved
    have hObserve := issuedBiasHalfOfObservation hp hX hIssue hw hSuccess hObserved
    rw [hWId] at hObserve
    exact ⟨(g,_),hCta,hObserve⟩
  obtain ⟨next,newSpec,hOwner,hNextIssue,hOrdinal,_⟩ :=
    biasReadyObservedHalfOwner hp hX stage half hw hSuccess hObserved
  obtain ⟨thread,atBox⟩ := next
  have useNext {a : Nat} {later : TensorCopy.Spec}
      (hNext : BiasSubbox p l X (thread,a) stage half later)
      (hOrd : biasTensorOrdinal l X stage half (thread,a) = phase + 1) :
      ∃ wait, wait.1 / l.block = cta ∧
        MbarObserved X (.async tensor (.notify .load)) (.thread wait) := by
    obtain ⟨release,_,hReturn,hCta',_,hCount,_,_⟩ :=
      biasTensorReuseOfConsumerWarp hp hX (0 : Fin 4) hNext (by omega)
    rw [hOwner] at hReturn hCta' hCount
    have he : biasArrivalOrdinal X (biasEmptyObject l cta stage) release = phase := by omega
    obtain ⟨k,i,r,hGet,hId,hReply,hSeen,_⟩ := biasReturnObservedReadyExact hp hX stage hReturn
    rw [he] at hSeen
    have hObserve := issuedBiasHalfOfObservation hp hX hIssue hGet hReply hSeen
    rw [hId] at hObserve
    exact ⟨(release.1,k),hCta',hObserve⟩
  by_cases hEq : observed = phase+1
  · exact useNext hNextIssue (hOrdinal.trans hEq)
  have hP : phase+1 < biasTensorOrdinal l X stage half (thread,atBox) := by omega
  obtain ⟨k,_,earlier,hEarlier,hNext⟩ := biasEarlierHalfOfOrdinal hp hX hP
  exact useNext hEarlier hNext

/-- In an exited CTA every issued Bias subbox completed before a real consumer's exit. -/
theorem biasTensorNotificationFinishedAtExit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {tensor : EvId} {stage half : Fin 2} {spec : TensorCopy.Spec}
    (hIssue : BiasSubbox p l X tensor stage half spec)
    (hExit : CtaExited l X (tensor.1/l.block)) :
    SharedFinished l kernel Assumptions.all X
      (.async tensor (.notify .load)) (tensor.1/l.block) := by
  let cta := tensor.1/l.block
  let g := cta*l.block + 128*stage.val
  have hStageVal := stage.isLt
  have hLane : 128*stage.val < l.block := by rw [hp.block]; omega
  obtain ⟨_,hGet⟩ := hIssue.1
  have hGrid : cta < l.grid := NamedBar.cta_lt (PTX.Proof.event_thread_lt hX hGet)
  have hg : g < l.threads := NamedBar.cta_thread_lt hGrid hLane
  have hCta : g/l.block = cta := by
    simp [g,hp.block]
    omega
  have hLocal : g % l.block = 128*stage.val := by
    simp [g,hp.block]
    omega
  have hW : Prologue.warpIndex l g = 4*stage.val := by
    unfold Prologue.warpIndex
    rw [hLocal]
    omega
  have hw : Prologue.warpIndex l g < 8 := by omega
  have hStage : Prologue.warpIndex l g / 4 = stage.val := by omega
  obtain ⟨batch,hb,hLo,hHi,hBudget⟩ := Loader.biasTensorOrdinalWithinBudget hp hX hCuQ hIssue
  have hWork : cta < tilePrefix p p.batch * p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  obtain ⟨site,hLast⟩ := hExit g hg hCta
  let finish := (X.tr g).length - 1
  have hEnd : X.get (g,finish) = some ⟨site,.exit⟩ := by
    change (X.tr g)[finish]? = _
    rwa [← List.getLast?_eq_getElem?]
  obtain ⟨same,hSame,hSLo,hSHi,hPoll⟩ :=
    Softmax.biasAcquireExtentAtExit hp hX hCuQ (usedKProtected hp hX)
      hw (hCta.symm ▸ hWork) hEnd rfl
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hBatch : same = batch :=
    (hUnique same ⟨hSame,hCta ▸ hSLo,hCta ▸ hSHi⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst same
  have hStageEq : Softmax.stageOf ⟨Prologue.warpIndex l g,hw⟩ = stage := Fin.ext hStage
  rw [hCta,hStageEq] at hPoll
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  have hPos := (Mma.trips_bounds hp hb hTile).1
  have hAlgebra := Loader.biasLoaderBudget_le_consumer p batch
    (assignedCoordinates p batch cta).1 stage hPos
  have hBefore : biasTensorOrdinal l X stage half tensor <
      okPolls (biasReadyObject l cta stage) ((X.tr g).take finish) :=
    hBudget.trans_le (hAlgebra.trans hPoll)
  have hMono := MbarRing.Poll.okPolls_mono (biasReadyObject l cta stage) (X.tr g)
    (i := finish) (j := (X.tr g).length) (by dsimp [finish]; omega)
  rw [List.take_length] at hMono
  obtain ⟨wait,hOwner,hObserve⟩ :=
    biasIssueObservedOfConsumerExtent hp hX hIssue hCta hw hStage (hBefore.trans_le hMono)
  exact biasNotificationFinishedOfObservation hX hOwner hExit hObserve

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
