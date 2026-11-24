-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Correction
public import Kernels.TmlFa4Fwd.Proof.CorrectionReadySources
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputSourceLane
public import Kernels.TmlFa4Fwd.Proof.MbarAddressClosure
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Lemmas.Flow.TcTmpl
public import Lemmas.TensorStore.TensorStoreThread
public import Lemmas.Flow.BulkCount
public import Mathlib.Data.List.NodupEquivFin
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionOutputReadyTrace
import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands
import Kernels.TmlFa4Fwd.Proof.MbarRecordOwner

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX PTX.Flow PTX.Proof Prologue Epilogue AsyncCopy

noncomputable section

private def readyInitializer (stage : Fin 2) : Fin 34 := ⟨26 + stage.val, by omega⟩

private theorem readyInitializerAddress (l : Launch) (g : Nat) (stage : Fin 2) :
    initObject l (g / l.block) (readyInitializer stage) = readyLoc l g stage := by
  fin_cases stage <;> rfl

private theorem readyPollRecord {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {stage : Fin 2} (hWait : ReadyAcquire l X issue stage) :
    ∃ record, record ∈ X.objects (readyLoc l issue.1 stage) := by
  obtain ⟨j, _, hj⟩ := hWait
  have hAction : objectAction X X.async (readyLoc l issue.1 stage) (.thread (issue.1, j)) =
      some (.pollParity 0 true) := by
    simp only [objectAction, hj, ↓reduceIte]
  obtain ⟨record, hMember, _⟩ := (hX.tma.2.2.1 _).2.2 _ _ hAction
  exact ⟨record, hMember⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem outputReadyInitialized {g : Nat} {stage : Fin 2} {record : MBarrier.Record Ref}
    (hMember : record ∈ X.objects (readyLoc l g stage)) :
    PairTmaRing.InitFirst X (readyLoc l g stage) 128 := by
  rw [← readyInitializerAddress] at hMember
  have hInit := (activeObjectHistory hp hX (readyInitializer stage) hMember).1
  have hCount : (initSite (readyInitializer stage)).count = 128 :=
    (by decide : ∀ s : Fin 2, (initSite (readyInitializer s)).count = 128) stage
  rwa [readyInitializerAddress, hCount] at hInit

private theorem tensorDoesNotNotifyReady {i : EvId} {addr g : Nat} {spec : TensorCopy.Spec}
    (stage : Fin 2) (hIssue : X.TensorIssue i addr spec) : spec.mbar ≠ readyLoc l g stage := by
  intro hTarget
  obtain ⟨_, he⟩ := hIssue
  obtain ⟨site, rfl⟩ := Loader.actualInputIssuePc hX he
  have hLoc := Loader.loaderTensorOffset hp hX site he
  have audit : ∀ (j : Fin 14) (s : Fin 2),
      Loader.inputBarrierBase j + (Loader.inputSite j).barrierOffset ≠ 208 + 8 * s.val := by
    decide
  have hEq := congrArg Loc.addr (hTarget.symm.trans hLoc)
  change l.sharedBase + (208 + 8 * stage.val) =
    l.sharedBase + (Loader.inputBarrierBase site + (Loader.inputSite site).barrierOffset) at hEq
  exact audit site stage (by omega)

private theorem noCopyArrivalOnReady {i : EvId} {g : Nat} (stage : Fin 2) (noinc : Bool) :
    ¬ X.AsyncArrive i (readyLoc l g stage) noinc := by
  rintro ⟨site, he⟩
  obtain ⟨⟨packet, rfl⟩, hMode, _, _⟩ := Loader.actualAsyncArrival hX he
  subst noinc
  have hSite := (by decide : ∀ q : Fin 6,
    Loader.copyCommitPc q + 1 ∈ [674, 904, 1137, 1342, 1602, 1735]) packet
  obtain ⟨off, hOff, hLoc⟩ := Loader.loaderAsyncAddress hp hX he hSite
  have hAddress := congrArg Loc.addr hLoc
  change l.sharedBase + (208 + 8 * stage.val) = l.sharedBase + off at hAddress
  have hBounds : off ≤ 48 := (by decide : ∀ n ∈ [32, 40, 48], n ≤ 48) off hOff
  omega

/-- Actual ready polls see the one-shot arrival history once its ordinary arrival sites are
matched to the correction lanes. Every other field is fixed by actual operand provenance. -/
private theorem outputReadySourcesOfActualArrivals {issue : EvId} {stage : Fin 2} {pos : Nat → Nat}
    {record : MBarrier.Record Ref} (hRecord : record ∈ X.objects (readyLoc l issue.1 stage))
    (hArrivals : ∀ i site tx count rel scope, X.get i = some
      ⟨site, .arrive (readyLoc l issue.1 stage) tx count rel scope⟩ →
        ∃ lane < 128, i = (sourceLane l issue lane, pos lane) ∧ tx = 0 ∧ count = 1)
    (hKind : ∀ lane < 128, ∀ e, X.get (sourceLane l issue lane, pos lane) = some e →
      e.kind = .arrive (readyLoc l issue.1 stage) 0 1 true .cta) :
    OutputReadySources l X issue.1 stage pos where
  initialized := outputReadyInitialized hp hX hRecord
  arrival := by
    intro i site tx count rel scope he
    obtain ⟨lane, hl, hLane, hTx, hCount⟩ := hArrivals i site tx count rel scope he
    exact ⟨lane, hl, congrArg Ref.thread hLane, hTx, hCount⟩
  arrivalKind := hKind
  poll := fun _ _ _ _ _ _ he => outputReadyPollParity hp hX stage he rfl
  tensor := fun _ _ _ => tensorDoesNotNotifyReady hp hX stage
  copyArrive := fun _ => noCopyArrivalOnReady hp hX stage
  commit := by
    intro i s rank ⟨_, he⟩ hTarget
    exact commitExcludesOutputReady hp hX stage he hTarget rfl

/-- Every correction row has a unique ready publication, located by its actual trace identity. -/
private theorem actualOutputReadyHistoryOfRecord {issue : EvId} {stage : Fin 2}
    {record : MBarrier.Record Ref} (hRecord : record ∈ X.objects (readyLoc l issue.1 stage)) :
    ∃ pos : Nat → Nat, OutputReadySources l X issue.1 stage pos ∧
      ∀ lane < 128, ∀ j, CorrectionReady X (sourceLane l issue lane, j) stage → j = pos lane := by
  classical
  let pos (lane : Nat) : Nat :=
    if h : ∃ j, CorrectionReady X (sourceLane l issue lane, j) stage then Classical.choose h
    else (X.tr (sourceLane l issue lane)).length
  have matchPosition (lane j : Nat) (h : CorrectionReady X (sourceLane l issue lane, j) stage) :
      j = pos lane := by
    have hEx : ∃ j, CorrectionReady X (sourceLane l issue lane, j) stage := ⟨j, h⟩
    simp only [pos, dite_eq_left hEx]
    exact h.unique hp hX (Classical.choose_spec hEx)
  have sameCta (i : EvId) (hLoc : readyLoc l issue.1 stage = readyLoc l i.1 stage) :
      i.1 / l.block = issue.1 / l.block := congrArg Loc.cta hLoc.symm
  refine ⟨pos, outputReadySourcesOfActualArrivals hp hX hRecord ?_ ?_,
    fun lane _ j => matchPosition lane j⟩
  · intro i site tx count rel scope he
    have hSite := actualOutputReadyArrivalSite hp hX stage he rfl
    obtain ⟨hReady, hLo, hHi⟩ := CorrectionReady.ofActualArrival hp hX stage (hSite ▸ he)
    have hEvent := Option.some.inj (he.symm.trans (hReady.decoded hp hX))
    have hKind := Kind.arrive.inj (congrArg Event.kind hEvent)
    have hc := sameCta _ hKind.1
    let lane := i.1 % l.block - 256
    have hLane : lane < 128 ∧ sourceLane l issue lane = i.1 := by
      have hParts := Nat.div_add_mod i.1 l.block
      unfold warpIndex at hLo hHi
      unfold sourceLane lane
      rw [hp.block] at *
      omega
    have hObs : CorrectionReady X (sourceLane l issue lane, i.2) stage := by
      rwa [hLane.2, Prod.mk.eta]
    exact ⟨lane, hLane.1, Prod.ext hLane.2.symm (matchPosition lane i.2 hObs),
      hKind.2.1, hKind.2.2.1⟩
  · intro lane hl e he
    dsimp only [pos] at he
    split at he
    · rename_i hEx
      have hReady := (Classical.choose_spec hEx).decoded hp hX
      have hEq := congrArg Event.kind (Option.some.inj (he.symm.trans hReady))
      have hOwner : sourceLane l issue lane / l.block = issue.1 / l.block := by
        unfold sourceLane
        rw [hp.block]
        omega
      simpa only [readyLoc, hOwner] using hEq
    · have hIndex : (X.tr (sourceLane l issue lane)).length <
          (X.tr (sourceLane l issue lane)).length := (List.getElem?_eq_some_iff.mp he).1
      exact (Nat.lt_irrefl _ hIndex).elim


/-- The successful acquire sees the actual correction rows of its one-shot object. -/
theorem actualOutputReadyHistory {issue : EvId} {stage : Fin 2}
    (hWait : ReadyAcquire l X issue stage) :
    ∃ pos : Nat → Nat, OutputReadySources l X issue.1 stage pos ∧
      ∀ lane < 128, ∀ j, CorrectionReady X (sourceLane l issue lane, j) stage → j = pos lane := by
  obtain ⟨record, hRecord⟩ := readyPollRecord hX hWait
  exact actualOutputReadyHistoryOfRecord hp hX (issue := issue) hRecord

/-- Every record of an output-ready object is clean, including in prefixes with no O issue. -/
theorem outputReadyHistoryClean {g : Nat} {stage : Fin 2} {record : MBarrier.Record Ref}
    (hRecord : record ∈ X.objects (readyLoc l g stage)) : record.fault = none := by
  obtain ⟨_, hSources, _⟩ := actualOutputReadyHistoryOfRecord hp hX (issue := (g, 0)) hRecord
  exact (Epilogue.outputReadyHistory hX hSources).fault_free hX hRecord

/-- A successful ready poll has a publication from each correction row. -/
theorem actualReadyIncludesEveryRow {issue : EvId} {stage : Fin 2}
    (hReady : ReadyAcquire l X issue stage) {lane : Nat} (hl : lane < 128) :
    ∃ pub, CorrectionReady X (sourceLane l issue lane, pub) stage := by
  obtain ⟨pos, hSrc, _⟩ := actualOutputReadyHistory hp hX hReady
  obtain ⟨wait, _, he⟩ := hReady
  have hObserve := readyWaitObserves hX hSrc he hl
  obtain ⟨i, _, record, _, _, hr, hId, _⟩ := hObserve.2
  have hrMem := List.mem_of_getElem? hr
  have hAction := ((hX.tma.2.2.1 (readyLoc l issue.1 stage)).2.1 record hrMem).1
  rw [hId] at hAction
  change objectAction X X.async (readyLoc l issue.1 stage)
    (.thread (sourceLane l issue lane, pos lane)) = some record.action at hAction
  cases hGet : X.get (sourceLane l issue lane, pos lane) with
  | none => simp [objectAction, hGet] at hAction
  | some e =>
    have hk := hSrc.arrivalKind lane hl e hGet
    have hE : X.get (sourceLane l issue lane, pos lane) = some
        ⟨e.pc, .arrive (readyLoc l issue.1 stage) 0 1 true .cta⟩ := by
      cases e
      simp_all
    have hSite := actualOutputReadyArrivalSite hp hX stage hE rfl
    exact ⟨pos lane, (CorrectionReady.ofActualArrival hp hX stage (hSite ▸ hE)).1⟩

/-- The actual ready observation carries all same-stage writes by the publishing correction lane
through its shared proxy fence to the issuing warp. -/
theorem actualStagingPublication {issue : EvId} {addr : Nat} {spec : TensorStore.Spec}
    (hIssue : X.TensorStoreIssue issue addr spec) {lane stageWrite publication : Nat}
    {stage : Fin 2} (hLane : lane < 128) {a : Acc} {bytes : List Byte}
    (hReady : ReadyAcquire l X issue stage)
    (hPub : CorrectionReady X (sourceLane l issue lane, publication) stage)
    (hStage : StageStagingWrite X (sourceLane l issue lane, stageWrite) stage a bytes) :
    let g := sourceLane l issue lane
    ∃ fence wait, Staging.Publish l X (g, stageWrite) (g, fence) (g, publication)
      (issue.1, wait) issue (readyLoc l g stage) := by
  let g := sourceLane l issue lane
  obtain ⟨pos, hSource, hPosition⟩ := actualOutputReadyHistory hp hX hReady
  obtain ⟨wait, hWaitBefore, hWait⟩ := hReady
  have hSame : g / l.block = issue.1 / l.block := by
    unfold g sourceLane
    rw [hp.block]
    omega
  have hTarget : readyLoc l g stage = readyLoc l issue.1 stage := by simp only [readyLoc, hSame]
  have hObserve := readyWaitObserves hX hSource hWait hLane
  change WaitObserves X (.thread (g, pos lane)) (issue.1, wait) (readyLoc l issue.1 stage)
    true .cta at hObserve
  rw [← hPosition lane hLane publication hPub, ← hTarget] at hObserve
  obtain ⟨fence, hFenceOrder, hFence, hPast⟩ := hPub.stagingBeforeFence hp hX
  obtain ⟨fenceSite, hFence⟩ := hFence
  have hWritten := hPast hStage
  have hg := event_thread_lt hX hFence
  obtain ⟨_, hIssue⟩ := hIssue
  have hi := event_thread_lt hX hIssue
  have hScopes : ScopesMeet l .cta g .cta issue.1 :=
    ⟨⟨hg, hi, hSame⟩, ⟨hi, hg, hSame.symm⟩⟩
  have hOrder : po X (g, stageWrite) (g, fence) := by
    change X.get (g, fence) = _ at hFence
    exact ⟨rfl, hWritten.2.1, hWritten.2.2, by simp [SameAccess, hFence, Event.acc]⟩
  refine ⟨fence, wait, ⟨⟨fenceSite, hFence⟩, hg, .single (.inl hOrder),
    ⟨.cta, ⟨0, 1, _, hPub.decoded hp hX⟩, .cta, hObserve, hScopes⟩,
    ⟨rfl, hFenceOrder.2.1.le⟩, ⟨rfl, hWaitBefore, len_of_get hIssue⟩,
    ⟨hg, hi, congrArg l.clusterOfCta hSame⟩⟩⟩


/-- All 128 actual correction publications leave the ready object in phase one. -/
theorem finalReadyPhaseOfPublications {g : Nat} (stage : Fin 2)
    (hPublished : ∀ lane < 128, ∃ j, CorrectionReady X (sourceLane l (g,0) lane,j) stage) :
    ∃ s, MBarrier.stateBefore (X.objects (readyLoc l g stage))
      (X.objects (readyLoc l g stage)).length = some s ∧ s.phase = 1 := by
  have hCta (lane : Nat) (hl : lane < 128) :
      sourceLane l (g,0) lane / l.block = g / l.block := by
    unfold sourceLane
    rw [hp.block]
    omega
  have hRecords (lane : Nat) (hl : lane < 128) :
      ∃ j, CorrectionReady X (sourceLane l (g,0) lane,j) stage ∧
        ∃ r ∈ X.objects (readyLoc l g stage), r.id = .thread (sourceLane l (g,0) lane,j) := by
    obtain ⟨j,hPub⟩ := hPublished lane hl
    have hGet := hPub.decoded hp hX
    have hKind : readyLoc l (sourceLane l (g,0) lane) stage = readyLoc l g stage := by
      unfold readyLoc
      rw [hCta lane hl]
    rw [hKind] at hGet
    have hAction : objectAction X X.async (readyLoc l g stage)
        (.thread (sourceLane l (g,0) lane,j)) = some (.arrive 1 0) := by
      simp only [objectAction,hGet,↓reduceIte]
    exact ⟨j,hPub,(hX.tma.2.2.1 _).2.2 _ _ hAction⟩
  obtain ⟨_,_,r,hMem,_⟩ := hRecords 0 (by decide)
  obtain ⟨pos,hSources,hPositions⟩ :=
    actualOutputReadyHistoryOfRecord hp hX (issue := (g,0)) hMem
  obtain ⟨s,hState,_,hDone⟩ := (Epilogue.outputReadyHistory hX hSources).final_state hX
    (fun hNil => by rw [hNil] at hMem; cases hMem)
  refine ⟨s,hState,hDone.mpr ⟨?_,by simp⟩⟩
  intro a ha
  obtain ⟨lane,hl,rfl⟩ := List.mem_map.mp ha
  have hl' := List.mem_range.mp hl
  obtain ⟨j,hPub,r,hMem,hId⟩ := hRecords lane hl'
  obtain rfl := hPositions lane hl' j hPub
  exact ⟨r,hMem,hId⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Output
