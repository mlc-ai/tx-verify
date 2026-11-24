-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitActors
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Lemmas.Flow.ElectActor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.MBarrier PTX.TcMma Prologue

/-- A returning probability-store guard acquires the score object at CTA scope. -/
def ScoreAcquire (X : Execution) (wait : EvId) (object : Loc) : Prop :=
  ∃ e q, X.get wait = some e ∧ e.kind = .wait object q true true .cta

/-- The successful wait represented by a score acquire observes the same update
as its object-history observation. -/
theorem ScoreAcquire.observes {X : Execution} {wait : EvId} {object : Loc} {x : Ref}
    (hAcquire : ScoreAcquire X wait object) (hObserved : MbarObserved X x (.thread wait)) :
    WaitObserves X x wait object true .cta := by
  obtain ⟨_, other, loc, acq, scope, hId, hObserve, _⟩ := hObserved
  have hSame := Ref.thread.inj hId
  subst other
  obtain ⟨e,q,he,hKind⟩ := hAcquire
  obtain ⟨_,_,hGet⟩ := hObserve.1
  have h := congrArg Event.kind (Option.some.inj (he.symm.trans hGet))
  rw [hKind] at h
  obtain ⟨rfl,_,_,rfl,rfl⟩ := Kind.wait.inj h
  exact hObserve

/-- The actual store guard is the last successful score wait before the store. -/
theorem probabilityStoreScoreRecordWithCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {store : EvId} {cell : Cell} (stage : Fin 2)
    (hStore : StoreCell l X store cell)
    (hFootprint : TensorStoreFootprint l store cell (.probability stage)) :
    let object := scoreReadyObject l (store.1/l.block) stage
    ∃ (wait : EvId) (index phase : Nat) (r : Record Ref), (X.objects object)[index]? = some r ∧
      r.id = .thread wait ∧ r.reply.waited = some true ∧
      observedAt (X.objects object) index = some phase ∧
      ScoreAcquire X wait object ∧ Resumes kernel X wait store ∧
      okPolls object ((X.tr store.1).take store.2) ≤ phase + 1 ∧
      0 < okPolls object ((X.tr store.1).take store.2) ∧
      let ordinal := okPolls object ((X.tr store.1).take store.2)-1
      ordinal < okPolls object (X.tr store.1) ∧
      wait = (store.1,MbarRing.Poll.nth X object store.1 ordinal) := by
  obtain ⟨address,vals,shape,_,⟨site,he⟩,_,_⟩ := hStore
  have hGroup := hFootprint.warpGroup
  obtain ⟨round,quarter,hSite⟩ : ∃ (round : Softmax.Round) (q : Fin 4),
      site = Softmax.probabilityPc round q := by
    rcases tensorStoreSite hX he with h | ⟨other,chunk,rfl⟩
    · exact h
    · have h := correctionStoreWarpGroup hp hX other chunk he
      change store.1%l.block/128 = stage.val at hGroup
      have := stage.isLt
      omega
  subst site
  obtain ⟨g,j⟩ := store
  change g%l.block/128 = stage.val at hGroup
  have hStage : warpIndex l g/4 = stage.val := by unfold warpIndex; omega
  have hWarp : warpIndex l g < 8 := by have := stage.isLt; omega
  let object := scoreReadyObject l (g/l.block) stage
  let log := X.objects object
  obtain ⟨first,ev,q',acq',sc',hFirst,hFirstKind,_,hPrior⟩ :=
    softmaxProbabilityStoreScorePoll hp hX stage hWarp hStage round quarter he
  have hPositiveBudget : 0 < okPolls object ((X.tr g).take j) := by
    have hMark : okPoll object ev = true := by
      simp [okPoll,sourceWaitSuccess,hFirstKind,object]
    apply List.countP_pos_iff.mpr
    exact ⟨ev,List.mem_of_getElem? ((List.getElem?_take_of_lt hPrior.1.2.1).trans hFirst),
      hMark⟩
  let n := okPolls object ((X.tr g).take j)-1
  have hN : n+1 = okPolls object ((X.tr g).take j) := by dsimp [n]; omega
  obtain ⟨k,source,q,acq,scope,hK,hGet,hOrdinal⟩ :=
    MbarRing.Poll.exists_nth hN.le
  obtain ⟨rfl,rfl⟩ := successfulScoreWaitIsAcquire hp hX stage hWarp hGet
  obtain ⟨exit,hSpin⟩ := actualCanonicalPoll hX hGet
  have hTrace : TraceBefore X (g,k) (g,j) := ⟨rfl,hK,len_of_get he⟩
  have hResumes : Resumes kernel X (g,k) (g,j) := by
    refine ⟨hTrace,?_⟩
    simp only [hGet,Option.map_some,Kind.resume]
    exact ⟨source,exit,object,q,true,.cta,hGet,hSpin,hTrace⟩
  have hNth := MbarRing.Poll.nth_eq hGet
  have hn : n < okPolls object (X.tr g) := by
    rw [← hOrdinal]
    apply MbarRing.Poll.nth_present.mp
    rw [hNth]
    exact ⟨_,hGet⟩
  have hClean : ∀ r ∈ log, (∃ p ok, r.action = .pollParity p ok) → r.fault = none :=
    fun _ hr hPoll => actualInitOrPollClean hp hX hr (.inr hPoll)
  obtain ⟨i,r,_,hr,hId,_,hSuccess,_,hIndex⟩ := MbarRing.Poll.record hX hClean hn
  rw [← hOrdinal,hNth] at hId
  have hChecked := X.objects_checked hX object
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) object
  have hAlt := scoreReadySelectedAlternates hp hX stage hWarp rfl hStage
  have hSel := objectThreadSelected_iff.mpr ⟨_,hId⟩
  obtain ⟨st,hState,hLower,_⟩ :=
    hChecked.selected_poll_phase_ge hNo (objectThreadSelected g) (by decide) hAlt hr hSel hSuccess
  have hPositive : 0 < st.phase := by omega
  obtain ⟨st',_,hState',_,_,hCompleted⟩ := hChecked.okPoll hr hSuccess
  have hEq : st' = st := Option.some.inj (hState'.symm.trans hState)
  subst st'
  have hPhase : observedAt log i = some (st.phase-1) := by
    change (log[i]?).bind (·.reply.completed) = _
    rw [hr,Option.bind_some,hCompleted,ite_eq_left hPositive]
  change selectedBefore _ _ i = n at hIndex
  have hBound : okPolls object ((X.tr g).take j) ≤ (st.phase-1)+1 := by omega
  have hAt : MbarRing.Poll.nth X object g n = k := by rwa [← hOrdinal]
  exact ⟨(g,k),i,st.phase-1,r,hr,hId,hSuccess,hPhase,⟨_,_,hGet,rfl⟩,hResumes,hBound,
    hPositiveBudget,hn,congrArg (g, ·) hAt.symm⟩


/-- Every actual probability store follows a successful score acquire and its physical
record for its latest score guard, including stores in an unfinished output-packet visit. -/
theorem probabilityStoreScoreRecord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {store : EvId} {cell : Cell} (stage : Fin 2)
    (hStore : StoreCell l X store cell)
    (hFootprint : TensorStoreFootprint l store cell (.probability stage)) :
    let object := scoreReadyObject l (store.1/l.block) stage
    ∃ (wait : EvId) (index phase : Nat) (r : Record Ref), (X.objects object)[index]? = some r ∧
      r.id = .thread wait ∧ r.reply.waited = some true ∧
      observedAt (X.objects object) index = some phase ∧
      ScoreAcquire X wait object ∧ Resumes kernel X wait store ∧
      okPolls object ((X.tr store.1).take store.2) ≤ phase + 1 := by

  obtain ⟨wait,i,phase,r,hR,hId,hSuccess,hPhase,hAcquire,hResume,hBound,_⟩ :=
    probabilityStoreScoreRecordWithCursor hp hX stage hStore hFootprint
  exact ⟨wait,i,phase,r,hR,hId,hSuccess,hPhase,hAcquire,hResume,hBound⟩

/-- The elected MMA issuer is also the issuer of the score commit in that CTA. -/
theorem mmaAndScoreCommitSameThread {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i commit : EvId} {d cta : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    {spec : TcCommit.Spec} {stage : Fin 2} {rank : Fin 16}
    (hMma : X.MmaIssue i d op acc mask) (hScore : ScoreCommit l X commit cta stage spec rank)
    (hCta : i.1/l.block = cta) : i.1 = commit.1 := by
  obtain ⟨hw,k,site,inst,leader,he,hSelected⟩ := mmaIssueElection hp hX hMma
  obtain ⟨hCommit,hWarp,j,source,occ,hElect⟩ := scoreCommitActor hp hX hScore
  obtain ⟨_,hi⟩ := hMma
  obtain ⟨_,hc⟩ := hScore.1
  have hBoth : SameWarp l i.1 commit.1 :=
    ⟨⟨event_thread_lt hX hi,event_thread_lt hX hc,hCta.trans hCommit.symm⟩,hw.trans hWarp.symm⟩
  exact selected_elect_thread_unique hX.elect
    (e := (i.1,k)) (f := (commit.1,j)) he hElect hBoth hSelected rfl

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
