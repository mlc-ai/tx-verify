-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreCompletion
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemConflictGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityScore
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringProbabilityAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaProbabilityParity
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.MBarrier Prologue Scores

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- A score MMA and an ordinary store sharing a probability cell issued in one CTA. -/
theorem probabilityOverlapIssuer (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {mma store : EvId} {cell : TcMma.Cell} (hStore : TcMma.StoreCell l X store cell)
    (hFoot : TensorStoreFootprint l store cell (.probability stage))
    (hOverlap : MmaAccumulatorOn X mma cell (.probability stage)) :
    ∃ d op acc mask, X.MmaIssue mma d op acc mask ∧ SameCta l mma.1 store.1 := by
  obtain ⟨block,frag,d,op,acc,mask,row,col,hBank,hQk,hCell⟩ := hOverlap
  have hOp := hQk.queryOperand hp hX
  have hOwner : cell.cta = mma.1/l.block := by
    rcases TcMma.resultCell_cta hCell with hLo | hHi
    · exact hLo.trans hOp.ctaLow
    · exact hHi.trans hOp.ctaHigh
  obtain ⟨_,_,_,_,⟨_,he⟩,_,_⟩ := hStore
  exact ⟨d,op,acc,mask,⟨_,hQk.decoded⟩,event_thread_lt hX hQk.decoded,
    event_thread_lt hX he,hOwner.symm.trans hFoot.cta⟩

/-- The last probability store of a softmax visit belongs to its tail packet. -/
@[no_expose] def TailProbabilityStore (X : Execution) (store : EvId) : Prop :=
  ∃ (round : Softmax.Round) (address : Nat) (values : List Value) (shape : TcShape),
    X.get store = some ⟨Softmax.probabilityPc round 3,.tc (.st address values shape)⟩

/-- The decoded tail packet store in an actual trace. -/
theorem TailProbabilityStore.decoded {X : Execution} {store : EvId}
    (h : TailProbabilityStore X store) :
    ∃ (round : Softmax.Round) (address : Nat) (values : List Value) (shape : TcShape),
      X.get store = some ⟨Softmax.probabilityPc round 3,.tc (.st address values shape)⟩ :=
  h

/-- A probability store's physical columns place it in exactly its early or tail packet. -/
theorem probabilityStorePacketOfCell (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {store : EvId} {cell : TcMma.Cell} {stage : Fin 2} (hStore : TcMma.StoreCell l X store cell)
    (hFoot : TensorStoreFootprint l store cell (.probability stage)) :
    (EarlyProbabilityStore X store ∧ cell.column < probabilityColumn stage+48) ∨
      (TailProbabilityStore X store ∧ probabilityColumn stage+48 ≤ cell.column) := by
  have hGroup := hFoot.warpGroup
  obtain ⟨address,vals,shape,j,⟨site,he⟩,hj,rfl⟩ := hStore
  obtain ⟨round,quarter,hSite⟩ : ∃ (round : Softmax.Round) (q : Fin 4),
      site = Softmax.probabilityPc round q := by
    rcases tensorStoreSite hX he with h | ⟨other,k,rfl⟩
    · exact h
    · have h := correctionStoreWarpGroup hp hX other k he
      change (store.1%l.block)/128 = stage.val at hGroup
      have := stage.isLt
      omega
  subst site
  obtain ⟨w,hWarp,rfl,hLen,rfl⟩ := Scores.probabilityStoreAddress hp hX round quarter he
  have hStage : Softmax.stageOf w = stage := by
    apply Fin.ext
    change (store.1%l.block)/128 = stage.val at hGroup
    change w.val/4 = stage.val
    rw [hWarp]
    unfold warpIndex
    omega
  rw [hStage] at he ⊢
  have hLimit := scoreColumn_range stage
  have hP := probabilityColumn_range stage
  have hQ := quarter.isLt
  have hCol : probabilityColumn stage+16*quarter.val < 512 := by omega
  unfold Softmax.probabilityAddress
  rw [tcDataCell_warp32 l store.1 j hCol]
  rw [hLen] at hj
  by_cases hLast : quarter = 3
  · subst quarter
    exact .inr ⟨⟨round,_,_,_,he⟩,by dsimp; omega⟩
  · have hEarly : quarter.val < 3 := by
      by_contra! h
      exact hLast (Fin.ext (by omega))
    exact .inl ⟨EarlyProbabilityStore.ofDecoded round quarter hEarly he,by dsimp; omega⟩

/-- For the early packet, the lane's current store generation is bounded by the
physical score waits already returned before that store. -/
theorem EarlyProbabilityStore.scoreUses (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {store : EvId} (stage : Fin 2)
    (hStore : EarlyProbabilityStore X store) (hStage : warpIndex l store.1 / 4 = stage.val) :
    let cta := store.1/l.block
    let object := scoreReadyObject l cta stage
    probabilityOrdinal l X cta stage 0 store + 1 ≤
      okPolls object ((X.tr store.1).take store.2) := by
  obtain ⟨g,j⟩ := store
  obtain ⟨r,q,address,values,shape,hEarly,he⟩ := hStore.decoded
  change warpIndex l g / 4 = stage.val at hStage
  have hWarp : warpIndex l g < 8 := by have := stage.isLt; omega
  obtain ⟨k,⟨site,kind⟩,parity,acq,scope,hGet,hKind,hCount,hResume⟩ :=
    softmaxProbabilityStoreScorePoll hp hX stage hWarp hStage r q he
  have hQ : q ≠ 3 := fun h => by subst q; exact (Nat.lt_irrefl 3) hEarly
  change kind = _ at hKind
  subst kind
  simp only [hQ,↓reduceIte] at hCount
  have hUse := MbarRing.Poll.okPoll_get hGet
  have hm := MbarRing.Poll.okPolls_mono (scoreReadyObject l (g/l.block) stage) (X.tr g)
    (show k+1 ≤ j from hResume.1.2.1)
  dsimp only
  rw [← hCount,← hUse]
  exact hm

/-- A joint credit at or beyond the local ordinal follows an earlier non-credit event. -/
theorem eventBeforeProbabilityCredit {l : Launch} {X : Execution}
    {source credit : EvId} {stage packet : Fin 2} {event : Event}
    (he : X.get source = some event)
    (hNotCredit : arrivesOn (probabilityObject l (source.1/l.block) stage packet) event = false)
    (hCredit : ProbabilityCredit l X credit (source.1/l.block) stage packet)
    (hLane : credit.1 = source.1)
    (hOrdinal : probabilityOrdinal l X (source.1/l.block) stage packet source ≤
      probabilityOrdinal l X (source.1/l.block) stage packet credit) :
    TraceBefore X source credit := by
  obtain ⟨g,i⟩ := source
  obtain ⟨h,j⟩ := credit
  change h = g at hLane
  subst h
  obtain ⟨site,hGet⟩ := hCredit
  have hBefore : i < j := by
    by_contra! hLe
    rcases Nat.eq_or_lt_of_le hLe with rfl | hLt
    · obtain rfl := Option.some.inj (he.symm.trans hGet)
      simp [arrivesOn,sourceArrive] at hNotCredit
    · let loc := probabilityObject l (g/l.block) stage packet
      have hm := countP_take_mono (arrivesOn loc) (X.tr g) (show j+1 ≤ i from hLt)
      change (X.tr g)[j]? = _ at hGet
      rw [List.take_add_one,hGet,Option.toList_some,List.countP_append] at hm
      have hHit : arrivesOn loc
          ⟨site,.arrive (probabilityObject l (g/l.block) stage packet) 0 1 true .cta⟩ = true := by
        simp [arrivesOn, sourceArrive, loc]
      rw [List.countP_singleton,ite_eq_left hHit] at hm
      change ((X.tr g).take j).countP (arrivesOn loc) + 1 ≤
        ((X.tr g).take i).countP (arrivesOn loc) at hm
      change ((X.tr g).take i).countP (arrivesOn loc) ≤
        ((X.tr g).take j).countP (arrivesOn loc) at hOrdinal
      omega
  exact ⟨rfl,hBefore,len_of_get hGet⟩

/-- A joint credit at the store's generation or later follows that store on its lane. -/
theorem tensorStoreBeforeProbabilityCredit {l : Launch} {X : Execution}
    {store credit : EvId} {stage packet : Fin 2} {address : Nat} {values : List Value}
    {shape : TcShape} (hStore : X.TSt store address values shape)
    (hCredit : ProbabilityCredit l X credit (store.1/l.block) stage packet)
    (hLane : credit.1 = store.1)
    (hOrdinal : probabilityOrdinal l X (store.1/l.block) stage packet store ≤
      probabilityOrdinal l X (store.1/l.block) stage packet credit) :
    TraceBefore X store credit := by
  obtain ⟨_,he⟩ := hStore
  exact eventBeforeProbabilityCredit he rfl hCredit hLane hOrdinal

/-- A joint credit at the store's generation or later follows that store on its lane. -/
theorem EarlyProbabilityStore.beforeCredit {l : Launch} {X : Execution}
    {store credit : EvId} {stage : Fin 2} (hStore : EarlyProbabilityStore X store)
    (hCredit : ProbabilityCredit l X credit (store.1/l.block) stage 0)
    (hLane : credit.1 = store.1)
    (hOrdinal : probabilityOrdinal l X (store.1/l.block) stage 0 store ≤
      probabilityOrdinal l X (store.1/l.block) stage 0 credit) :
    TraceBefore X store credit := by
  obtain ⟨round,quarter,address,values,shape,hEarly,he⟩ := hStore.decoded
  exact tensorStoreBeforeProbabilityCredit ⟨_,he⟩ hCredit hLane hOrdinal

/-- An actual score commit no later than an MMA in its CTA contributes one count
to that MMA's earlier-score cursor. -/
theorem scoreCommitCountBeforeMma (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {mma commit : EvId} {d cta : Nat} {stage : Fin 2} {op : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {spec : TcCommit.Spec} {rank : Fin 16} (hIssue : X.MmaIssue mma d op acc mask)
    (hScore : ScoreCommit l X commit cta stage spec rank) (hCta : mma.1/l.block = cta)
    (hLater : commit.2 ≤ mma.2) :
    scoreCommitOrdinal l X cta stage commit + 1 ≤
      scoreCommitOrdinal l X cta stage mma := by
  have hLane := mmaAndScoreCommitSameThread hp hX hIssue hScore hCta
  obtain ⟨g,i⟩ := mma
  obtain ⟨h,j⟩ := commit
  change g = h at hLane
  subst h
  obtain ⟨rfl,hScore⟩ := scoreCommitRankZero hp hX hScore
  obtain ⟨⟨site,hGet⟩,hTarget⟩ := hScore
  obtain ⟨_,hMma⟩ := hIssue
  have hStrict : j < i := by
    rcases Nat.eq_or_lt_of_le hLater with hh | hh
    · change j = i at hh
      subst j
      have h := congrArg Event.kind (Option.some.inj (hMma.symm.trans hGet))
      exact (TcKind.noConfusion (Kind.tc.inj h))
    · exact hh
  let mark := scoreCommitOn (scoreReadyObject l cta stage)
  have hCount := countP_take_mono mark (X.tr g) (show j+1 ≤ i from hStrict)
  change (X.tr g)[j]? = _ at hGet
  rw [List.take_add_one,hGet,Option.toList_some,List.countP_append,List.countP_singleton] at hCount
  have hMark : mark ⟨site,.tc (.commit spec)⟩ = true := by simpa [mark,scoreCommitOn] using hTarget
  rw [ite_eq_left hMark] at hCount
  exact hCount

/-- The MMA lane's successful probability poll observes a physical phase at
least as large as the number of its preceding successful polls of this packet. -/
theorem probabilityAcquireRecord (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {wait : EvId} {cta : Nat} {stage packet : Fin 2}
    (h : ∃ e parity, X.get wait = some e ∧
      e.kind = .wait (probabilityObject l cta stage packet) parity true true .cta) :
    let obj := probabilityObject l cta stage packet
    ∃ (index phase : Nat) (poll : Record Ref), (X.objects obj)[index]? = some poll ∧
      poll.id = .thread wait ∧ poll.reply.waited = some true ∧
      observedAt (X.objects obj) index = some phase ∧
      okPolls obj ((X.tr wait.1).take wait.2) ≤ phase := by
  let obj := probabilityObject l cta stage packet
  let log := X.objects obj
  obtain ⟨j,e⟩ := wait
  obtain ⟨⟨source,kind⟩,parity,hGet,hKind⟩ := h
  change kind = _ at hKind
  subst kind
  let n := okPolls obj ((X.tr j).take e)
  have hNth := MbarRing.Poll.nth_eq hGet
  have hN : n < okPolls obj (X.tr j) := by
    apply MbarRing.Poll.nth_present.mp
    rw [hNth]
    exact ⟨_,hGet⟩
  have hClean : ∀ r ∈ log, (∃ q ok, r.action = .pollParity q ok) → r.fault = none :=
    fun _ hr hPoll => actualInitOrPollClean hp hX hr (.inr hPoll)
  obtain ⟨i,r,_,hr,hId,_,hOk,_,hIndex⟩ := MbarRing.Poll.record hX hClean hN
  dsimp only [n] at hId
  rw [hNth] at hId
  have hCheck := X.objects_checked hX obj
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) obj
  have hAlt := probabilitySelectedAlternates hp hX (cta := cta) (g := j) stage packet
  have hSelected := objectThreadSelected_iff.mpr ⟨_,hId⟩
  obtain ⟨st,hs,hLower,_⟩ :=
    hCheck.selected_poll_phase_ge hNo (objectThreadSelected j) (by decide) hAlt hr hSelected hOk
  obtain ⟨u,_,hu,_,_,hCompleted⟩ := hCheck.okPoll hr hOk
  have hEq : u = st := Option.some.inj (hu.symm.trans hs)
  subst u
  have hPositive : 0 < st.phase := by omega
  have hSeen : observedAt log i = some (st.phase-1) := by
    change (log[i]?).bind (·.reply.completed) = _
    rw [hr,Option.bind_some,hCompleted,ite_eq_left hPositive]
  change selectedBefore (objectThreadSelected j) log i = n at hIndex
  change selectedBefore (objectThreadSelected j) log i + 1 ≤ st.phase + 0 at hLower
  rw [hIndex,Nat.add_zero] at hLower
  exact ⟨i,st.phase-1,r,hr,hId,hOk,hSeen,by change n ≤ _; omega⟩

/-- The returning probability acquire observes a real packet phase covering
the MMA's earlier-score cursor. -/
theorem MmaProbabilityAcquire.record (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {mma wait : EvId} {stage packet : Fin 2} (h : MmaProbabilityAcquire l X mma stage packet wait) :
    let cta := mma.1/l.block
    let obj := probabilityObject l cta stage packet
    ∃ (index phase : Nat) (poll : Record Ref), (X.objects obj)[index]? = some poll ∧
      poll.id = .thread wait ∧ poll.reply.waited = some true ∧
      observedAt (X.objects obj) index = some phase ∧
      scoreCommitOrdinal l X cta stage mma ≤ phase+1 := by
  obtain ⟨i,phase,r,hr,hId,hOk,hSeen,hPhase⟩ :=
    probabilityAcquireRecord hp hX h.event
  exact ⟨i,phase,r,hr,hId,hOk,hSeen,h.coversScores.trans (Nat.add_le_add_right hPhase 1)⟩

end PTX.Kernels.TmlFa4Fwd.Thread
