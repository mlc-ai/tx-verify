-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleStatisticsPublication
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalOccurrence
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedPublicationPositions
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxProbabilityGate
import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Flow.Code.Part068
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Lemmas.Flow.TcTmpl
import Lemmas.Flow.CountTake
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreReadyUpdate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Softmax Prologue

private def pendingEarly (site : Nat) : Bool :=
  decide ((4397 < site ∧ site ≤ 4847) ∨ (5683 < site ∧ site ≤ 6532) ∨
    (6891 < site ∧ site ≤ 7437))

private def statisticsMark (pc : Nat) : Bool := scoredStatisticsMark ⟨pc,.exit⟩
private def probabilityMark (pc : Nat) : Bool := earlyProbabilityMark ⟨pc,.exit⟩

private def earlyRankCode (pc : Nat) (i : Instr) : Bool :=
  (!(statisticsMark pc || probabilityMark pc) || (i.guard.isNone && !i.op.isLocal)) &&
  match i.op with
  | .bra target _ => pendingEarly target == pendingEarly pc
  | .brx .. => false
  | _ => true

private theorem earlyRankCodeAt {site : Nat} {i : Instr} (hc : kernel.code[site]? = some i) :
    earlyRankCode site i = true := by
  have hAll : (kernel.code.zipIdx 0).all (fun (ins,pc) => earlyRankCode pc ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i,site)
  apply List.mem_of_getElem? (i := site)
  simp only [List.getElem?_zipIdx,hc,Option.map_some,Nat.zero_add]

private theorem earlyRankSegment {site : Nat} {m : SegMatch CuteSlot}
    (hs : site ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel site = some m) :
    pendingEarly m.stop = pendingEarly site := by
  have hAll : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => pendingEarly seg.stop == pendingEarly site
      | none => false) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAll site hs
  rwa [hm,beq_iff_eq] at h

private theorem pendingEarlyNext (pc : Nat) :
    (pendingEarly (pc+1)).toNat + (probabilityMark pc).toNat =
      (pendingEarly pc).toNat + (statisticsMark pc).toNat := by
  by_cases hMark : pc = 4397 ∨ pc = 4847 ∨ pc = 5683 ∨ pc = 6532 ∨
      pc = 6891 ∨ pc = 7437
  · rcases hMark with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hStats : statisticsMark pc = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    simp [statisticsMark,scoredStatisticsMark] at h
    exact hMark (by tauto)
  have hEarly : probabilityMark pc = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    simp [probabilityMark,earlyProbabilityMark] at h
    exact hMark (by tauto)
  have hNext : pendingEarly (pc+1) = pendingEarly pc := by
    apply decide_eq_decide.mpr
    push Not at hMark
    omega
  rw [hStats,hEarly,hNext]

private theorem markedEarlyProgress {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (he : EStep kernel Assumptions.all l g s e (some u))
    (hMark : statisticsMark s.pc = true ∨ probabilityMark s.pc = true) :
    u.pc = s.pc+1 := by
  rcases hMark with hStat | hProb
  · have hStat : s.pc ∈ [4397,5683,6891] := List.contains_iff_mem.mp hStat
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hStat
    rcases hStat with h | h | h
    · exact followsMarkedBarrier h Flow.code_4397 rfl he
    · exact followsMarkedBarrier h Flow.code_5683 rfl he
    · exact followsMarkedBarrier h Flow.code_6891 rfl he
  · have hProb : s.pc ∈ [4847,6532,7437] := List.contains_iff_mem.mp hProb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hProb
    obtain ⟨i,hCode,_,hFire⟩ := estep_event_source he
    rcases hProb with h | h | h
    · rw [h,Flow.code_4847] at hCode
      obtain rfl := Option.some.inj hCode
      exact congrArg TState.pc (fires_arrive_state hFire).1
    · rw [h,Flow.code_6532] at hCode
      obtain rfl := Option.some.inj hCode
      exact congrArg TState.pc (fires_arrive_state hFire).1
    · rw [h,Flow.code_7437] at hCode
      obtain rfl := Option.some.inj hCode
      exact congrArg TState.pc (fires_arrive_state hFire).1

private theorem earlyRankStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    (pendingEarly u.pc).toNat + ev.toList.countP earlyProbabilityMark =
      (pendingEarly s.pc).toNat + ev.toList.countP scoredStatisticsMark := by
  rcases hStep with ⟨rfl,hLocal⟩ | ⟨e,rfl,hStep⟩
  · obtain ⟨i,hCode,_,hCase⟩ := tauScoreSource hLocal
    have hAudit := earlyRankCodeAt hCode
    simp only [earlyRankCode,Bool.and_eq_true] at hAudit
    have hUnmarked : statisticsMark s.pc = false ∧ probabilityMark s.pc = false := by
      by_cases h : statisticsMark s.pc = true ∨ probabilityMark s.pc = true
      · have hS : (statisticsMark s.pc || probabilityMark s.pc) = true :=
          Bool.or_eq_true_iff.mpr h
        have hGuards := hAudit.1
        rw [hS] at hGuards
        obtain ⟨hGuard,hNonLocal⟩ : i.guard = none ∧ i.op.isLocal = false := by
          simpa using hGuards
        rcases hCase with ⟨_,hSkip⟩ | ⟨_,hL,_⟩
        · rw [hGuard] at hSkip
          cases hSkip
        · rw [hNonLocal] at hL
          cases hL
      · push Not at h
        exact ⟨Bool.eq_false_of_not_eq_true h.1,Bool.eq_false_of_not_eq_true h.2⟩
    have hNext := pendingEarlyNext s.pc
    simp only [hUnmarked.1,hUnmarked.2,Bool.toNat_false,Nat.add_zero] at hNext
    simp only [Option.toList_none,List.countP_nil,Nat.add_zero]
    rcases hCase with ⟨rfl,_⟩ | ⟨_,_,hExec⟩
    · exact hNext
    rcases scoreExecLocal hExec with hFrame | ⟨_,hSite,hMatch,hRun⟩
    · have hPc := hFrame.pc
      cases hOp : i.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
      case bra target uniform =>
        have hh := hAudit.2
        simp only [hOp,beq_iff_eq] at hh
        rw [hPc,hh]
      case brx => simp [hOp] at hAudit
      all_goals exact hPc.symm ▸ hNext
    · rw [(scoreSegmentFrame hRun).1,earlyRankSegment hSite hMatch]
  · have hSite := estep_source_pc hStep
    have hasLayout : earlyProbabilityMark e = probabilityMark s.pc ∧
        scoredStatisticsMark e = statisticsMark s.pc := by
      cases e
      simp only [probabilityMark,statisticsMark,earlyProbabilityMark,scoredStatisticsMark] at *
      rw [hSite]
      trivial
    have count (q : Event → Bool) : [e].countP q = (q e).toNat := by
      cases h : q e <;> simp [h]
    simp only [Option.toList_some,count,hasLayout.1,hasLayout.2]
    change (pendingEarly u.pc).toNat + (probabilityMark s.pc).toNat =
      (pendingEarly s.pc).toNat + (statisticsMark s.pc).toNat
    by_cases hMarks : statisticsMark s.pc = true ∨ probabilityMark s.pc = true
    · rw [markedEarlyProgress hStep hMarks]
      exact pendingEarlyNext s.pc
    · obtain ⟨i,hCode,hLocal,hFires⟩ := estep_event_source hStep
      have hAll : kernel.code.all (fun i => i.op.isLocal || Epilogue.ordinaryEvent i.op) =
          true := by decide +kernel
      have hOrd := List.all_eq_true.mp hAll _ (List.mem_of_getElem? hCode)
      rw [hLocal,Bool.false_or] at hOrd
      rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hOrd) hFires with h | h
      · rw [h]
        push Not at hMarks
        rw [Bool.eq_false_of_not_eq_true hMarks.1,Bool.eq_false_of_not_eq_true hMarks.2]
      · rw [h]
        exact pendingEarlyNext s.pc

private theorem earlyRankPath {l : Launch} {g : Nat} {s t : TState} {es : List Event}
    (hPath : TraceReach kernel Assumptions.all l g s es t) :
    (pendingEarly t.pc).toNat + es.countP earlyProbabilityMark =
      (pendingEarly s.pc).toNat + es.countP scoredStatisticsMark := by
  induction hPath with
  | refl => rfl
  | tau ht _ ih =>
    have hStep := earlyRankStep (.inl ⟨rfl,ht⟩)
    simp only [Option.toList_none,List.countP_nil,Nat.add_zero] at hStep
    rw [← hStep]
    exact ih
  | event he _ ih =>
    have hStep := earlyRankStep (.inr ⟨_,rfl,he⟩)
    simp only [Option.toList_some,List.countP_cons,List.countP_nil,Nat.zero_add] at hStep ⊢
    omega

/-- At an actual rescale coefficient write, the lane has one previous
statistics publication for each previous early probability packet. -/
theorem rescaleStoreStatisticsEarlyRank {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos : Nat} {biased : Bool}
    {a : Acc} {bytes : List Byte}
    (hStore : StatisticsStore X (g,pos) (rescaleStore biased) a bytes) :
    ((X.tr g).take pos).countP scoredStatisticsMark =
      ((X.tr g).take pos).countP earlyProbabilityMark := by
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX hStore)
  obtain ⟨t,_,hPath,hStep⟩ := hRun.before_event hStore
  have hSite := (estep_source_pc hStep).symm
  have hClear : pendingEarly t.pc = false := by
    rw [hSite]
    cases biased
    · change pendingEarly 6890 = false
      decide
    · change pendingEarly 5682 = false
      decide
  have hRank := earlyRankPath hPath
  rw [hClear] at hRank
  simpa only [show pendingEarly 0 = false by decide,Bool.toNat_false,Nat.zero_add] using hRank.symm

private theorem namedArrivalKind {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {id count : Opnd} {aligned : Bool}
    (hc : kernel.code[s.pc]? = some ⟨none,.barArrive id count aligned⟩)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ id count, e.kind = .bar id count .arrive := by
  obtain ⟨ins,hCode,_,hf⟩ := estep_event_source he
  obtain rfl := Option.some.inj (hc.symm.trans hCode)
  simp only [eventTmpl] at hf
  unfold barTmpl at hf
  repeat' split at hf
  all_goals first | exact ⟨_,_,congrArg Event.kind hf.1⟩ | cases hf.2

private theorem statisticsNoticeOfEarlierStore {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos : Nat}
    {biased : Bool} {a : Acc} {bytes : List Byte}
    (hStore : StatisticsStore X (g,pos) (rescaleStore biased) a bytes) :
    (before X (g,pos)).notices = ((X.tr g).take pos).countP scoredStatisticsMark := by
  rw [beforeNotices]
  apply List.countP_congr
  intro e hm
  obtain ⟨j,hGet⟩ := List.mem_iff_getElem?.mp hm
  have hLength := (List.getElem?_eq_some_iff.mp hGet).1
  rw [List.length_take] at hLength
  have hEarlier : j < pos := by omega
  rw [List.getElem?_take_of_lt hEarlier] at hGet
  constructor
  · intro h
    obtain ⟨round,hNotice⟩ := Option.isSome_iff_exists.mp h
    have hFinal : round ≠ .final := by
      intro hRound
      subst round
      have hPast := afterFinalPublicationPc hX (g := g) (i := j) ⟨e,hGet,hNotice⟩ hEarlier hStore
      change 7616 < (statsStore (rescaleStore biased)).pc at hPast
      cases biased <;> exact (by decide : ¬ 7616 < (statsStore (rescaleStore _)).pc) hPast
    have hSite : e.pc = 4397 ∨ e.pc = 5683 ∨ e.pc = 6891 := by
      rcases e with ⟨pc,kind⟩
      cases kind <;> simp only [notice,reduceCtorEq] at hNotice
      rename_i mode
      cases mode <;> simp only [reduceCtorEq] at hNotice
      unfold noticeRound at hNotice
      split at hNotice <;> simp_all
    simpa [scoredStatisticsMark] using hSite
  · intro h
    have hSite : e.pc ∈ [4397,5683,6891] := List.contains_iff_mem.mp h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite
    have hAt : X.get (g,j) = some e := hGet
    obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX hAt)
    have hSize : pos < (X.tr g).length := len_of_get hStore
    obtain ⟨s,u,hStep,_⟩ := hr.after_event hAt (by omega)
    have hPc := estep_source_pc hStep
    have hKind : ∃ id count, e.kind = .bar id count .arrive := by
      rcases hSite with hS | hS | hS
      · exact namedArrivalKind ((hPc.symm.trans hS).symm ▸ Flow.code_4397) hStep
      · exact namedArrivalKind ((hPc.symm.trans hS).symm ▸ Flow.code_5683) hStep
      · exact namedArrivalKind ((hPc.symm.trans hS).symm ▸ Flow.code_6891) hStep
    obtain ⟨id,count,hKind⟩ := hKind
    unfold publishesStats notice
    rw [hKind]
    rcases hSite with hS | hS | hS <;> rw [hS] <;> rfl

/-- Every actual rescale alpha publication has the ordinal of the preceding
physical early probability packets of that same lane and stage. -/
theorem rescaleStoreNoticeOfEarlyCredits {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos : Nat} {stage : Fin 2} {biased : Bool} {a : Acc} {bytes : List Byte}
    (hStage : warpIndex l g/4 = stage.val)
    (hStore : StatisticsStore X (g,pos) (rescaleStore biased) a bytes) :
    (before X (g,pos)).notices = probabilityOrdinal l X (g/l.block) stage 0 (g,pos) := by
  have hWarp : warpIndex l g < 8 := by have := stage.isLt; omega
  exact (statisticsNoticeOfEarlierStore hX hStore).trans
    ((rescaleStoreStatisticsEarlyRank hX hStore).trans
      (earlyProbabilityCount hp hX stage hWarp hStage (len_of_get hStore)))

private theorem countUnchanged {X : Execution} (q : Event → Bool) {g pos n : Nat}
    (hQuiet : ∀ j < n, ∃ e, X.get (g,pos+j) = some e ∧ q e = false) :
    ((X.tr g).take (pos+n)).countP q = ((X.tr g).take pos).countP q := by
  induction n with
  | zero => rw [Nat.add_zero]
  | succ n ih =>
    obtain ⟨e,he,hFalse⟩ := hQuiet n (by omega)
    rw [Nat.add_succ,countP_take_succ_false he hFalse]
    exact ih (fun j hj => hQuiet j (by omega))

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
