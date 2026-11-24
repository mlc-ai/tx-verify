-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxCounterEntry
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalOccurrence
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.NamedBarrierParticipants
import Lemmas.Flow.NthEv
import Lemmas.Step.ExitLast
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
import Kernels.TmlFa4Fwd.Flow.Code.Part068
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part103
import Kernels.TmlFa4Fwd.Flow.Code.Part104

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue

private def exitEvent : Event := ⟨9205, .exit⟩

private def blockNotice (e : Event) : Bool :=
  match Thread.Scores.notice e with
  | some .first | some .biased | some .plain => true
  | some .final | none => false

private def finalNotice (e : Event) : Bool := Thread.Scores.notice e == some .final

private theorem countStatsSplit (events : List Event) :
    events.countP Thread.Scores.publishesStats =
      events.countP blockNotice + events.countP finalNotice := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.countP_cons, ih]
    cases hn : Thread.Scores.notice e with
    | none => simp [Thread.Scores.publishesStats, blockNotice, finalNotice, hn]
    | some round =>
      cases round <;> simp [Thread.Scores.publishesStats, blockNotice, finalNotice, hn] <;> omega

private theorem blockNoticeLe (events : List Event) :
    events.countP blockNotice ≤ events.countP Thread.Scores.publishesStats := by
  rw [countStatsSplit]
  omega

section
variable {l : Launch}

private theorem noticeOfContinuingBarrier {g pc : Nat} {round : Thread.Scores.Round} {s u : TState}
    {e : Event} (he : EStep kernel Assumptions.all l g s e (some u)) (hPc : e.pc = pc)
    (hCode : kernel.code[pc]? = some ⟨none, .barArrive (.reg 5127) (.imm 64) true⟩)
    (hRound : Thread.Scores.noticeRound pc = some round) :
    Thread.Scores.notice e = some round := by
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  rw [← estep_source_pc he, hPc, hCode] at hc
  obtain rfl := Option.some.inj hc.symm
  have hKind : ∃ id count, e.kind = .bar id count .arrive := by
    simp only [eventTmpl] at hf
    unfold barTmpl at hf
    repeat' split at hf
    all_goals first
      | exact ⟨_, _, congrArg Event.kind hf.1⟩
      | cases hf.2
  obtain ⟨id,count,hKind⟩ := hKind
  simpa [Thread.Scores.notice, hKind, hPc] using hRound

private theorem markerIsNotice {g pc : Nat} {round : Thread.Scores.Round} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hExit : (⟨9205,.exit⟩ : Event) ∈ es) (hMarker : pc ≠ 9205)
    (hCode : kernel.code[pc]? = some ⟨none, .barArrive (.reg 5127) (.imm 64) true⟩)
    (hRound : Thread.Scores.noticeRound pc = some round) {e : Event} (he : e ∈ es) (hm : e.pc = pc)
    :
    Thread.Scores.notice e = some round := by
  induction hw with
  | stop => cases he
  | tau _ _ ih => exact ih hExit he
  | ev hStep _ ih =>
    rcases List.mem_cons.mp he with rfl | he'
    · exact noticeOfContinuingBarrier hStep hm hCode hRound
    · have hTail := (List.mem_cons.mp hExit).resolve_left (by
        intro h
        obtain ⟨_, _, hf⟩ := hStep
        rw [← h] at hf
        cases fires_end_none hf (.inr rfl))
      exact ih hTail he'
  | last hStep =>
    obtain rfl := List.mem_singleton.mp he
    have hEq := List.mem_singleton.mp hExit
    exact (hMarker (hm.symm.trans (congrArg Event.pc hEq.symm))).elim

/-- The marked publications count toward the role cursor on a walk ending in an actual exit. -/
private theorem loopPublicationIsNotice {g : Nat} (loop : ScoreLoop) {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hExit : (⟨9205,.exit⟩ : Event) ∈ es) {e : Event} (he : e ∈ es)
    (hm : loopPublication loop e = true) :
    blockNotice e = true := by
  have hPc := loopPublicationPc loop hm
  cases loop
  · have hn := markerIsNotice (round := .biased) hw hExit (by decide) Flow.code_5683 rfl he hPc
    simp [blockNotice, hn]
  · have hn := markerIsNotice (round := .plain) hw hExit (by decide) Flow.code_6891 rfl he hPc
    simp [blockNotice, hn]

private theorem blockNoticeSites {e : Event} (h : blockNotice e = true) :
    e.pc ∈ [4397,5683,6891] := by
  obtain ⟨round,hn,hNot⟩ : ∃ round, Thread.Scores.notice e = some round ∧
      round ≠ .final := by
    cases hn : Thread.Scores.notice e with
    | none => simp [blockNotice,hn] at h
    | some round =>
      cases round <;> simp_all [blockNotice]
  unfold Thread.Scores.notice at hn
  split at hn <;> try contradiction
  unfold Thread.Scores.noticeRound at hn
  split at hn <;> simp_all

private theorem loopNoticeAtSite {e : Event} (loop : ScoreLoop)
    (hLo : windowHead loop ≤ e.pc) (hHi : e.pc < windowEnd loop)
    (h : blockNotice e = true) : loopPublication loop e = true := by
  have hSite := blockNoticeSites h
  have hPc : e.pc = (if loop = .biased then 5683 else 6891) := by
    cases loop <;> dsimp [windowHead,windowEnd,loopWindow,windowSite] at hLo hHi ⊢
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite; omega
  exact loopPublicationOfPc loop hPc

private theorem loopNoticeCount {g : Nat} {s : TState} {es before : List Event} {vs : List Visit}
    (loop : ScoreLoop) (hw : Walk kernel Assumptions.all l g s es vs) (hExit : exitEvent ∈ es)
    (hIn : before ⊆ es) (hSites : ∀ e ∈ before, windowHead loop ≤ e.pc ∧ e.pc < windowEnd loop) :
    before.countP blockNotice = before.countP (loopPublication loop) := by
  apply List.countP_congr
  intro e he
  exact ⟨loopNoticeAtSite loop (hSites e he).1 (hSites e he).2,
    loopPublicationIsNotice loop hw hExit (hIn he)⟩

private def afterBlockCode (i : Instr) : Bool :=
  (i.op.isLocal || ordinaryEvent i.op) &&
    match i.op with
    | .bra dst _ => decide (7605 ≤ dst)
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem afterBlockAudit : (kernel.code.drop 7605).all afterBlockCode = true := by
  kernel_rfl

private theorem afterBlockCodeAt {s : TState} {i : Instr}
    (hPc : 7605 ≤ s.pc) (hc : kernel.code[s.pc]? = some i) : afterBlockCode i = true := by
  apply List.all_eq_true.mp afterBlockAudit
  apply List.mem_of_getElem? (i := s.pc-7605)
  rwa [List.getElem?_drop,Nat.add_sub_of_le hPc]

private theorem afterBlocksStep {g : Nat} {s u : TState} {ev : Option Event} (hPc : 7605 ≤ s.pc)
    (h : WStep kernel Assumptions.all l g s ev u) : 7605 ≤ u.pc := by
  rcases h with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · obtain ⟨i,hc,_,hSource⟩ := tauScoreSource ht
    rcases hSource with ⟨rfl,_⟩ | ⟨_,_,hx⟩
    · exact hPc.trans (Nat.le_succ _)
    have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hF := (scoreExecLocal hx).resolve_right (fun ⟨_,hm,_⟩ => hOff hm)
    have hCode := (Bool.and_eq_true_iff.mp (afterBlockCodeAt hPc hc)).2
    have hNext := hF.pc
    cases hop : i.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hNext
    case bra dst uni =>
      rw [hNext]
      simpa only [afterBlockCode,hop,decide_eq_true_eq] using hCode
    case brx => simp [hop] at hCode
    all_goals omega
  · obtain ⟨i,hc,hLocal,hFire⟩ := estep_event_source he
    have hOp := (Bool.and_eq_true_iff.mp (afterBlockCodeAt hPc hc)).1
    simp only [hLocal,Bool.false_or] at hOp
    rcases callbackFrame_fires (ordinaryEventFrame hOp) hFire with hEq | hEq <;> omega

private theorem noBlockNoticeAfter {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hp : 7605 ≤ s.pc) (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP blockNotice = 0 := by
  have hNo {e : Event} (he : 7605 ≤ e.pc) : blockNotice e = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hSite := blockNoticeSites h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite
    omega
  induction hw with
  | stop => simp
  | tau ht _ ih => exact ih (afterBlocksStep hp (.inl ⟨rfl,ht⟩))
  | ev he _ ih =>
    have hTail := ih (afterBlocksStep hp (.inr ⟨_,rfl,he⟩))
    simp [hNo ((estep_source_pc he).symm ▸ hp),hTail]
  | last he => simp [hNo ((estep_source_pc he).symm ▸ hp)]

private def countFacts (blocks split : Nat) : List (Nat × Value) :=
  [(1229, b32 (blocks-1)), (1359, b32 split)]

private theorem signedBits {n : Nat} (h : n < 2^31) :
    toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) = (n : Int) := by
  rw [truncBits_ofNat (show n < 2^32 by omega) (by decide)]
  have hWord : n < 2^64 := by omega
  have h32 : n < 2^32 := by omega
  simp only [toSigned, toNat_ofNat_lt hWord, Nat.mod_eq_of_lt h32, ite_eq_left h]

private theorem plainCountDecision (l : Launch) (g blocks split : Nat)
    (hb : blocks < 2^31) (hs : split < blocks) :
    Seg kernel Assumptions.all l g 2 6654 (countFacts blocks split)
      6656 ([(643, .pred (decide (split = 0))), (1491, b32 split)]) := by
  have hMinOp : (IntOp.min false == IntOp.max false) = false := rfl
  have hSign : ((some IType.s : Option IType) == some IType.s) = true := rfl
  have hMin : compare .lt .s 32 (truncBits 32 (BitVec.ofNat 64 (blocks - 1)))
      (truncBits 32 (BitVec.ofNat 64 split)) = false := by
    change decide (toSigned 32 (truncBits 32 (BitVec.ofNat 64 (blocks - 1))) <
      toSigned 32 (truncBits 32 (BitVec.ofNat 64 split))) = false
    rw [signedBits (by omega), signedBits (by omega)]
    exact decide_eq_false (by omega)
  have hTest : compare .lt .s 32 (truncBits 32 (BitVec.ofNat 64 split))
      (truncBits 32 (BitVec.ofInt 64 1)) = decide (split = 0) := by
    change decide (toSigned 32 (truncBits 32 (BitVec.ofNat 64 split)) < (1 : Int)) = _
    rw [signedBits (by omega), decide_eq_decide]
    omega
  intro t ht
  simp only [countFacts] at ht
  seg_fp ht using
    simp only [b32, hMinOp, hSign, Bool.false_eq_true, ite_false, ite_true, hMin,
      Option.getD_some]
    simp only [truncBits_ofNat (show split < 2^32 by omega) (by decide)] at hTest ⊢
    all_goals rw [hTest]

/-- The decoded plain-loop decision depends only on the integer repeat limits. -/
theorem plainCountDecisionWithLimits (l : Launch) (g blocks split : Nat)
    (hb : blocks < 2^31) (hs : split < blocks) :
    Seg kernel Assumptions.all l g 2 6654 (repeatCountLimits blocks split)
      6656 [(643,.pred (decide (split = 0))), (1491,b32 split)] :=
  plainCountDecision l g blocks split hb hs

private theorem runOfTerminalWalk {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) (hExit : exitEvent ∈ es)
    : Run kernel Assumptions.all l g s es none := by
  induction hw with
  | stop => cases hExit
  | tau ht _ ih =>
    cases ih hExit with
    | step hLoc he hTail => exact .step (.head ht hLoc) he hTail
    | last hLoc he => exact .last (.head ht hLoc) he
  | ev he _ ih =>
    rcases List.mem_cons.mp hExit with rfl | hOther
    · obtain ⟨_, _, hf⟩ := he
      cases fires_end_none hf (.inr rfl)
    · exact .step .refl he (ih hOther)
  | last he => exact .last .refl he

private theorem plainExitNoticeCount {g blocks split : Nat} {s : TState} {es : List Event}
    (hs : At s 6654 (countFacts blocks split)) (hb : blocks < 2^31) (hSplit : split < blocks)
    (hr : Run kernel Assumptions.all l g s es none) (hExit : exitEvent ∈ es) :
    es.countP blockNotice = split := by
  obtain ⟨t, ht, hT⟩ := (plainCountDecision l g blocks split hb hSplit).apply hs
  have hPred := hT.2.2.2.2.1
  have hAt : At t 6656 [(1491, b32 split)] := hT.mono hT.2.2.2.2.2
  obtain ⟨a, ha, hA⟩ := run_bra (A := Assumptions.all) (L := l) (g := g)
    Flow.code_6656 (decide (split=0)) hAt hPred
    (fun a ha => by
      simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (maxSeg (by decide))
  have haRun := hr.after_local (run_rtg (run_comp ht ha))
  obtain ⟨vs,hWalk⟩ := Mma.walkFromRun haRun
  by_cases hZero : split = 0
  · have hPc : a.pc = 7605 := by simpa only [hZero,decide_true,ite_true] using hA.1
    rw [hZero]
    exact noBlockNoticeAfter hPc.ge hWalk
  have hPos : 0 < split := Nat.pos_of_ne_zero hZero
  have hA' : At a 6657 [(1491,b32 split)] := by
    simpa only [decide_eq_false hZero,Bool.false_eq_true,ite_false] using hA
  obtain ⟨u, tail, hInit, hUWalk⟩ := scoreRunToHeadBefore .plain hWalk
    (by rw [hA'.1]; decide) (by rw [hA'.1]; decide) (by intro _ h; cases h) hExit (by decide)
  rw [hA'.1] at hInit
  have hSub : a.sub ≤ 3 := hA'.2.1.symm ▸ Nat.zero_le _
  obtain ⟨hPc, hUS, hWord⟩ := plainLoopInitializedCount hA'.1 hSub hA'.2.2.2.2.1
    hPos (by omega) hInit
  obtain ⟨v,pre,rest,path,hEs,hMem,hV,hCount,_,_,_,_,hVWalk,hSites⟩ :=
    loopPublicationCountBounds .plain hUWalk hPc hUS hWord (by omega) hExit (by decide)
  have hNotice := loopNoticeCount .plain hUWalk hExit
    (by intro e he; rw [hEs]; exact List.mem_append_left _ he) hSites
  have hAfter : 7605 ≤ v.pc := by rw [hV]; decide
  rw [hEs,List.countP_append,hNotice,noBlockNoticeAfter hAfter hVWalk,Nat.add_zero,hCount,
    initialPlainDistance hPos (by omega)]

private theorem noticesFromRepeatEntry {g blocks biasCap : Nat} {a : TState} {es : List Event}
    (hBlocks : 0 < blocks) (hb : blocks < 2^31) (hBias : 0 < biasCap)
    (hA : let split := firstPlainSplit blocks biasCap
      if firstBiasedRepeats blocks biasCap = 0 then At a 6654 (repeatCountLimits blocks split)
      else At a 5032 ((7248,b32 (2^32-(blocks-split))) :: repeatCountLimits blocks split))
    (haRun : Run kernel Assumptions.all l g a es none) (hExit : (⟨9205,.exit⟩ : Event) ∈ es) :
    es.countP blockNotice = blocks-1 := by
  let split := firstPlainSplit blocks biasCap
  let biased := firstBiasedRepeats blocks biasCap
  have hSplit : split < blocks := by unfold split firstPlainSplit; omega
  change (if biased = 0 then At a 6654 (repeatCountLimits blocks split)
    else At a 5032 ((7248,b32 (2^32-(blocks-split))) :: repeatCountLimits blocks split)) at hA
  by_cases hz : biased = 0
  · rw [ite_eq_left hz] at hA
    have hFrame : At a 6654 (countFacts blocks split) := hA
    have hLower := plainExitNoticeCount hFrame hb hSplit haRun hExit
    unfold biased firstBiasedRepeats at hz
    change blocks-1-split = 0 at hz
    omega
  · rw [ite_eq_right hz] at hA
    have hMore : split+1 < blocks := by
      unfold biased firstBiasedRepeats at hz
      change blocks-1-split ≠ 0 at hz
      omega
    have hWord : a.regs 7248 = some (b32 (2^32-(blocks-split))) := hA.2.2.2.2.1
    have hSub : a.sub ≤ 3 := hA.2.1.symm ▸ Nat.zero_le _
    obtain ⟨vs, hw⟩ := Mma.walkFromRun haRun
    obtain ⟨u, pre, rest, tail, hEs, hMem, hU, hCount, hRegs, hUS, hUA, hUF, hWalk,hSites⟩ :=
      loopPublicationCountBounds .biased hw hA.1 hSub hWord (by omega) hExit (by decide)
    have hRegs' : Holds a.regs (countFacts blocks split) := hA.2.2.2.2.2
    have hFrame : At u 6654 (countFacts blocks split) :=
      ⟨hU, hUS, hUA, hUF, (hRegs _ (by decide)).trans hRegs'.1,
        (hRegs _ (by decide)).trans hRegs'.2.1, trivial⟩
    have hAfter := plainExitNoticeCount hFrame hb hSplit (runOfTerminalWalk hWalk hMem) hMem
    have hBefore := loopNoticeCount .biased hw hExit
      (by intro e he; rw [hEs]; exact List.mem_append_left _ he) hSites
    rw [initialBiasedDistance hb hMore] at hCount
    rw [hEs, List.countP_append]
    omega

private theorem plainLateNoticeLower {g blocks split : Nat} {s : TState} {es : List Event}
    {visits : List Visit} {target : Event} (hs : At s 6654 (countFacts blocks split))
    (hb : blocks < 2^31) (hSplit : split < blocks)
    (hw : Walk kernel Assumptions.all l g s es visits) (hExit : target ∈ es)
    (hLate : 7605 ≤ target.pc) :
    split ≤ es.countP scoredStatisticsMark := by
  obtain ⟨t, ht, hT⟩ := (plainCountDecision l g blocks split hb hSplit).apply hs
  have hPred := hT.2.2.2.2.1
  have hAt : At t 6656 [(1491, b32 split)] := hT.mono hT.2.2.2.2.2
  obtain ⟨a, ha, hA⟩ := run_bra (A := Assumptions.all) (L := l) (g := g)
    Flow.code_6656 (decide (split=0)) hAt hPred
    (fun a ha => by
      simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (maxSeg (by decide))
  rcases Mma.advanceWalkLocals (run_comp ht ha) hw with rfl | ⟨_,_,_,hWalk⟩
  · cases hExit
  by_cases hZero : split = 0
  · simp [hZero]
  have hPos : 0 < split := Nat.pos_of_ne_zero hZero
  have hA' : At a 6657 [(1491,b32 split)] := by
    simpa only [decide_eq_false hZero,Bool.false_eq_true,ite_false] using hA
  obtain ⟨u, tail, hInit, hUWalk⟩ := scoreRunToHeadBefore .plain hWalk
    (by rw [hA'.1]; decide) (by rw [hA'.1]; decide) (by intro _ h; cases h) hExit
    ((show (scoreLoopSite .plain).head ≤ 7605 by decide).trans hLate)
  rw [hA'.1] at hInit
  have hSub : a.sub ≤ 3 := hA'.2.1.symm ▸ Nat.zero_le _
  obtain ⟨hPc, hUS, hWord⟩ := plainLoopInitializedCount hA'.1 hSub hA'.2.2.2.2.1
    hPos (by omega) hInit
  obtain ⟨v,pre,rest,path,hEs,hMem,hV,hCount,_,_,_,_,hVWalk,hSites⟩ :=
    loopPublicationCountBounds .plain hUWalk hPc hUS hWord (by omega) hExit
      ((show (scoreLoopSite .plain).increment + 4 ≤ 7605 by decide).trans hLate)
  have hNotice : pre.countP (loopPublication .plain) ≤ pre.countP scoredStatisticsMark := by
    apply List.countP_mono_left
    intro ev _ h
    have hPc := loopPublicationPc .plain h
    simp [scoredStatisticsMark, hPc]
  rw [initialPlainDistance hPos (by omega)] at hCount
  rw [hEs,List.countP_append]
  omega

private theorem noticesBeforeLateFromRepeatEntry {g blocks biasCap : Nat} {a : TState}
    {es : List Event} {visits : List Visit} {target : Event} (hBlocks : 0 < blocks)
    (hb : blocks < 2^31) (hBias : 0 < biasCap)
    (hA : let split := firstPlainSplit blocks biasCap
      if firstBiasedRepeats blocks biasCap = 0 then At a 6654 (repeatCountLimits blocks split)
      else At a 5032 ((7248,b32 (2^32-(blocks-split))) :: repeatCountLimits blocks split))
    (hWalk : Walk kernel Assumptions.all l g a es visits) (hExit : target ∈ es)
    (hLate : 7605 ≤ target.pc) :
    blocks-1 ≤ es.countP scoredStatisticsMark := by
  let split := firstPlainSplit blocks biasCap
  let biased := firstBiasedRepeats blocks biasCap
  have hSplit : split < blocks := by unfold split firstPlainSplit; omega
  change (if biased = 0 then At a 6654 (repeatCountLimits blocks split)
    else At a 5032 ((7248,b32 (2^32-(blocks-split))) :: repeatCountLimits blocks split)) at hA
  by_cases hz : biased = 0
  · rw [ite_eq_left hz] at hA
    have hFrame : At a 6654 (countFacts blocks split) := hA
    have hLower := plainLateNoticeLower hFrame hb hSplit hWalk hExit hLate
    unfold biased firstBiasedRepeats at hz
    change blocks-1-split = 0 at hz
    omega
  · rw [ite_eq_right hz] at hA
    have hMore : split+1 < blocks := by
      unfold biased firstBiasedRepeats at hz
      change blocks-1-split ≠ 0 at hz
      omega
    have hWord : a.regs 7248 = some (b32 (2^32-(blocks-split))) := hA.2.2.2.2.1
    have hSub : a.sub ≤ 3 := hA.2.1.symm ▸ Nat.zero_le _
    obtain ⟨u, pre, rest, tail, hEs, hMem, hU, hCount, hRegs, hUS, hUA, hUF, hWRest,hSites⟩ :=
      loopPublicationCountBounds .biased hWalk hA.1 hSub hWord (by omega) hExit
        ((show (scoreLoopSite .biased).increment + 4 ≤ 7605 by decide).trans hLate)
    have hRegs' : Holds a.regs (countFacts blocks split) := hA.2.2.2.2.2
    have hFrame : At u 6654 (countFacts blocks split) :=
      ⟨hU, hUS, hUA, hUF, (hRegs _ (by decide)).trans hRegs'.1,
        (hRegs _ (by decide)).trans hRegs'.2.1, trivial⟩
    have hAfter := plainLateNoticeLower hFrame hb hSplit hWRest hMem hLate
    have hBefore : pre.countP (loopPublication .biased) ≤ pre.countP scoredStatisticsMark := by
      apply List.countP_mono_left
      intro ev _ h
      have hPc := loopPublicationPc .biased h
      simp [scoredStatisticsMark, hPc]
    rw [initialBiasedDistance hb hMore] at hCount
    rw [hEs, List.countP_append]
    omega

private theorem repeatedMarksBeforeLate {g blocks cap past : Nat} {s : TState} {es : List Event}
    {vs : List Visit} {target : Event} (hBlocks : 0 < blocks) (hb : blocks < 2^31) (hCap : 0 < cap)
    (hc : cap < 2^31) (hs : At s 5006 (firstLoopGeometry blocks cap past))
    (hw : Walk kernel Assumptions.all l g s es vs) (he : target ∈ es) (hLate : 7605 ≤ target.pc) :
    blocks - 1 ≤ es.countP scoredStatisticsMark := by
  obtain ⟨a,_,hA,hWalk⟩ := firstCountEntryWalkOfLateEvent hBlocks hb hCap hc hs hw he hLate
  exact noticesBeforeLateFromRepeatEntry hBlocks hb hCap hA hWalk he hLate

/-- A completed first-pass state needs only the three integer count words to account for
the repeated statistics notices on an exiting trace. -/
private theorem repeatedBlockNoticesOfGeometry {g blocks cap past : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hBlocks : 0 < blocks) (hb : blocks < 2^31) (hCap : 0 < cap)
    (hc : cap < 2^31) (hs : At s 5006 (firstLoopGeometry blocks cap past))
    (hw : Walk kernel Assumptions.all l g s es vs) (he : (⟨9205,.exit⟩ : Event) ∈ es) :
    es.countP blockNotice = blocks-1 := by
  obtain ⟨a,_,hA,hWalk⟩ := firstCountEntryWalk hBlocks hb hCap hc hs hw he
  exact noticesFromRepeatEntry hBlocks hb hCap hA (runOfTerminalWalk hWalk he) he

private theorem staysAfterFirstRound :
    (kernel.code.drop 5006).all (fun i => Thread.staysPastEvent 5006 i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem firstRoundSegments :
    Assumptions.swExp2Sites.all (fun site =>
      match PTX.Assumption.cuteExp2.matchAt kernel site with
      | some seg => decide (5006 ≤ seg.stop)
      | none => false) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem noBiasedCreditAfterLoop {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (h : 6654 ≤ s.pc) (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP (barrierMark 6532) = 0 := by
  have hCode : (kernel.code.drop 6654).all (fun i => Thread.staysPastEvent 6654 i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hAbove := Thread.eventTailEventsOfSegmentFloor hCode (fun site hSite hm seg hs => by
    have hAudit : Assumptions.swExp2Sites.all (fun pc =>
        if 6654 ≤ pc then
          match PTX.Assumption.cuteExp2.matchAt kernel pc with
          | some m => decide (6654 ≤ m.stop)
          | none => false
        else true) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    simpa only [ite_eq_left hSite, hs, decide_eq_true_eq]
      using List.all_eq_true.mp hAudit site hm) hw h
  apply List.countP_eq_zero.mpr
  intro ev he hm
  have hf : ev.pc = 6532 := beq_iff_eq.mp hm
  have := hAbove ev he
  omega

private theorem biasedCreditCountOfRepeatedGeometry {g blocks cap past : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hBlocks : 0 < blocks) (hb : blocks < 2^31) (hCap : 0 < cap)
    (hc : cap < 2^31) (hs : At s 5006 (firstLoopGeometry blocks cap past))
    (hw : Walk kernel Assumptions.all l g s es vs) (he : (⟨9205,.exit⟩ : Event) ∈ es) :
    es.countP (barrierMark 6532) = firstBiasedRepeats blocks cap := by
  obtain ⟨u,_,hA,hWalk⟩ := firstCountEntryWalk hBlocks hb hCap hc hs hw he
  let split := firstPlainSplit blocks cap
  let biased := firstBiasedRepeats blocks cap
  change (if biased = 0 then At u 6654 (repeatCountLimits blocks split)
    else At u 5032 ((7248,b32 (2^32-(blocks-split))) :: repeatCountLimits blocks split)) at hA
  change _ = biased
  by_cases hz : biased = 0
  · rw [ite_eq_left hz] at hA
    exact (noBiasedCreditAfterLoop hA.1.ge hWalk).trans hz.symm
  rw [ite_eq_right hz] at hA
  have hMore : split+1 < blocks := by
    unfold biased firstBiasedRepeats at hz
    omega
  have huWord : u.regs 7248 = some (b32 (2^32-(blocks-split))) := hA.2.2.2.2.1
  have huSub : u.sub ≤ 3 := hA.2.1.symm ▸ Nat.zero_le _
  obtain ⟨v,pre,tail,_,hList,_,hV,hCount,_,_,_,_,hTail,_⟩ :=
    loopProbabilityCountBounds .biased hWalk hA.1 huSub huWord (by omega) he (by decide)
  have hAbove : 6654 ≤ v.pc := by rw [hV]; decide
  rw [hList,List.countP_append,noBiasedCreditAfterLoop hAbove hTail,Nat.add_zero]
  exact hCount.trans (initialBiasedDistance hb hMore)
end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {stop : Event}
    (hg : g < l.threads) (hWarp : Prologue.warpIndex l g < 8)
    (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hCuQ : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4*i)).at k))
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k)) (he : X.get (g,index) = some stop)
include hp hX hg hWarp hWork hCuQ hUsedK he

private theorem exitedActivePublicationAndScoreCount (hExit : stop.kind = .exit) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      (Thread.Scores.before X (g,index)).notices =
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 + 1 ∧
      (Thread.Scores.before X (g,(X.tr g).length)).notices =
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 + 1 ∧
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 ≤
        okPolls (Thread.Scores.scoreReadyObject l (g/l.block)
          ⟨Prologue.warpIndex l g / 4, by omega⟩)
          (X.tr g) ∧ (X.tr g).countP (barrierMark 6532) ≤ 10 ∧
      (∃ i, Thread.Scores.Publishes X (g,i) .first) ∧
      (∃ i, Thread.Scores.Publishes X (g,i) .final) ∧
      let tile := (assignedCoordinates p batch (g/l.block)).1
      let blocks := Mma.trips p batch tile
      let stage := stageOf ⟨Prologue.warpIndex l g,hWarp⟩
      (X.tr g).countP (barrierMark 6532) =
        firstBiasedRepeats blocks (blocks - stageGeometryBlocks p batch tile stage + 10) := by
  rcases stop with ⟨pc,kind⟩
  change kind = .exit at hExit
  subst kind
  have hPc := actualExitPc hX he
  subst pc
  let stage := stageOf ⟨Prologue.warpIndex l g,hWarp⟩
  let src := laneOf l g
  have hLane : warpLane l g src = g := Nat.sub_add_cancel
    ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hSrc : src < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨batch,hBatch,hLo,hHi,j,u,waits,before,rest,tail,_,hEs,
    hExit',hFirstNotice,hU,hWalk,hSites⟩ :=
    activeCountersOfExit hp hX hg hWarp hSrc hWork hCuQ hUsedK (hLane.symm ▸ he)
  rw [hLane] at hEs hWalk
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let blocks := Mma.trips p batch tile
  let cap := blocks-stageGeometryBlocks p batch tile stage+10
  let past := p.kLength batch-p.qLength batch+256*tile
  have hAt : At u 5006 (firstLoopGeometry blocks cap past) := hU
  have hb := hBatch
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  have hBounds := firstGeometryBounds hp stage hb hTile (lane := 0) (by decide)
  have hRepeat := repeatedBlockNoticesOfGeometry hBounds.1 hBounds.2.1 hBounds.2.2.1
    hBounds.2.2.2.1 hAt hWalk hExit'
  obtain ⟨_,hFull⟩ := hX.thr g hg
  obtain ⟨_,hFullWalk⟩ := Mma.walkFromRun hFull
  have hExitFull : (⟨9205,.exit⟩ : Event) ∈ X.tr g := List.mem_of_getElem? he
  have hObserved (ev : Event) (hEv : ev ∈ before) (hMark : barrierMark 4397 ev = true) :
      ev ∈ X.tr g ∧ Thread.Scores.notice ev = some .first := by
    have hD : ev ∈ (X.tr g).drop (j+3) := by
      rw [hEs]
      exact List.mem_append_left _ (List.mem_append_right _ hEv)
    have hIn := List.mem_of_mem_drop hD
    exact ⟨hIn,markerIsNotice hFullWalk hExitFull (by decide) Flow.code_4397 rfl
      hIn (beq_iff_eq.mp hMark)⟩
  have hCount : before.countP blockNotice = 1 := by
    rw [← hFirstNotice]
    apply List.countP_congr
    intro ev hEv
    constructor
    · intro hb
      apply beq_iff_eq.mpr
      have h := blockNoticeSites hb
      have hSite := hSites ev hEv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      omega
    · intro hm
      simp [blockNotice, (hObserved ev hEv hm).2]
  obtain ⟨first,hFirstIn,hMark⟩ := List.countP_pos_iff.mp (by rw [hFirstNotice]; decide :
    0 < before.countP (barrierMark 4397))
  obtain ⟨_,hNotice⟩ := hObserved first hFirstIn hMark
  obtain ⟨k,hK⟩ := List.mem_iff_getElem?.mp hFirstIn
  have hKLen := (List.getElem?_eq_some_iff.mp hK).1
  let firstPos := (j+3)+(waits.length+k)
  have hGet : X.get (g,firstPos) = some first := by
    change (X.tr g)[(j+3)+(waits.length+k)]? = some first
    rw [← List.getElem?_drop,hEs,List.append_assoc,List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left,List.getElem?_append_left hKLen]
    exact hK
  have hPub : Thread.Scores.Publishes X (g,firstPos) .first := ⟨first,hGet,hNotice⟩
  have hSources := statsBarrierSources hp hX ⟨Prologue.warpIndex l g,hWarp⟩
  have hZero := (Thread.Scores.notificationOrdinal hp hX hWarp (j := firstPos)).trans
    (Thread.Scores.firstOrdinal hp hX hPub hSources)
  rw [Thread.Scores.beforeNotices] at hZero
  have hBeforeFirst := (blockNoticeLe ((X.tr g).take firstPos)).trans_eq hZero
  have hStartBefore : j+3+waits.length ≤ firstPos := by dsimp [firstPos]; omega
  have hStartZero := (countP_take_mono blockNotice (X.tr g) hStartBefore).trans hBeforeFirst
  rw [List.take_add,hEs,List.append_assoc,List.take_append_length,List.countP_append] at hStartZero
  have hSuffix := congrArg (List.countP blockNotice) hEs
  simp only [List.countP_append] at hSuffix
  have hAll := congrArg (List.countP blockNotice)
    (List.take_append_drop (j+3) (X.tr g))
  simp only [List.countP_append] at hAll
  have hLen := Execution.exit_last hX hg he
  change index+1 = (X.tr g).length at hLen
  have hEndLength : ((X.tr g).drop index).length = 1 := by
    rw [List.length_drop, ← hLen]
    omega
  have hEndHead : ((X.tr g).drop index)[0]? = some ⟨9205,.exit⟩ := by
    rw [List.getElem?_drop,Nat.add_zero]
    exact he
  have hEnd : (X.tr g).drop index = [⟨9205,.exit⟩] := by
    cases h : (X.tr g).drop index with
    | nil => simp [h] at hEndHead
    | cons x rest =>
      simp only [h, List.getElem?_cons_zero, Option.some.injEq] at hEndHead
      simp [h] at hEndLength
      rw [hEndHead,hEndLength]
  have hPrefix := congrArg (List.countP blockNotice)
    (List.take_append_drop index (X.tr g))
  simp only [List.countP_append, hEnd, List.countP_cons, List.countP_nil] at hPrefix
  have hNotNotice : blockNotice ⟨9205,.exit⟩ = false := rfl
  simp only [hNotNotice, Bool.false_eq_true, ite_false, Nat.add_zero] at hPrefix
  have hBlocks : 0 < blocks := hBounds.1
  change rest.countP blockNotice = blocks-1 at hRepeat
  have hBlockCount : ((X.tr g).take index).countP blockNotice = blocks := by omega
  obtain ⟨z,_,f,hFinal,hFinalNotice⟩ :=
    Thread.Scores.finalPublicationOfExit hp hX hPub ⟨index,_,he,rfl⟩
  have hFinalPub : Thread.Scores.Publishes X (g,z) .final := ⟨f,hFinal,hFinalNotice⟩
  have hNoFinalBefore : ((X.tr g).take z).countP finalNotice = 0 := by
    apply List.countP_eq_zero.mpr
    intro ev hEv hm
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hEv
    have hiLen := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_take] at hiLen
    have hiBefore : i < z := by omega
    rw [List.getElem?_take_of_lt hiBefore] at hi
    exact Thread.Scores.noPublicationAfterFinal hX
      (show Thread.Scores.Publishes X (g,i) .final from ⟨ev,hi,beq_iff_eq.mp hm⟩)
      hiBefore hFinalPub
  have hNoFinalAfter : ((X.tr g).drop (z+1)).countP finalNotice = 0 := by
    apply List.countP_eq_zero.mpr
    intro ev hEv hm
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hEv
    rw [List.getElem?_drop] at hi
    exact Thread.Scores.noPublicationAfterFinal hX hFinalPub (by omega : z < z+1+i)
      (show Thread.Scores.Publishes X (g,z+1+i) .final from ⟨ev,hi,beq_iff_eq.mp hm⟩)
  have hFullFinal : (X.tr g).countP finalNotice = 1 := by
    conv_lhs => rw [← List.take_append_drop (z+1) (X.tr g)]
    rw [List.countP_append,countP_take_succ (p := finalNotice) hFinal
      (show finalNotice f = true from beq_iff_eq.mpr hFinalNotice),
      hNoFinalBefore,hNoFinalAfter]
  have hFullBlock : (X.tr g).countP blockNotice = blocks := hPrefix.symm.trans hBlockCount
  have hFinalAtExit : ((X.tr g).take index).countP finalNotice = 1 := by
    have hSplit := congrArg (List.countP finalNotice) (List.take_append_drop index (X.tr g))
    simpa [List.countP_append,hEnd,finalNotice,Thread.Scores.notice] using hSplit.trans hFullFinal
  refine ⟨batch,hBatch,hLo,hHi,?_,?_,?_,?_⟩
  · rw [Thread.Scores.beforeNotices,countStatsSplit]
    change _ = blocks+1
    rw [hBlockCount,hFinalAtExit]
  · rw [Thread.Scores.beforeNotices]
    change ((X.tr g).take (X.tr g).length).countP _ = blocks+1
    rw [List.take_length,countStatsSplit,hFullBlock,hFullFinal]

  · have hStats : ((X.tr g).take index).countP blockNotice ≤
        ((X.tr g).take index).countP scoredStatisticsMark := by
      apply List.countP_mono_left
      intro ev _ hNotice
      simpa only [scoredStatisticsMark, List.contains_iff_mem] using blockNoticeSites hNotice
    have hBudget := precedingStatisticsScoreBudget hX he
    dsimp only at hBudget
    let stage : Fin 2 := ⟨Prologue.warpIndex l g / 4, by omega⟩
    have hMark : scoreAcquireMark = phaseAcquired true :=
      funext fun e => (scoreReadyMarkKind e).symm
    rw [hMark, Thread.Scores.scoreCount hp hX stage hWarp rfl rfl] at hBudget
    have hMono := (List.take_sublist (l := X.tr g) (i := index)).countP_le
      (p := okPoll (Thread.Scores.scoreReadyObject l (g/l.block) stage))
    change blocks ≤ okPolls (Thread.Scores.scoreReadyObject l (g/l.block) stage) (X.tr g)
    rw [← hBlockCount]
    exact hStats.trans (hBudget.trans hMono)

  · let start := j+3+waits.length
    have hBeforeStart : start ≤ firstPos := hStartBefore
    have hBeforeFirstRound : ((X.tr g).take start).countP (barrierMark 6532) = 0 := by
      apply List.countP_eq_zero.mpr
      intro event hm hmPc
      obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hm
      have hKLen := (List.getElem?_eq_some_iff.mp hk).1
      simp only [List.length_take] at hKLen
      have hK : k < start := by omega
      rw [List.getElem?_take_of_lt hK] at hk
      have hEarly : first.pc < 5006 := hSites first hFirstIn
      have hLate : 5006 ≤ event.pc := by
        rw [show event.pc = 6532 from beq_iff_eq.mp hmPc]
        decide
      exact (Nat.not_lt_of_ge (show k ≤ firstPos by omega))
        (Thread.traceOrderOfPcFloor hX staysAfterFirstRound firstRoundSegments hGet hk hEarly hLate)
    have hBeforeLoop : before.countP (barrierMark 6532) = 0 := by
      apply List.countP_eq_zero.mpr
      intro event hm hmPc
      have hPc : event.pc = 6532 := beq_iff_eq.mp hmPc
      have := hSites event hm
      omega
    have hTail : (X.tr g).drop start = before ++ rest := by
      dsimp [start]
      rw [← List.drop_drop, hEs, List.append_assoc, List.drop_append_length]
    have hCount := biasedCreditCountOfRepeatedGeometry hBounds.1 hBounds.2.1
      hBounds.2.2.1 hBounds.2.2.2.1 hAt hWalk hExit'
    have hStageNear : blocks ≤ stageGeometryBlocks p batch tile stage+1 := by
      have hs := stage.isLt
      dsimp [blocks,Mma.trips,stageGeometryBlocks]
      omega
    have hCap : cap ≤ 11 := by unfold cap; omega
    have hLimit : firstBiasedRepeats blocks cap ≤ 10 := by
      unfold firstBiasedRepeats firstPlainSplit
      omega
    have hExact : (X.tr g).countP (barrierMark 6532) = firstBiasedRepeats blocks cap := by
      rw [← List.take_append_drop start (X.tr g), List.countP_append, hBeforeFirstRound, hTail,
        List.countP_append, hBeforeLoop, hCount]
      simp [blocks, cap, tile]
    exact ⟨hExact.symm ▸ hLimit, ⟨firstPos,hPub⟩, ⟨z,hFinalPub⟩, hExact⟩

/-- An exiting active lane published statistics once per selected block plus
one final notification. -/
theorem exitedActivePublicationCount (hExit : stop.kind = .exit) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      (Thread.Scores.before X (g,index)).notices =
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 + 1 ∧
      (Thread.Scores.before X (g,(X.tr g).length)).notices =
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 + 1 := by
  obtain ⟨batch, hb, hLo, hHi, hBefore, hFull, _⟩ :=
    exitedActivePublicationAndScoreCount hp hX hg hWarp hWork hCuQ hUsedK he hExit
  exact ⟨batch, hb, hLo, hHi, hBefore, hFull⟩
end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hw : Prologue.warpIndex l g < 8) (hWork : g/l.block < tilePrefix p p.batch*p.heads)
    (hCuQ : DrainCuQProtected p X)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k))
include hp hX hg hw hWork hCuQ hUsedK

/-- An exited softmax lane in an active CTA acquired every score round. -/
theorem exitedActiveScorePollExtent (hExit : Thread.Exited X g) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 ≤
        okPolls (Thread.Scores.scoreReadyObject l (g/l.block) ⟨Prologue.warpIndex l g/4, by omega⟩)
          (X.tr g) := by
  obtain ⟨_, _, he, hx⟩ := hExit
  obtain ⟨batch, hb, hLo, hHi, _, _, hScore, _⟩ :=
    exitedActivePublicationAndScoreCount hp hX hg hw hWork hCuQ hUsedK he hx
  exact ⟨batch, hb, hLo, hHi, hScore⟩

/-- The completed biased loop issues at most ten recurring early probability credits. -/
theorem exitedActiveBiasedCreditCap (hExit : Thread.Exited X g) :
    (X.tr g).countP (barrierMark 6532) ≤ 10 := by
  obtain ⟨_,_,he,hEnd⟩ := hExit
  obtain ⟨_,_,_,_,_,_,_,hCount,_⟩ :=
    exitedActivePublicationAndScoreCount hp hX hg hw hWork hCuQ hUsedK he hEnd
  exact hCount

/-- The selected active lane records its opening, terminal and repeated publication extent. -/
theorem exitedActiveBarrierExtent (hExit : Thread.Exited X g) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1) * p.heads ∧
      (∃ i, Thread.Scores.Publishes X (g,i) .first) ∧
      (∃ i, Thread.Scores.Publishes X (g,i) .final) ∧
      (Thread.Scores.before X (g,(X.tr g).length)).notices =
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 + 1 ∧
      let tile := (assignedCoordinates p batch (g/l.block)).1
      let blocks := Mma.trips p batch tile
      let stage := stageOf ⟨Prologue.warpIndex l g,hw⟩
      (X.tr g).countP (barrierMark 6532) =
        firstBiasedRepeats blocks (blocks - stageGeometryBlocks p batch tile stage + 10) := by
  obtain ⟨_,_,he,hEnd⟩ := hExit
  obtain ⟨batch,hb,hLo,hHi,_,hNotices,_,_,hFirst,hFinal,hCount⟩ :=
    exitedActivePublicationAndScoreCount hp hX hg hw hWork hCuQ hUsedK he hEnd
  exact ⟨batch,hb,hLo,hHi,hFirst,hFinal,hNotices,hCount⟩
end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {stop : Event}
    (hg : g < l.threads) (hWarp : Prologue.warpIndex l g < 8)
    (hFirst : g / l.block < tilePrefix p (min p.batch 31) * p.heads)
    (hCuQ : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4*i)).at k))
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k)) (he : X.get (g,index) = some stop)
include hp hX hg hWarp hFirst hCuQ hUsedK he

end

private theorem reachThenWalk {l : Launch} {g : Nat} {start finish : TState}
    {before rest : List Event} {vs : List Visit}
    (hr : TraceReach kernel Assumptions.all l g start before finish)
    (hw : Walk kernel Assumptions.all l g finish rest vs) :
    ∃ trail, Walk kernel Assumptions.all l g start (before ++ rest) trail := by
  induction hr with
  | refl => exact ⟨vs,hw⟩
  | tau h _ ih =>
    obtain ⟨_,hTrail⟩ := ih hw
    exact ⟨_,.tau h hTrail⟩
  | event h _ ih =>
    obtain ⟨_,hTrail⟩ := ih hw
    exact ⟨_,.ev h hTrail⟩

private theorem publicationPrefixThrough {l : Launch} {g index : Nat} {s : TState}
    {result : Option TState} {es : List Event} {target : Event}
    (hr : Run kernel Assumptions.all l g s es result) (he : es[index]? = some target) :
    ∃ vs, Walk kernel Assumptions.all l g s (es.take index ++ [target]) vs := by
  obtain ⟨t,q,hReach,hStep⟩ := hr.before_event he
  cases q with
  | none => exact reachThenWalk hReach (.last hStep)
  | some u => exact reachThenWalk hReach (.ev hStep (.stop u))

private theorem finalPublicationSite {e : Event} (h : Thread.Scores.notice e = some .final) :
    e.pc = 7616 := by
  unfold Thread.Scores.notice at h
  split at h <;> try contradiction
  unfold Thread.Scores.noticeRound at h
  split at h <;> simp_all

private theorem markBeforePublicationIsNotice {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {target : Event} (hTarget : X.get (g,j) = some target)
    {e : Event} (he : e ∈ (X.tr g).take j) (hm : scoredStatisticsMark e = true) :
    Thread.Scores.publishesStats e = true := by
  obtain ⟨k,hGet⟩ := List.mem_iff_getElem?.mp he
  have hk := (List.getElem?_eq_some_iff.mp hGet).1
  simp only [List.length_take] at hk
  have hK : k < j := by omega
  rw [List.getElem?_take_of_lt hK] at hGet
  have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hTarget).1
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX hTarget)
  obtain ⟨_,_,hStep,_⟩ := hRun.after_event hGet (by omega)
  simp only [scoredStatisticsMark,List.contains_iff_mem,List.mem_cons,List.not_mem_nil,
    or_false] at hm
  rcases hm with h0 | h1 | h2
  · have h := noticeOfContinuingBarrier (round := .first) hStep h0 Flow.code_4397 rfl
    simp [Thread.Scores.publishesStats,h]
  · have h := noticeOfContinuingBarrier (round := .biased) hStep h1 Flow.code_5683 rfl
    simp [Thread.Scores.publishesStats,h]
  · have h := noticeOfContinuingBarrier (round := .plain) hStep h2 Flow.code_6891 rfl
    simp [Thread.Scores.publishesStats,h]

/-- A final actual statistics publication follows at least one publication
for each KV block of the producer's selected tile, even if the lane has not exited. -/
theorem finalPublicationOrdinalLower {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} (hw : Prologue.warpIndex l g < 8)
    (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hCuQ : DrainCuQProtected p X)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k))
    (hPub : Thread.Scores.Publishes X (g,index) .final) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 ≤
        (Thread.Scores.before X (g,index)).notices := by
  obtain ⟨target,he,hNotice⟩ := hPub
  have hSite := finalPublicationSite hNotice
  have hLate : 7605 ≤ target.pc := by omega
  let lane := laneOf l g
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  obtain ⟨batch,hb,hLo,hHi,j,s,_,hReads,hAt,hr,hJ,_⟩ :=
    activeGeometryOfLateEvent hp hX (event_thread_lt hX he) hw
      (show lane < 32 from Nat.mod_lt _ (by decide)) hWork hCuQ hUsedK (hLane.symm ▸ he) hLate
  rw [hLane] at hr
  let tr := (X.tr g).drop (j+3)
  let k := index-(j+3)
  have hGet : tr[k]? = some target := by
    dsimp [tr,k]
    rwa [List.getElem?_drop,Nat.add_sub_of_le hJ]
  obtain ⟨_,hTrace⟩ := publicationPrefixThrough hr hGet
  let warp : Fin 8 := ⟨Prologue.warpIndex l g,hw⟩
  let stage := stageOf warp
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  obtain ⟨u,waits,first,rest,path,hEs,hFound,hFirst,hCounter,hWalk,_⟩ :=
    firstGeometryCounterWalkOfLateEvent hp stage hb hTile hAt hTrace (by simp) hLate
  have hBounds := firstGeometryBounds hp stage hb hTile (lane := 0) (by decide)
  have hRepeated :=
    repeatedMarksBeforeLate hBounds.1 hBounds.2.1 hBounds.2.2.1 hBounds.2.2.2.1
      hCounter hWalk hFound hLate
  have hMarkFirst : 1 ≤ first.countP scoredStatisticsMark := by
    rw [← hFirst]
    apply List.countP_mono_left
    intro e _ h
    have hPc : e.pc = 4397 := beq_iff_eq.mp h
    simp [scoredStatisticsMark,hPc]
  have hTarget : scoredStatisticsMark target = false := by simp [scoredStatisticsMark,hSite]
  have hEq := congrArg (List.countP scoredStatisticsMark) hEs
  simp only [List.countP_append,List.countP_singleton,hTarget,Bool.false_eq_true,
    ite_false,Nat.add_zero] at hEq
  let blocks := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  change blocks-1 ≤ rest.countP scoredStatisticsMark at hRepeated
  have hPos : 0 < blocks := hBounds.1
  change (tr.take k).countP scoredStatisticsMark = waits.countP scoredStatisticsMark +
    first.countP scoredStatisticsMark + rest.countP scoredStatisticsMark at hEq
  have hBlockCount : blocks ≤ (tr.take k).countP scoredStatisticsMark := by omega
  have hSubset : (tr.take k).countP scoredStatisticsMark ≤
      ((X.tr g).take index).countP scoredStatisticsMark := by
    have hSplit := List.take_add (l := X.tr g) (i := j+3) (j := k)
    have hSum : j+3+k = index := Nat.add_sub_of_le hJ
    rw [hSum] at hSplit
    rw [hSplit,List.countP_append]
    exact Nat.le_add_left _ _
  have hCount : ((X.tr g).take index).countP scoredStatisticsMark ≤
      ((X.tr g).take index).countP Thread.Scores.publishesStats :=
    List.countP_mono_left (fun _ hMem hMark => markBeforePublicationIsNotice hX he hMem hMark)
  refine ⟨batch,hb,hLo,hHi,?_⟩
  rw [Thread.Scores.beforeNotices]
  exact hBlockCount.trans (hSubset.trans hCount)

end PTX.Kernels.TmlFa4Fwd.Softmax
