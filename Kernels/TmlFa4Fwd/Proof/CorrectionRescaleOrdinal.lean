-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescalePrefix
public import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Flow.Code.Part124
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Lemmas.Flow.EventCont

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Mma Softmax

/-- Each correction rescale feedback loop waits at one instruction per stage. -/
def correctionRescaleMarkPc (stage : Fin 2) : Nat :=
  if stage.val = 0 then 8006 else 8225

/-- The event marker of a rescale wait for a fixed stage. -/
def isRescaleStageWait (stage : Fin 2) : Event → Bool := barrierMark (correctionRescaleMarkPc stage)

/-- A ballot of the rescale loop, excluding ballots of the scheduler. -/
def isRescaleStageVote (stage : Fin 2) : Event → Bool :=
  barrierMark (correctionRescaleMarkPc stage + 3)

private def rescaleMark (vote : Bool) (stage : Fin 2) : Nat :=
  correctionRescaleMarkPc stage + if vote then 3 else 0

private def remaining (vote : Bool) (stage : Fin 2) (t : TState) : Nat :=
  barrierRemaining (rescaleMark vote stage) t

private def correctedRegion (steps : Nat) (t : TState) : Prop :=
  8006 ≤ t.pc ∧ t.pc ≤ 8444 ∧ t.sub ≤ 3 ∧
    t.regs 7278 = some (b32 (2^32-steps)) ∧ (t.pc = 8444 → t.fault = none)

private theorem markCode (stage : Fin 2) :
    kernel.code[correctionRescaleMarkPc stage]? =
      some ⟨none, .barSyncN (.reg (1625+stage.val)) (.imm 64) true⟩ := by
  fin_cases stage
  · exact Flow.code_8006
  · exact Flow.code_8225

private def rescaleBallotCode (stage : Fin 2) : Instr :=
  ⟨none, .warp ⟨.vote .ballot false, some (.int .b 32),
    [some (if stage.val = 0 then 5979 else 6237)],
    [.reg (731 + 2 * stage.val)], some (.imm (-1))⟩⟩

private theorem rescaleBallotAt (stage : Fin 2) :
    kernel.code[rescaleMark true stage]? = some (rescaleBallotCode stage) := by
  fin_cases stage
  · exact Flow.code_8009
  · exact Flow.code_8228

private theorem rescaleBallotContinues {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (stage : Fin 2) (hPc : s.pc = rescaleMark true stage)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc + 1 := by
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
  rw [hPc, rescaleBallotAt stage] at hCode
  obtain rfl := Option.some.inj hCode
  unfold rescaleBallotCode at hFire
  cases hp : readPred l g s (.reg (731 + 2 * stage.val)) with
  | error fault =>
    simp [eventTmpl, warpTmpl_vote, voteTmpl, hp, readBits, pure, Except.pure,
      Fires] at hFire
  | ok input =>
    obtain ⟨_,_,_,rfl⟩ := fires_vote hp hFire
    rfl

/-- The returning instruction at either rescale ballot advances to its decision. -/
theorem rescaleVoteContinues {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (stage : Fin 2) (hPc : s.pc = correctionRescaleMarkPc stage + 3)
    (he : EStep kernel Assumptions.all l g s e (some u)) : u.pc = s.pc + 1 :=
  rescaleBallotContinues stage hPc he

private def roleBranchKeepsMark (vote : Bool) (stage : Fin 2) (src : Nat) (op : Op) : Bool :=
  match op with
  | .bra dst _ => decide (src ≤ rescaleMark vote stage ↔ dst ≤ rescaleMark vote stage)
  | .brx .. => false
  | _ => true

private theorem branchKeepsMarkAt (vote : Bool) (stage : Fin 2) {pc : Nat} {ins : Instr}
    (hLo : 8006 ≤ pc) (hHi : pc < 8444) (hC : kernel.code[pc]? = some ins) :
    roleBranchKeepsMark vote stage pc ins.op = true := by
  let code := ((kernel.code.drop 8006).take (8444-8006)).zipIdx 8006
  have hAll : code.all (fun (i, pc) => roleBranchKeepsMark vote stage pc i.op) = true := by
    cases vote <;> fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (ins, pc)
  apply List.mem_of_getElem? (i := pc-8006)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hC]
  rfl

private theorem remainingStep {l : Launch} {g steps : Nat} {s u : TState}
    {ev : Option Event} (vote : Bool) (stage : Fin 2) (hs : correctedRegion steps s)
    (hCut : s.pc ≠ 8444) (hStep : WStep kernel Assumptions.all l g s ev u) :
    correctedRegion steps u ∧ remaining vote stage s =
      ev.toList.countP (barrierMark (rescaleMark vote stage)) + remaining vote stage u := by
  obtain ⟨hl, hh, hSub, hWord, _⟩ := hs
  have hHi : s.pc < 8444 := by omega
  obtain ⟨hP, hRange, hR⟩ := correctionLinearStep 3 hl hHi hSub hStep
  have hAt : correctedRegion steps u := by
    change (8006 ≤ u.pc ∧ u.pc < 8444 ∨ u.pc ∈ [8444] ∧ u.fault = none) at hRange
    rcases hRange with ⟨hLow,hHigh⟩ | ⟨hExit, hf⟩
    · exact ⟨hLow, by omega, hP.sub, hR.trans hWord, fun h => (by omega : False).elim⟩
    · have h := List.mem_singleton.mp hExit
      exact ⟨by omega, by omega, hP.sub, hR.trans hWord, fun _ => hf⟩
  refine ⟨hAt, markedEventTransition (pc := rescaleMark vote stage)
    ?_ ?_ ?_ ?_ ?_ hStep⟩
  · cases vote
    · exact ⟨_, markCode stage, rfl, rfl⟩
    · exact ⟨_, rescaleBallotAt stage, rfl, rfl⟩
  · cases vote
    · exact fun hs {_} he => followsMarkedBarrier hs (markCode stage) rfl he
    · exact fun hs {_} he => rescaleBallotContinues stage hs he
  · intro ins dst uni hc ho
    simpa only [roleBranchKeepsMark, ho, decide_eq_true_eq] using
      branchKeepsMarkAt vote stage hl hHi hc
  · intro ins index ds uni hc ho
    simpa [roleBranchKeepsMark, ho] using branchKeepsMarkAt vote stage hl hHi hc
  · intro m hSite _
    simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hSite
    omega

variable {l : Launch} {g steps : Nat} {s : TState}

private theorem cutRescalePass {es : List Event} {vs : List Visit} (vote : Bool) (stage : Fin 2)
    (hs : correctedRegion steps s) (hw : Walk kernel Assumptions.all l g s es vs) :
    (es.countP (barrierMark (rescaleMark vote stage)) ≤ remaining vote stage s ∧
      ∀ e ∈ es, e.pc < 8444) ∨
      ∃ u pre rest tail, es = pre ++ rest ∧ correctedRegion steps u ∧ u.pc = 8444 ∧
        pre.countP (barrierMark (rescaleMark vote stage)) = remaining vote stage s ∧
        (∀ e ∈ pre, e.pc < 8444) ∧ Walk kernel Assumptions.all l g u rest tail := by
  have atCut (t : TState) (ht : t.pc = 8444) : remaining vote stage t = 0 := by
    unfold remaining barrierRemaining
    rw [ht]
    cases vote <;> fin_cases stage <;> decide
  induction hw with
  | stop => simp
  | @tau t u es vs ht hw ih =>
    by_cases hCut : t.pc = 8444
    · exact .inr ⟨t, [], es, _, rfl, hs, hCut, (atCut t hCut).symm, by simp, .tau ht hw⟩
    obtain ⟨hu, hRank⟩ := remainingStep vote stage hs hCut (.inl ⟨rfl,ht⟩)
    simp only [Option.toList_none, List.countP_nil, Nat.zero_add] at hRank
    simpa only [hRank] using ih hu
  | @ev t u e es vs he hw ih =>
    by_cases hCut : t.pc = 8444
    · exact .inr ⟨t, [], e::es, _, rfl, hs, hCut, (atCut t hCut).symm, by simp, .ev he hw⟩
    obtain ⟨hu, hRank⟩ := remainingStep vote stage hs hCut (.inr ⟨e,rfl,he⟩)
    rw [Option.toList_some, List.countP_cons, List.countP_nil, Nat.zero_add] at hRank
    have hBound : e.pc < 8444 := by
      have hPc := estep_source_pc he
      have hHi := hs.2.1
      omega
    rcases ih hu with hShort | ⟨v, pre, rest, tail, hEs, hv, hCut', hPre, hBefore, hWalk⟩
    · refine .inl ⟨?_, ?_⟩
      · rw [List.countP_cons, hRank]
        omega
      · intro event hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hBound
        · exact hShort.2 event hm
    · refine .inr ⟨v, e::pre, rest, tail, by rw [hEs]; rfl, hv, hCut', ?_, ?_, hWalk⟩
      · rw [List.countP_cons, hPre, hRank]
        omega
      · intro event hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hBound
        · exact hBefore event hm
  | @last t e he =>
    by_cases hCut : t.pc = 8444
    · exact .inr ⟨t, [], [e], _, rfl, hs, hCut, (atCut t hCut).symm, by simp, .last he⟩
    refine .inl ⟨?_, ?_⟩
    · unfold barrierMark remaining barrierRemaining
      simp only [List.countP_cons, List.countP_nil, estep_source_pc he]
      by_cases hEq : t.pc = rescaleMark vote stage <;> simp [hEq]
    · intro event hm
      obtain rfl := List.mem_singleton.mp hm
      have hPc := estep_source_pc he
      have hHi := hs.2.1
      omega

/-- Every rescale prefix is within the seeded wait budget, or factors through the exact
rescale fallthrough after consuming the entire budget. -/
private theorem correctionMarkedPrefix {es : List Event} {vs : List Visit} (vote : Bool)
    (stage : Fin 2) (hPc : s.pc = 8006) (hSub : s.sub ≤ 3) (hLo : 2 ≤ steps) (hHi : steps ≤ 2^32)
    (hReg : s.regs 7278 = some (b32 (2^32-steps))) (hw : Walk kernel Assumptions.all l g s es vs) :
    (es.countP (barrierMark (rescaleMark vote stage)) ≤ steps - 1 ∧ ∀ e ∈ es, e.pc < 8447) ∨
      ∃ u pre rest tail, es = pre ++ rest ∧ u.pc = 8447 ∧
        pre.countP (barrierMark (rescaleMark vote stage)) = steps - 1 ∧
        (∀ e ∈ pre, e.pc < 8447) ∧ Walk kernel Assumptions.all l g u rest tail := by
  induction steps using Nat.strong_induction_on generalizing s es vs with
  | h steps ih =>
    have hs : correctedRegion steps s := ⟨hPc.ge, by omega, hSub, hReg,
      fun h => (by omega : False).elim⟩
    have hOne : remaining vote stage s = 1 := by
      unfold remaining barrierRemaining
      rw [hPc]
      cases vote <;> fin_cases stage <;> decide
    rcases cutRescalePass vote stage hs hw with hShort |
      ⟨v, pre, rest, tail, hEs, hv, hvPc, hPre, hBefore, hW⟩
    · refine .inl ⟨by omega, fun e he => (hShort.2 e he).trans (by decide)⟩
    obtain ⟨u, hRun, hup, _, huSub, huReg⟩ :=
      rescaleCounterStep hvPc (hv.2.2.2.2 hvPc) hv.2.2.2.1 hLo hHi
    rcases advanceWalkLocals hRun hW with rfl | ⟨post, _, _, hRest⟩
    · refine .inl ⟨?_, ?_⟩
      · rw [hEs, List.append_nil, hPre]
        omega
      · intro e he
        rw [hEs, List.append_nil] at he
        exact (hBefore e he).trans (by decide)
    by_cases hEnd : steps = 2
    · exact .inr ⟨u, pre, rest, post, hEs, by simpa only [hEnd, ↓reduceIte] using hup,
        by omega, fun e he => (hBefore e he).trans (by decide), hRest⟩
    have hBack : u.pc = 8006 := by simpa only [hEnd, ↓reduceIte] using hup
    rcases ih (steps-1) (by omega) hBack (huSub.trans hv.2.2.1) (by omega) (by omega)
      huReg hRest with hShort | ⟨t, middle, after, walk, hSplit, hLast, hMid, hMidBefore, ht⟩
    · refine .inl ⟨?_, ?_⟩
      · rw [hEs, List.countP_append, hPre]
        omega
      · intro e he
        rw [hEs] at he
        rcases List.mem_append.mp he with he | he
        · exact (hBefore e he).trans (by decide)
        · exact hShort.2 e he
    · refine .inr ⟨t, pre ++ middle, after, walk, by rw [hEs, hSplit, List.append_assoc],
        hLast, ?_, ?_, ht⟩
      · rw [List.countP_append, hPre, hOne, hMid]
        omega
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact (hBefore e he).trans (by decide)
        · exact hMidBefore e he

/-- The rescale wait count is bounded on prefixes and exact at the loop exit. -/
theorem correctionRescaleMarkedPrefix {es : List Event} {vs : List Visit} (stage : Fin 2)
    (hPc : s.pc = 8006) (hSub : s.sub ≤ 3) (hLo : 2 ≤ steps) (hHi : steps ≤ 2^32)
    (hReg : s.regs 7278 = some (b32 (2^32-steps))) (hw : Walk kernel Assumptions.all l g s es vs) :
    (es.countP (isRescaleStageWait stage) ≤ steps - 1 ∧ ∀ e ∈ es, e.pc < 8447) ∨
      ∃ u pre rest tail, es = pre ++ rest ∧ u.pc = 8447 ∧
        pre.countP (isRescaleStageWait stage) = steps - 1 ∧
        (∀ e ∈ pre, e.pc < 8447) ∧ Walk kernel Assumptions.all l g u rest tail :=
  correctionMarkedPrefix false stage hPc hSub hLo hHi hReg hw

/-- Each completed rescale pass contributes exactly one ballot for each stage. -/
theorem correctionRescaleVotePrefix {es : List Event} {vs : List Visit} (stage : Fin 2)
    (hPc : s.pc = 8006) (hSub : s.sub ≤ 3) (hLo : 2 ≤ steps) (hHi : steps ≤ 2^32)
    (hReg : s.regs 7278 = some (b32 (2^32-steps))) (hw : Walk kernel Assumptions.all l g s es vs) :
    (es.countP (isRescaleStageVote stage) ≤ steps - 1 ∧ ∀ e ∈ es, e.pc < 8447) ∨
      ∃ u pre rest tail, es = pre ++ rest ∧ u.pc = 8447 ∧
        pre.countP (isRescaleStageVote stage) = steps - 1 ∧
        (∀ e ∈ pre, e.pc < 8447) ∧ Walk kernel Assumptions.all l g u rest tail :=
  correctionMarkedPrefix true stage hPc hSub hLo hHi hReg hw

private def staysAtOrAfter (cutoff : Nat) (op : Op) : Bool :=
  (op.isLocal || Epilogue.ordinaryEvent op) &&
    match op with
    | .bra dst _ => decide (cutoff ≤ dst)
    | .brx .. => false
    | _ => true

private theorem staysAtOrAfterAt {cutoff : Nat} {s : TState} {i : Instr}
    (hAudit : (kernel.code.drop cutoff).all (fun ins => staysAtOrAfter cutoff ins.op) = true)
    (hPc : cutoff ≤ s.pc) (hc : kernel.code[s.pc]? = some i) :
    staysAtOrAfter cutoff i.op = true := by
  have hm : i ∈ kernel.code.drop cutoff := by
    apply List.mem_of_getElem? (i := s.pc - cutoff)
    rwa [List.getElem?_drop, Nat.add_sub_of_le hPc]
  exact List.all_eq_true.mp hAudit i hm

private theorem staysAtOrAfterStep {l : Launch} {g cutoff : Nat} {s u : TState}
    {e : Option Event} (hStrict : 7746 ≤ cutoff)
    (hAudit : (kernel.code.drop cutoff).all (fun ins => staysAtOrAfter cutoff ins.op) = true)
    (hPc : cutoff ≤ s.pc) (hStep : WStep kernel Assumptions.all l g s e u) : cutoff ≤ u.pc := by
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, _, hs⟩ := correctionTauFrame hOff ht
    rcases hs with ⟨rfl, _⟩ | ⟨_, _, hf⟩
    · exact hPc.trans (Nat.le_succ _)
    · have hCode := staysAtOrAfterAt hAudit hPc hc
      simp only [staysAtOrAfter, Bool.and_eq_true] at hCode
      have hBranch := hCode.2
      have hNext := hf.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hNext
      case bra dst uni =>
        rw [hNext]
        simpa only [ho, decide_eq_true_eq] using hBranch
      case brx => simp [ho] at hBranch
      all_goals omega
  · obtain ⟨i, hc, hLocal, hf⟩ := estep_event_source he
    have hCode := staysAtOrAfterAt hAudit hPc hc
    simp only [staysAtOrAfter, Bool.and_eq_true] at hCode
    have hFrame := Epilogue.ordinaryEventFrame
      (A := Assumptions.all) (l := l) (g := g) (s := s)
      (by simpa only [hLocal, Bool.false_or] using hCode.1)
    rcases callbackFrame_fires hFrame hf with h | h <;> omega

private theorem afterCorrectionEvents {l : Launch} {g cutoff : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hStrict : 7746 ≤ cutoff)
    (hAudit : (kernel.code.drop cutoff).all (fun ins => staysAtOrAfter cutoff ins.op) = true)
    (hPc : cutoff ≤ s.pc) (hw : Walk kernel Assumptions.all l g s es vs) :
    ∀ e ∈ es, cutoff ≤ e.pc := by
  have hStep {s u : TState} {ev : Option Event} (h : cutoff ≤ s.pc)
      (he : WStep kernel Assumptions.all l g s ev u) : cutoff ≤ u.pc :=
    staysAtOrAfterStep hStrict hAudit h he
  induction hw with
  | stop => simp
  | tau ht _ ih => exact ih (hStep hPc (.inl ⟨rfl, ht⟩))
  | ev he _ ih =>
    intro e hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rwa [estep_source_pc he]
    · exact ih (hStep hPc (.inr ⟨_, rfl, he⟩)) _ hm
  | last he =>
    intro e hm
    obtain rfl := List.mem_singleton.mp hm
    rwa [estep_source_pc he]

private theorem afterRescaleEvents {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hPc : 8447 ≤ s.pc)
    (hw : Walk kernel Assumptions.all l g s es vs) : ∀ e ∈ es, 8447 ≤ e.pc :=
  afterCorrectionEvents (by decide) (by set_option maxRecDepth 100000 in kernel_rfl) hPc hw

/-- After the first returned statistics credit, the lane never returns to its first release. -/
theorem correctionEventsAfterFirstRelease {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hPc : 7988 ≤ s.pc)
    (hw : Walk kernel Assumptions.all l g s es vs) : ∀ e ∈ es, 7988 ≤ e.pc :=
  afterCorrectionEvents (by decide) (by set_option maxRecDepth 100000 in kernel_rfl) hPc hw

/-- Neither ordinary finalization nor a terminal fault reenters the rescale range. -/
theorem correctionRescaleMarkedNone {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (stage : Fin 2) (hPc : 8447 ≤ s.pc)
    (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP (isRescaleStageWait stage) = 0 := by
  apply List.countP_eq_zero.mpr
  intro e he hm
  have hLate := afterRescaleEvents hPc hw e he
  have hMark : e.pc = correctionRescaleMarkPc stage := beq_iff_eq.mp hm
  have hBefore : correctionRescaleMarkPc stage < 8447 := by fin_cases stage <;> decide
  omega

/-- No rescale ballot is issued after the rescale loop. -/
theorem correctionRescaleVoteNone {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (stage : Fin 2) (hPc : 8447 ≤ s.pc)
    (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP (isRescaleStageVote stage) = 0 := by
  apply List.countP_eq_zero.mpr
  intro e he hm
  have hLate := afterRescaleEvents hPc hw e he
  have hMark : e.pc = correctionRescaleMarkPc stage + 3 := beq_iff_eq.mp hm
  have hBefore : correctionRescaleMarkPc stage + 3 < 8447 := by fin_cases stage <;> decide
  omega

/-- A lane observed in finalization has made one rescale ballot per remaining block and stage. -/
theorem correctionRescaleVoteCount {es : List Event} {vs : List Visit} (stage : Fin 2)
    (hPc : s.pc = 8006) (hSub : s.sub ≤ 3) (hLo : 2 ≤ steps) (hHi : steps ≤ 2^32)
    (hReg : s.regs 7278 = some (b32 (2^32-steps))) (hw : Walk kernel Assumptions.all l g s es vs)
    {target : Event} (hTarget : target ∈ es) (hLate : 8447 ≤ target.pc) :
    es.countP (isRescaleStageVote stage) = steps-1 := by
  rcases correctionRescaleVotePrefix stage hPc hSub hLo hHi hReg hw with hShort |
    ⟨u, pre, rest, tail, hEs, hu, hCount, hBefore, hWalk⟩
  · exact (Nat.not_lt_of_ge hLate (hShort.2 target hTarget)).elim
  rw [hEs,List.countP_append,hCount,correctionRescaleVoteNone stage hu.ge hWalk,Nat.add_zero]

/-- No correction lane can issue more than one rescale wait per remaining KV block. -/
theorem correctionRescaleMarkedBound {es : List Event} {vs : List Visit} (stage : Fin 2)
    (hPc : s.pc = 8006) (hSub : s.sub ≤ 3) (hLo : 2 ≤ steps) (hHi : steps ≤ 2^32)
    (hReg : s.regs 7278 = some (b32 (2^32-steps))) (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP (isRescaleStageWait stage) ≤ steps - 1 := by
  rcases correctionRescaleMarkedPrefix stage hPc hSub hLo hHi hReg hw with h |
    ⟨u, pre, rest, tail, hEs, hu, hCount, _, hWalk⟩
  · exact h.1
  rw [hEs, List.countP_append, hCount, correctionRescaleMarkedNone stage hu.ge hWalk, Nat.add_zero]

/-- The pre-rescale and final named waits each run at most once per correction stage. -/
def correctionSingleStatsPc (stage : Fin 2) (final : Bool) : Nat :=
  if final then (if stage.val = 0 then 8465 else 8761)
  else (if stage.val = 0 then 7985 else 7988)

private theorem singleStatsCode (stage : Fin 2) (final : Bool) :
    kernel.code[correctionSingleStatsPc stage final]? =
      some ⟨none, .barSyncN (.reg (1625+stage.val)) (.imm 64) true⟩ := by
  fin_cases stage <;> cases final
  · exact Flow.code_7985
  · exact Flow.code_8465
  · exact Flow.code_7988
  · exact Flow.code_8761

private def sameSideOf (mark pc : Nat) (op : Op) : Bool :=
  match op with
  | .bra dst _ => decide (pc ≤ mark ↔ dst ≤ mark)
  | .brx .. => false
  | _ => true

private theorem sameSideOfCode (stage : Fin 2) (final : Bool) {pc : Nat} {ins : Instr}
    (hPc : 7985 ≤ pc) (hc : kernel.code[pc]? = some ins) :
    sameSideOf (correctionSingleStatsPc stage final) pc ins.op = true := by
  let code := (kernel.code.drop 7985).zipIdx 7985
  have hAll : code.all (fun (i, p) => sameSideOf (correctionSingleStatsPc stage final) p i.op) =
      true := by
    fin_cases stage <;> cases final <;> set_option maxRecDepth 100000 in kernel_rfl
  have hm : (ins, pc) ∈ code := by
    apply List.mem_of_getElem? (i := pc - 7985)
    dsimp only [code]
    rw [List.getElem?_zipIdx, List.getElem?_drop, Nat.add_sub_of_le hPc, hc]
    rfl
  exact List.all_eq_true.mp hAll _ hm

/-- A non-rescale wait can only be issued once before the lane advances past it. -/
theorem correctionSingleStatsRankBound {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (stage : Fin 2) (final : Bool)
    (hPc : 7985 ≤ s.pc) (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP (barrierMark (correctionSingleStatsPc stage final)) ≤
      barrierRemaining (correctionSingleStatsPc stage final) s := by
  let pc := correctionSingleStatsPc stage final
  have hAudit : (kernel.code.drop 7985).all (fun ins => staysAtOrAfter 7985 ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hStep {s u : TState} {ev : Option Event} (h : 7985 ≤ s.pc)
      (he : WStep kernel Assumptions.all l g s ev u) :
      7985 ≤ u.pc ∧ barrierRemaining pc s =
        ev.toList.countP (barrierMark pc) + barrierRemaining pc u := by
    refine ⟨staysAtOrAfterStep (by decide) hAudit h he,
      markedBarrierTransition ⟨_, singleStatsCode stage final, rfl, rfl⟩ ?_ ?_ ?_ he⟩
    · intro ins dst uni hc ho
      simpa only [sameSideOf, ho, decide_eq_true_eq] using sameSideOfCode stage final h hc
    · intro ins index ds uni hc ho
      simpa [sameSideOf, ho] using sameSideOfCode stage final h hc
    · intro m hSite _
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hSite
      omega
  have hBound : es.countP (barrierMark pc) ≤ barrierRemaining pc s := by
    induction hw with
    | stop => simp
    | tau ht _ ih =>
      obtain ⟨hu, hRank⟩ := hStep hPc (.inl ⟨rfl, ht⟩)
      simpa only [hRank, Option.toList_none, List.countP_nil, Nat.zero_add] using ih hu
    | ev he _ ih =>
      obtain ⟨hu, hRank⟩ := hStep hPc (.inr ⟨_, rfl, he⟩)
      have bound := ih hu
      rw [Option.toList_some, List.countP_cons, List.countP_nil, Nat.zero_add] at hRank
      rw [List.countP_cons, hRank]
      omega
    | @last t e he =>
      unfold barrierRemaining barrierMark
      simp only [List.countP_cons, List.countP_nil, estep_source_pc he]
      by_cases hEq : t.pc = pc <;> simp [hEq]
  exact hBound

/-- An observed correction prefix issues each non-rescale wait at most once. -/
theorem correctionSingleStatsBound {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (stage : Fin 2) (final : Bool)
    (hPc : 7985 ≤ s.pc) (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP (barrierMark (correctionSingleStatsPc stage final)) ≤ 1 :=
  (correctionSingleStatsRankBound stage final hPc hw).trans (by
    unfold barrierRemaining
    split <;> decide)

/-- Before any observed instruction after the rescale pairs, the actual consumer trace has
exactly one wait per stage for each remaining block after the first. -/
theorem correctionRescaleMarkedCount {es : List Event} {vs : List Visit} (stage : Fin 2)
    (hPc : s.pc = 8006) (hSub : s.sub ≤ 3) (hLo : 2 ≤ steps) (hHi : steps ≤ 2^32)
    (hReg : s.regs 7278 = some (b32 (2^32-steps))) (hr : Walk kernel Assumptions.all l g s es vs)
    {target : Event} (hTarget : target ∈ es) (hLate : 8447 ≤ target.pc) :
    ∃ u before rest tail, es = before ++ rest ∧ target ∈ rest ∧ u.pc = 8447 ∧
      before.countP (isRescaleStageWait stage) = steps-1 ∧
      Walk kernel Assumptions.all l g u rest tail := by
  rcases correctionRescaleMarkedPrefix stage hPc hSub hLo hHi hReg hr with hShort |
    ⟨u, pre, rest, tail, hEs, hu, hCount, hBefore, hWalk⟩
  · have h := hShort.2 target hTarget
    omega
  refine ⟨u, pre, rest, tail, hEs, ?_, hu, hCount, hWalk⟩
  rw [hEs] at hTarget
  exact (List.mem_append.mp hTarget).resolve_left (fun hm => Nat.not_lt_of_ge hLate (hBefore _ hm))

end PTX.Kernels.TmlFa4Fwd.Correction
