-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxProbabilityGate
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
import Kernels.TmlFa4Fwd.Proof.Thread.BiasBarrierProgress
import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Lemmas.Flow.EventCont
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Flow.Code.Part055
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part103
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Kernels.TmlFa4Fwd.Flow.Code.Part082
import Kernels.TmlFa4Fwd.Flow.Code.Part102

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue Thread Thread.Scores

private def biasMarkPc (repeated : Bool) : Nat := if repeated then 5271 else 3583

private def earlyMarkPc (repeated : Bool) : Nat := if repeated then 6532 else 4847

private def closingMarkPc (repeated notice : Bool) : Nat :=
  if notice then (if repeated then 5683 else 4397) else earlyMarkPc repeated

private def biasDebt (repeated notice : Bool) (pc : Nat) : Nat :=
  if biasMarkPc repeated < pc ∧ pc ≤ closingMarkPc repeated notice then 1 else 0

private def keepsBiasDebt (repeated notice : Bool) (pc : Nat) (op : Op) : Bool :=
  match op with
  | .bra dst _ => decide (biasDebt repeated notice pc = biasDebt repeated notice dst)
  | .brx .. => false
  | _ => true

private theorem debtBranch (repeated notice : Bool) {pc : Nat} {i : Instr}
    (hCode : kernel.code[pc]? = some i) : keepsBiasDebt repeated notice pc i.op = true := by
  have hTable : (kernel.code.zipIdx 0).all (fun (i,pc) =>
      keepsBiasDebt repeated notice pc i.op) = true := by
    cases repeated <;> cases notice <;> set_option maxRecDepth 100000 in kernel_rfl
  exact List.all_eq_true.mp hTable (i,pc) (List.mem_zipIdx_iff_getElem?.mpr hCode)

private theorem debtSegment (repeated notice : Bool) {pc : Nat} {seg : SegMatch CuteSlot}
    (hSite : pc ∈ Assumptions.swExp2Sites) (hMatch : cuteExp2.matchAt kernel pc = some seg) :
    biasDebt repeated notice pc = biasDebt repeated notice seg.stop := by
  have hTable : Assumptions.swExp2Sites.all (fun pc =>
      (cuteExp2.matchAt kernel pc).any fun seg => decide
        (biasDebt repeated notice pc = biasDebt repeated notice seg.stop)) = true := by
    cases repeated <;> cases notice <;> set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hTable pc hSite
  simpa only [hMatch,Option.any_some,decide_eq_true_eq] using h

private theorem barrierCode (repeated : Bool) :
    ∃ i, kernel.code[biasMarkPc repeated]? = some i ∧ i.guard = none ∧ barOp i.op = true := by
  cases repeated
  · exact ⟨_,Flow.code_3583,rfl,rfl⟩
  · exact ⟨_,Flow.code_5271,rfl,rfl⟩

private theorem closingCode (repeated notice : Bool) :
    ∃ i, kernel.code[closingMarkPc repeated notice]? = some i ∧
      i.guard = none ∧ i.op.isLocal = false := by
  have hAudit : ∀ r n : Bool, (kernel.code[closingMarkPc r n]?).any
      (fun i => i.guard.isNone && !i.op.isLocal) = true := by decide +kernel
  have h := hAudit repeated notice
  cases hc : kernel.code[closingMarkPc repeated notice]? with
  | none => simp [hc] at h
  | some i =>
    simp only [hc, Option.any_some, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨i, rfl, Option.isNone_iff_eq_none.mp h.1, h.2⟩

private theorem closingMarkNext (repeated notice : Bool) {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (hPc : s.pc = closingMarkPc repeated notice)
    (he : EStep kernel Assumptions.all l g s e (some u)) : u.pc = s.pc+1 := by
  cases notice
  · obtain ⟨i,hc,_,hf⟩ := estep_event_source he
    rw [hPc] at hc
    cases repeated
    · change kernel.code[4847]? = some i at hc
      rw [Flow.code_4847] at hc
      obtain rfl := Option.some.inj hc.symm
      exact congrArg TState.pc (fires_arrive_state hf).1
    · change kernel.code[6532]? = some i at hc
      rw [Flow.code_6532] at hc
      obtain rfl := Option.some.inj hc.symm
      exact congrArg TState.pc (fires_arrive_state hf).1
  · have hAudit : ∀ r : Bool, (kernel.code[closingMarkPc r true]?).any
        (fun i => barOp i.op) = true := by decide +kernel
    have h := hAudit repeated
    cases hc : kernel.code[closingMarkPc repeated true]? with
    | none => simp [hc] at h
    | some i => exact followsMarkedBarrier hPc hc (by simpa only [hc, Option.any_some] using h) he

private theorem debtAdvance (repeated notice : Bool) (pc : Nat) :
    (decide (pc = closingMarkPc repeated notice)).toNat + biasDebt repeated notice (pc+1) =
      (decide (pc = biasMarkPc repeated)).toNat + biasDebt repeated notice pc := by
  have hSpan : biasMarkPc repeated < closingMarkPc repeated notice := by
    cases repeated <;> cases notice <;> decide
  by_cases hStart : pc = biasMarkPc repeated <;>
    by_cases hEnd : pc = closingMarkPc repeated notice <;>
    simp [hStart,hEnd,biasDebt,hSpan.ne,hSpan.ne']
  all_goals try split_ifs
  all_goals omega

private theorem noLocalAtMark {l : Launch} {g : Nat} {s u : TState} {site : Nat}
    (hc : ∃ i, kernel.code[site]? = some i ∧ i.guard = none ∧ i.op.isLocal = false)
    (hTau : Tau kernel Assumptions.all l g s u) : s.pc ≠ site := by
  intro hPc
  obtain ⟨i,hi,hn,hn'⟩ := hc
  obtain ⟨j,hj,_,hStep⟩ := tauScoreSource hTau
  rw [hPc,hi] at hj
  obtain rfl := Option.some.inj hj
  rcases hStep with ⟨_,hGuard⟩ | ⟨_,hLocal,_⟩
  · rw [hn] at hGuard
    cases hGuard
  · rw [hn'] at hLocal
    cases hLocal

private theorem checkBarOrdinary : kernel.code.all
    (fun ins => ins.op.isLocal || Epilogue.ordinaryEvent ins.op) = true := by decide +kernel

private theorem ordinaryReturning {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (he : EStep kernel Assumptions.all l g s e (some u)) : u.pc = s.pc ∨ u.pc = s.pc+1 := by
  obtain ⟨ins,hCode,hLocal,hFire⟩ := estep_event_source he
  have hOp := List.all_eq_true.mp checkBarOrdinary _ (List.mem_of_getElem? hCode)
  exact callbackFrame_fires (Epilogue.ordinaryEventFrame
    (by simpa only [hLocal,Bool.false_or] using hOp)) hFire

private theorem biasCountStep (repeated notice : Bool) {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (hStep : WStep kernel Assumptions.all l g s ev u) :
    ev.toList.countP (barrierMark (closingMarkPc repeated notice)) + biasDebt repeated notice u.pc =
      ev.toList.countP (barrierMark (biasMarkPc repeated)) + biasDebt repeated notice s.pc := by
  have hBegin : ∃ i, kernel.code[biasMarkPc repeated]? = some i ∧
      i.guard = none ∧ i.op.isLocal = false := by
    obtain ⟨i,hc,hn,hOp⟩ := barrierCode repeated
    refine ⟨i,hc,hn,?_⟩
    cases h : i.op <;> simp only [h,barOp,Bool.false_eq_true] at hOp
    all_goals rfl
  have hAdvance := debtAdvance repeated notice s.pc
  rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hE⟩
  · have hN := noLocalAtMark hBegin hTau
    have hE := noLocalAtMark (closingCode repeated notice) hTau
    have same (hu : u.pc = s.pc+1) :
        biasDebt repeated notice u.pc = biasDebt repeated notice s.pc := by
      simpa [hu,hN,hE] using hAdvance
    simp only [Option.toList_none,List.countP_nil,Nat.zero_add]
    obtain ⟨i,hCode,_,hExec⟩ := tauScoreSource hTau
    rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hExec⟩
    · exact same rfl
    · rcases scoreExecLocal hExec with hFrame | ⟨seg,hSite,hMatch,hRun⟩
      · have hPc := hFrame.pc
        have hKeep := debtBranch repeated notice hCode
        cases hOp : i.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
        case bra dst uni =>
          rw [hPc]
          exact (by simpa only [hOp,keepsBiasDebt,decide_eq_true_eq] using hKeep :
            biasDebt repeated notice s.pc = biasDebt repeated notice dst).symm
        case brx => simp [hOp,keepsBiasDebt] at hKeep
        all_goals exact same hPc
      · rw [(scoreSegmentFrame hRun).1]
        exact (debtSegment repeated notice hSite hMatch).symm
  · have hPc := estep_source_pc hE
    have finish (hNext : u.pc = s.pc+1) :
        (some e : Option Event).toList.countP (barrierMark (closingMarkPc repeated notice)) +
            biasDebt repeated notice u.pc =
          (some e : Option Event).toList.countP (barrierMark (biasMarkPc repeated)) +
            biasDebt repeated notice s.pc := by
      have hDec (a b : Nat) : (decide (a=b)).toNat = (if a=b then 1 else 0) := by
        by_cases h : a=b <;> simp [h]
      rw [hDec,hDec] at hAdvance
      simpa only [Option.toList_some,List.countP_cons,List.countP_nil,Nat.zero_add,
        barrierMark,hPc,beq_iff_eq,hNext] using hAdvance
    by_cases hB : s.pc = biasMarkPc repeated
    · obtain ⟨i,hi,_,hOp⟩ := barrierCode repeated
      exact finish (followsMarkedBarrier hB hi hOp hE)
    by_cases hC : s.pc = closingMarkPc repeated notice
    · exact finish (closingMarkNext repeated notice hC hE)
    rcases ordinaryReturning hE with hSame | hNext
    · simp [barrierMark,hPc,hB,hC,hSame]
    · exact finish hNext

private theorem biasCountPath (repeated notice : Bool) {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} (h : TraceReach kernel Assumptions.all l g s es u) :
    es.countP (barrierMark (closingMarkPc repeated notice)) + biasDebt repeated notice u.pc =
      es.countP (barrierMark (biasMarkPc repeated)) + biasDebt repeated notice s.pc := by
  induction h with
  | refl => simp
  | tau ht _ ih =>
    have hStep := biasCountStep repeated notice (.inl ⟨rfl,ht⟩)
    simp only [Option.toList_none,List.countP_nil,Nat.zero_add] at hStep
    rw [← hStep]
    exact ih
  | event he _ ih =>
    have hStep := biasCountStep repeated notice (.inr ⟨_,rfl,he⟩)
    simp only [Option.toList_some,List.countP_cons,List.countP_nil] at hStep
    simp only [List.countP_cons]
    omega

/-- Through any thread prefix, the opening and repeated bias rendezvous each precede
one matching statistics arrival. The debt is outstanding strictly between the two. -/
theorem biasStatisticsCountAtEvent {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos : Nat} {e : Event}
    (he : X.get (g,pos) = some e) (repeated : Bool) :
    let first := if repeated then 5271 else 3583
    let last := if repeated then 5683 else 4397
    let trace := (X.tr g).take pos
    trace.countP (barrierMark last) + (if first < e.pc ∧ e.pc ≤ last then 1 else 0) =
      trace.countP (barrierMark first) := by
  obtain ⟨_, hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t, _, hTrace, hStep⟩ := hr.before_event he
  have hCount := biasCountPath repeated true hTrace
  rw [← estep_source_pc hStep] at hCount
  cases repeated <;> simpa [biasDebt,biasMarkPc,closingMarkPc] using hCount

/-- An exiting softmax lane has accounted for each bias rendezvous in both its paired
statistics arrival and its early probability publication. -/
theorem biasRendezvousCountsAtExit {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos pc : Nat}
    (he : X.get (g,pos) = some ⟨pc, .exit⟩) (repeated : Bool) :
    let first := if repeated then 5271 else 3583
    let stats := if repeated then 5683 else 4397
    let credit := if repeated then 6532 else 4847
    (X.tr g).countP (barrierMark first) = (X.tr g).countP (barrierMark stats) ∧
      (X.tr g).countP (barrierMark first) = (X.tr g).countP (barrierMark credit) := by
  have hPc := actualExitPc hX he
  subst pc
  obtain ⟨_, hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t, _, hTrace, hStep⟩ := hr.before_event he
  have hSource : t.pc = 9205 := (estep_source_pc hStep).symm
  have hs := biasCountPath repeated true hTrace
  have hc := biasCountPath repeated false hTrace
  rw [hSource] at hs hc
  have hLast := Execution.exit_last hX (event_thread_lt hX he) he
  have hCounts {site : Nat} (hSite : site ≠ 9205) :
      (X.tr g).countP (barrierMark site) = ((X.tr g).take pos).countP (barrierMark site) := by
    conv_lhs => rw [← List.take_length (l := X.tr g), ← hLast, List.take_add_one,
      (show (X.tr g)[pos]? = _ from he), Option.toList_some, List.countP_append]
    simp [barrierMark, hSite.symm]
  cases repeated <;>
    simp [biasDebt,biasMarkPc,closingMarkPc,earlyMarkPc,hCounts] at hs hc ⊢ <;>
    exact ⟨hs.symm, hc.symm⟩

/-- The fallthrough and its successor are forward-only barriers for the role. -/
def threshold (loop : ScoreLoop) (strict : Bool) : Nat :=
  (scoreLoopSite loop).increment + 4 + strict.toNat

private def softmaxFloorOp (loop : ScoreLoop) (strict : Bool) (op : Op) : Bool :=
  match op with
  | .bra dst _ => decide (threshold loop strict ≤ dst)
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem lateBranch (loop : ScoreLoop) (strict : Bool) {pc : Nat} {ins : Instr}
    (hPc : threshold loop strict ≤ pc) (hCode : kernel.code[pc]? = some ins) :
    softmaxFloorOp loop strict ins.op = true := by
  have hAudit : (kernel.code.drop (threshold loop strict)).all
      (fun i => softmaxFloorOp loop strict i.op) = true := by
    cases loop <;> cases strict <;> kernel_rfl
  apply List.all_eq_true.mp hAudit _ (List.mem_of_getElem? (i := pc-threshold loop strict) ?_)
  rw [List.getElem?_drop,Nat.add_sub_of_le hPc]
  exact hCode

set_option maxRecDepth 100000 in
private theorem lateSegments (loop : ScoreLoop) (strict : Bool) {pc : Nat} {seg : SegMatch CuteSlot}
    (hLo : threshold loop strict ≤ pc)
    (hSite : pc ∈ Assumptions.swExp2Sites) (hM : cuteExp2.matchAt kernel pc = some seg) :
    threshold loop strict ≤ seg.stop := by
  have hAudit : Assumptions.swExp2Sites.all (fun q =>
      !decide (threshold loop strict ≤ q) ||
        (cuteExp2.matchAt kernel q).any (fun r => decide (threshold loop strict ≤ r.stop)))
      = true := by cases loop <;> cases strict <;> kernel_rfl
  have h := List.all_eq_true.mp hAudit pc hSite
  simpa only [hM,hLo,decide_true,Option.any_some,Bool.not_true,Bool.false_or,
    decide_eq_true_eq] using h

private theorem plainStaysLate (loop : ScoreLoop) (strict : Bool) {l : Launch} {g : Nat} {s u :
  TState}
    {ev : Option Event} (hPc : threshold loop strict ≤ s.pc)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    threshold loop strict ≤ u.pc := by
  rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hE⟩
  · obtain ⟨ins,hc,_,hExec⟩ := tauScoreSource hTau
    rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hTerm⟩
    · exact hPc.trans (Nat.le_succ _)
    rcases scoreExecLocal hTerm with hFrame | ⟨seg,hs,hm,hRun⟩
    · have hKeep := lateBranch loop strict hPc hc
      have hNext := hFrame.pc
      cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hNext
      case bra dst uni =>
        rw [hNext]
        simpa only [hOp,softmaxFloorOp,decide_eq_true_eq] using hKeep
      case brx => simp [hOp,softmaxFloorOp] at hKeep
      all_goals exact hNext.symm ▸ hPc.trans (Nat.le_succ _)
    · rw [(scoreSegmentFrame hRun).1]
      exact lateSegments loop strict hPc hs hm
  · rcases ordinaryReturning hE with h | h
    · rwa [h]
    · rw [h]; exact hPc.trans (Nat.le_succ _)

theorem scorePathStaysAfterLoop (loop : ScoreLoop) (strict : Bool) {l : Launch} {g : Nat} {s u :
  TState}
    {es : List Event} (h : TraceReach kernel Assumptions.all l g s es u)
    (hs : threshold loop strict ≤ s.pc) :
    threshold loop strict ≤ u.pc := by
  induction h with
  | refl => exact hs
  | tau ht _ ih => exact ih (plainStaysLate loop strict hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (plainStaysLate loop strict hs (.inr ⟨_,rfl,he⟩))

private theorem pathStaysLate (terminal : Bool) {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} (h : TraceReach kernel Assumptions.all l g s es u)
    (hs : (if terminal then 7605 else 6654) ≤ s.pc) :
    (if terminal then 7605 else 6654) ≤ u.pc := by
  cases terminal
  · exact scorePathStaysAfterLoop .biased false h hs
  · exact scorePathStaysAfterLoop .plain false h hs

private theorem afterExitStep (loop : ScoreLoop) {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (hPc : s.pc = threshold loop false)
    (h : WStep kernel Assumptions.all l g s ev u) : threshold loop true ≤ u.pc := by
  have hCode : ∃ i, kernel.code[s.pc]? = some i ∧ i.op.isLocal = true ∧
      (∀ pc, ¬ BrxTarget i.op pc) ∧ nextPc i.op s.pc = s.pc+1 := by
    rw [hPc]
    cases loop
    · exact ⟨_,Flow.code_6654,rfl,fun _ => nofun,rfl⟩
    · exact ⟨_,Flow.code_7605,rfl,fun _ => nofun,rfl⟩
  obtain ⟨i,hCode,hLocal,hNo,hNext⟩ := hCode
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; cases loop <;> decide
  have hu : u.pc = s.pc+1 := by
    rcases h with ⟨rfl,hTau⟩ | ⟨e,rfl,hE⟩
    · obtain ⟨i',hCode',_,hStep⟩ := tauScoreSource hTau
      obtain rfl := Option.some.inj (hCode'.symm.trans hCode)
      rcases hStep with ⟨rfl,_⟩ | ⟨_,_,hx⟩
      · rfl
      · rcases scoreExecLocal hx with hL | ⟨_,hSite,_,_⟩
        · exact (hL.pc.resolve_right (hNo _)).trans hNext
        · exact (hOff hSite).elim
    · exact (noLocalEvent hCode hLocal hE).elim
  rw [hu,hPc]
  exact le_rfl

/-- Every actual path from a loop head to its fallthrough or a continuing head
has preserved the same resident lane, scale and score-loop geometry registers. -/
theorem scoreTraceKeepsResidents (loop : ScoreLoop) {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} (hPath : TraceReach kernel Assumptions.all l g s es u)
    (hLo : (scoreLoopSite loop).head ≤ s.pc) (hEnd : u.pc ≤ threshold loop false)
    (hSub : s.sub ≤ 3) : ∀ r ∈ loopResident loop, u.regs r = s.regs r := by
  have hBefore : s.pc ≤ threshold loop false := by
    by_contra! h
    have hThreshold : threshold loop true ≤ s.pc := by
      simp only [threshold,Bool.toNat_false,Bool.toNat_true,Nat.add_zero] at h ⊢
      omega
    have hLate := scorePathStaysAfterLoop loop true hPath hThreshold
    simp only [threshold,Bool.toNat_false,Bool.toNat_true,Nat.add_zero] at hLate hEnd
    omega
  induction hPath with
  | refl => exact fun _ _ => rfl
  | @tau s t u es hStep hTail ih =>
    have hW : WStep kernel Assumptions.all l g s none t := .inl ⟨rfl,hStep⟩
    rcases hBefore.lt_or_eq with hb | hb
    · obtain ⟨hL,hH,hS,_,hR⟩ := scoreLoopStepWithResidents loop hLo
        (by simpa only [threshold,Bool.toNat_false,Nat.add_zero] using hb) hSub hW
      exact fun r hr => (ih hL hEnd hS hH r hr).trans (hR r hr)
    · have hLate := scorePathStaysAfterLoop loop true hTail (afterExitStep loop hb hW)
      simp only [threshold,Bool.toNat_false,Bool.toNat_true,Nat.add_zero] at hLate hEnd
      omega
  | @event s t u es e hStep hTail ih =>
    have hW : WStep kernel Assumptions.all l g s (some e) t := .inr ⟨e,rfl,hStep⟩
    rcases hBefore.lt_or_eq with hb | hb
    · obtain ⟨hL,hH,hS,_,hR⟩ := scoreLoopStepWithResidents loop hLo
        (by simpa only [threshold,Bool.toNat_false,Nat.add_zero] using hb) hSub hW
      exact fun r hr => (ih hL hEnd hS hH r hr).trans (hR r hr)
    · have hLate := scorePathStaysAfterLoop loop true hTail (afterExitStep loop hb hW)
      simp only [threshold,Bool.toNat_false,Bool.toNat_true,Nat.add_zero] at hLate hEnd
      omega

private theorem noPlainBeforeBiased {l : Launch} {g : Nat} {s u : TState}
    {events : List Event} (hr : TraceReach kernel Assumptions.all l g s events u)
    (hu : u.pc < 6654) : events.countP (barrierMark 7437) = 0 := by
  apply List.countP_eq_zero.mpr
  intro e he
  have noLate (hf : 6654 ≤ e.pc) : False := by
    induction hr with
    | refl => cases he
    | tau _ _ ih => exact ih hu he
    | event hE hTail ih =>
      rcases List.mem_cons.mp he with he' | hRest
      · subst e
        have hPc := estep_source_pc hE
        exact (Nat.not_le_of_lt hu) (pathStaysLate false hTail
          (plainStaysLate .biased false (hPc ▸ hf) (.inr ⟨_,rfl,hE⟩)))
      · exact ih hu hRest
  intro h
  have hPc : e.pc = 7437 := beq_iff_eq.mp h
  exact noLate (by omega)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem biasBarrierMarkEq (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g i : Nat} (hStage : warpIndex l g/4 = stage.val) {e : Event}
    (he : X.get (g,i) = some e) (hi : i+1 < (X.tr g).length) :
    Execution.isBarId (11+stage.val) e = (barrierMark 3583 e || barrierMark 5271 e) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨pc,kind⟩ := e
    cases kind <;> simp only [Execution.isBarId,Bool.false_eq_true] at h
    case bar id count mode =>
      obtain rfl := beq_iff_eq.mp h
      have hf := actualNamedBarrierCountById hp hX he
      have hCount : count = some 128 := by fin_cases stage <;> exact hf
      obtain ⟨hSite,hCnt,_,_,_⟩ := actualNamedBarrier hp hX he
      rcases biasCountSite hSite (hCnt.symm.trans hCount) with h | h <;> simp [barrierMark,h]
  · intro h
    have hAt : e.pc = 3583 ∨ e.pc = 5271 := by
      simpa only [barrierMark,Bool.or_eq_true,beq_iff_eq] using h
    let repeated := decide (e.pc = 5271)
    have hPc : e.pc = biasMarkPc repeated := by
      rcases hAt with h | h <;> simp [h,repeated,biasMarkPc]
    obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
    obtain ⟨t,u,hE,_⟩ := hr.after_event he hi
    obtain ⟨ins,hCode,_,hOp⟩ := barrierCode repeated
    have hSource : t.pc = biasMarkPc repeated := (estep_source_pc hE).symm.trans hPc
    obtain ⟨_,id,n,mode,hKind⟩ := markedBarrierContinues hSource hCode hOp hE
    have he' : X.get (g,i) = some ⟨if repeated then 5271 else 3583,.bar id n mode⟩ := by
      have heq : e = ⟨if repeated then 5271 else 3583,.bar id n mode⟩ := by
        cases e; exact congrArg₂ Event.mk hPc hKind
      simpa only [heq] using he
    have hId := (actualBiasBarrierStage hp hX repeated he').2
    simp [Execution.isBarId,hKind,hId,hStage]

theorem earlyProbabilityMarkCount (xs : List Event) :
    xs.countP earlyProbabilityMark = xs.countP (barrierMark 4847) +
      xs.countP (barrierMark 6532) + xs.countP (barrierMark 7437) := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    simp only [List.countP_cons,ih,earlyProbabilityMark,List.contains_cons,List.contains_nil,
      Bool.or_false,barrierMark]
    by_cases a : e.pc = 4847 <;> by_cases b : e.pc = 6532 <;> by_cases c : e.pc = 7437
    all_goals simp_all
    all_goals omega

/-- While packing the biased scores, every prior Bias rendezvous has completed exactly
one early probability publication in the same softmax lane. -/
theorem biasedScoreWindowEqualsProbabilityOrdinal (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {ev : Event} (stage : Fin 2)
    (hw : warpIndex l g < 8) (hStage : warpIndex l g/4 = stage.val) (he : X.get (g,j) = some ev)
    (start : 5112 ≤ ev.pc) (stop : ev.pc ≤ 5181) :
    observedBarrierOrdinal X (g,j) (11+stage.val) =
      probabilityOrdinal l X (g/l.block) stage 0 (g,j) := by
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t,_,hTrace,hE⟩ := hr.before_event he
  let before := (X.tr g).take j
  have ht : t.pc = ev.pc := (estep_source_pc hE).symm
  have hFirst := biasCountPath false false hTrace
  have hRepeat := biasCountPath true false hTrace
  change before.countP (barrierMark 4847)+biasDebt false false t.pc =
    before.countP (barrierMark 3583)+biasDebt false false 0 at hFirst
  change before.countP (barrierMark 6532)+biasDebt true false t.pc =
    before.countP (barrierMark 5271)+biasDebt true false 0 at hRepeat
  have hZero := noPlainBeforeBiased hTrace (by omega)
  have hMark : before.countP (Execution.isBarId (11+stage.val)) =
      before.countP (fun e => barrierMark 3583 e || barrierMark 5271 e) := by
    apply List.countP_congr
    intro e hMem
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hMem
    have hLt := (List.getElem?_eq_some_iff.mp hi).1
    simp only [before,List.length_take] at hLt
    have hBefore : i < j := by omega
    rw [List.getElem?_take_of_lt hBefore] at hi
    change X.get (g,i) = some e at hi
    have hJ : j < (X.tr g).length := len_of_get he
    exact (Bool.eq_iff_iff.mp (biasBarrierMarkEq hp hX stage hStage hi (by omega)))
  have hBar := countP_or_disj (p := barrierMark 3583) (q := barrierMark 5271)
    (l := before) (fun e _ h => (by
      have a : e.pc = 3583 := beq_iff_eq.mp h.1
      have b : e.pc = 5271 := beq_iff_eq.mp h.2
      omega))
  have hEarly := earlyProbabilityCount hp hX stage hw hStage (len_of_get he)
  change before.countP _ = probabilityOrdinal l X (g/l.block) stage 0 (g,j)
  simp [biasDebt,biasMarkPc,closingMarkPc,earlyMarkPc,show ¬ t.pc ≤ 4847 by omega,
    show ¬ 5271 < t.pc by omega] at hFirst hRepeat
  change before.countP (barrierMark 7437) = 0 at hZero
  rw [← hEarly,earlyProbabilityMarkCount,hMark,hBar,hZero,Nat.add_zero,hFirst,hRepeat]

/-- By a real biased acquire, every prior Bias rendezvous has completed exactly
one early probability publication in the same softmax lane. -/
theorem biasedVisitEqualsProbabilityOrdinal (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j phase : Nat} {obj : Loc} {acq : Bool}
    {scope : MbarScope} (stage : Fin 2) (hw : warpIndex l g < 8)
    (hStage : warpIndex l g/4 = stage.val)
    (he : X.get (g,j) = some ⟨5181,.wait obj phase true acq scope⟩) :
    observedBarrierOrdinal X (g,j) (11+stage.val) =
      probabilityOrdinal l X (g/l.block) stage 0 (g,j) :=
  biasedScoreWindowEqualsProbabilityOrdinal hp hX stage hw hStage he
    (by decide : 5112 ≤ 5181) (Nat.le_refl 5181)

private def beforeFirstEarlyCredit (pc : Nat) (op : Op) : Bool :=
  match op with
  | .bra dst _ => decide (pc ≤ 4847 → dst < 7605 → dst ≤ 4847)
  | .brx .. => false
  | _ => true

private theorem firstCreditBranch {pc : Nat} {ins : Instr} (hc : kernel.code[pc]? = some ins) :
    beforeFirstEarlyCredit pc ins.op = true := by
  have hAudit : (kernel.code.zipIdx 0).all
      (fun (i,pc) => beforeFirstEarlyCredit pc i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  exact List.all_eq_true.mp hAudit (ins,pc) (List.mem_zipIdx_iff_getElem?.mpr hc)

private theorem firstCreditSegment {pc : Nat} {seg : SegMatch CuteSlot}
    (hPc : pc ≤ 4847) (hSite : pc ∈ Assumptions.swExp2Sites)
    (hM : cuteExp2.matchAt kernel pc = some seg) : seg.stop ≤ 4847 := by
  have hAudit : Assumptions.swExp2Sites.all (fun q =>
      !decide (q ≤ 4847) || (cuteExp2.matchAt kernel q).any (fun r => decide (r.stop ≤ 4847)))
      = true := by set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAudit pc hSite
  simpa only [hPc,hM,decide_true,Bool.not_true,Bool.false_or,Option.any_some,
    decide_eq_true_eq] using h

private theorem beforeFirstEarlyCreditStep {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (hPc : s.pc ≤ 4847) (hEnd : u.pc < 7605)
    (hSilent : ∀ e, ev = some e → e.pc ≠ 4847)
    (h : WStep kernel Assumptions.all l g s ev u) : u.pc ≤ 4847 := by
  rcases h with ⟨rfl,hTau⟩ | ⟨e,rfl,hE⟩
  · have hNot := noLocalAtMark (closingCode false false) hTau
    change s.pc ≠ 4847 at hNot
    obtain ⟨ins,hc,_,hLocal⟩ := tauScoreSource hTau
    rcases hLocal with ⟨rfl,_⟩ | ⟨_,_,hx⟩
    · change s.pc+1 ≤ 4847
      omega
    rcases scoreExecLocal hx with hFrame | ⟨seg,hSite,hM,hRun⟩
    · have hAudit := firstCreditBranch hc
      have hu := hFrame.pc
      cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hu
      case bra dst uni =>
        have hb : s.pc ≤ 4847 → dst < 7605 → dst ≤ 4847 := by
          simpa only [hOp,beforeFirstEarlyCredit,decide_eq_true_eq] using hAudit
        rw [hu]
        exact hb hPc (hu ▸ hEnd)
      case brx => simp [hOp,beforeFirstEarlyCredit] at hAudit
      all_goals omega
    · rw [(scoreSegmentFrame hRun).1]
      exact firstCreditSegment hPc hSite hM
  · have hNot := hSilent e rfl
    rw [estep_source_pc hE] at hNot
    rcases ordinaryReturning hE with h | h <;> omega

private theorem quietFirstEarlyCreditPath {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} (h : TraceReach kernel Assumptions.all l g s es u)
    (hs : s.pc ≤ 4847) (hu : u.pc < 7605) (hNo : ∀ e ∈ es, e.pc ≠ 4847) :
    u.pc ≤ 4847 := by
  induction h with
  | refl => exact hs
  | @tau a b c events ht hRest ih =>
    have hQuiet : b.pc < 7605 := by
      by_contra! hBad
      exact (Nat.not_le_of_lt hu) (pathStaysLate true hRest hBad)
    exact ih (beforeFirstEarlyCreditStep hs hQuiet (by simp) (.inl ⟨rfl,ht⟩)) hu hNo
  | @event a b c events e he hRest ih =>
    have hQuiet : b.pc < 7605 := by
      by_contra! hBad
      exact (Nat.not_le_of_lt hu) (pathStaysLate true hRest hBad)
    have hHead := beforeFirstEarlyCreditStep hs hQuiet (fun e hEq =>
      hNo _ (Option.some.inj hEq ▸ List.mem_cons_self ..)) (.inr ⟨_,rfl,he⟩)
    exact ih hHead hu (fun e hMem => hNo e (List.mem_cons_of_mem _ hMem))

/-- The repeated numerical body is entered only after the opening P credit. -/
theorem firstCreditBeforeRepeatedEvent {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {event : Event}
    (he : X.get (g,j) = some event) (hLo : 4847 < event.pc) (hHi : event.pc < 7605) :
    0 < ((X.tr g).take j).countP (barrierMark 4847) := by
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t,_,hTrace,hE⟩ := hr.before_event he
  have hPc : t.pc = event.pc := (estep_source_pc hE).symm
  apply Nat.pos_of_ne_zero
  intro hZero
  have hAudit : ∀ e ∈ (X.tr g).take j, e.pc ≠ 4847 := by
    intro e he' hSite
    have hMark := List.countP_eq_zero.mp hZero e he'
    simp [barrierMark,hSite] at hMark
  exact (Nat.not_le_of_lt (hPc.symm ▸ hLo))
    (quietFirstEarlyCreditPath hTrace (by decide) (hPc.symm ▸ hHi) hAudit)

/-- Both repeated score-load sites follow the first probability publication. -/
theorem firstCreditBeforeRepeatedScore {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g j address : Nat} {words : List Value} {shape : TcShape}
    (r : Round) (hRepeat : r ≠ .first) (q : Fin 4)
    (he : X.get (g,j) = some ⟨scorePc r q,.tc (.ld address words shape)⟩) :
    0 < ((X.tr g).take j).countP (barrierMark 4847) := by
  have hRange : 4847 < scorePc r q ∧ scorePc r q < 7605 := by
    cases r
    · exact (hRepeat rfl).elim
    · fin_cases q <;> decide
    · fin_cases q <;> decide
  exact firstCreditBeforeRepeatedEvent hX he hRange.1 hRange.2

/-- Every repeated numerical event follows a named Bias rendezvous for its stage. -/
theorem firstBiasBarrierBeforeRepeatedEvent (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {event : Event} (stage : Fin 2)
    (hStage : warpIndex l g/4 = stage.val) (he : X.get (g,j) = some event) (hLo : 4847 < event.pc)
    (hHi : event.pc < 7605) :
    0 < observedBarrierOrdinal X (g,j) (11+stage.val) := by
  have hCredit := firstCreditBeforeRepeatedEvent hX he hLo hHi
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t,_,hTrace,hE⟩ := hr.before_event he
  have hCount := biasCountPath false false hTrace
  have hFirst : 0 < ((X.tr g).take j).countP (barrierMark 3583) := by
    change ((X.tr g).take j).countP (barrierMark 4847)+biasDebt false false t.pc =
      ((X.tr g).take j).countP (barrierMark 3583)+0 at hCount
    omega
  have hMark : ((X.tr g).take j).countP (Execution.isBarId (11+stage.val)) =
      ((X.tr g).take j).countP (fun e => barrierMark 3583 e || barrierMark 5271 e) := by
    apply List.countP_congr
    intro e hMem
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hMem
    have hLt := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_take] at hLt
    have hBefore : i < j := by omega
    rw [List.getElem?_take_of_lt hBefore] at hi
    change X.get (g,i) = some e at hi
    have hJ : j < (X.tr g).length := len_of_get he
    exact (Bool.eq_iff_iff.mp (biasBarrierMarkEq hp hX stage hStage hi (by omega)))
  rw [observedBarrierOrdinal,hMark]
  apply Nat.pos_of_ne_zero
  intro hZero
  have hBad : ((X.tr g).take j).countP (barrierMark 3583) = 0 := by
    apply List.countP_eq_zero.mpr
    intro e hMem
    have hFalse := List.countP_eq_zero.mp hZero e hMem
    cases h : barrierMark 3583 e <;> simp_all
  omega

/-- A repeated score load has a nonzero probability generation. -/
theorem repeatedScoreHasEarlierVisit (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j address : Nat} {words : List Value} {shape : TcShape} (stage : Fin 2)
    (hw : warpIndex l g < 8) (hStage : warpIndex l g/4 = stage.val) (r : Round)
    (hRepeat : r ≠ .first) (q : Fin 4)
    (he : X.get (g,j) = some ⟨scorePc r q,.tc (.ld address words shape)⟩) :
    0 < probabilityOrdinal l X (g/l.block) stage 0 (g,j) := by
  rw [← earlyProbabilityCount hp hX stage hw hStage (len_of_get he),
    earlyProbabilityMarkCount]
  have h := firstCreditBeforeRepeatedScore hX r hRepeat q he
  dsimp only
  omega

/-- Every recorded biased score load follows the first probability publication. -/
theorem biasedScoreHasEarlierVisit (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j address : Nat} {words : List Value} {shape : TcShape} (stage : Fin 2)
    (hw : warpIndex l g < 8) (hStage : warpIndex l g/4 = stage.val) (q : Fin 4)
    (he : X.get (g,j) = some ⟨scorePc .biased q,.tc (.ld address words shape)⟩) :
    0 < probabilityOrdinal l X (g/l.block) stage 0 (g,j) :=
  repeatedScoreHasEarlierVisit hp hX stage hw hStage .biased (by decide) q he

end PTX.Kernels.TmlFa4Fwd.Softmax
