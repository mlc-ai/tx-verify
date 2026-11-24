-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Correction
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarriers
public import Lemmas.Protocol.NamedBarArrive
public import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
public import Lemmas.Flow.ContinuingEvent
import Lemmas.Flow.EventCont
import Lemmas.Protocol.CountNth
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.CorrectionStats

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption Softmax

private def creditSites (stage : Fin 2) : List Nat :=
  if stage.val = 0 then [7987, 8443, 8468] else [8224, 8464, 8764]

private def isWait (stage : Fin 2) (pc : Nat) : Bool := (correctionStatsSites stage).contains pc

private def probabilitySites (stage : Fin 2) : List Nat :=
  if stage.val = 0 then [7752, 8223, 8759] else [7754, 8442, 9055]

private def isCredit (stage : Fin 2) (pc : Nat) (probability := false) : Bool :=
  (if probability then probabilitySites stage else creditSites stage).contains pc

private def statsOutstanding (stage : Fin 2) (pc : Nat) : Bool :=
  if stage.val = 0 then
    decide (7986 ≤ pc ∧ pc ≤ 7987 ∨ 8007 ≤ pc ∧ pc ≤ 8443 ∨ 8466 ≤ pc ∧ pc ≤ 8468)
  else
    decide (7989 ≤ pc ∧ pc ≤ 8224 ∨ 8226 ≤ pc ∧ pc ≤ 8464 ∨ 8762 ≤ pc ∧ pc ≤ 8764)

private def outstanding (stage : Fin 2) (pc : Nat) (probability : Bool) : Nat :=
  if probability then
    if 9201 ≤ pc then 0
    else if stage.val = 0 then
      if 7753 ≤ pc ∧ pc ≤ 7985 then 0
      else if 8007 ≤ pc ∧ pc ≤ 8223 ∨ 8466 ≤ pc ∧ pc ≤ 8759 then 2
      else 1
    else
      if 7755 ≤ pc ∧ pc ≤ 7988 then 0
      else if 8226 ≤ pc ∧ pc ≤ 8442 ∨ 8762 ≤ pc ∧ pc ≤ 9055 then 2
      else 1
  else (statsOutstanding stage pc).toNat

/-- The statistics slot returns every credit. Leaving the probability loop may discard capacity. -/
private def balance (probability : Bool) (a b : Nat) : Prop :=
  if probability then a ≤ b else a = b

private theorem sequentialBalance (stage : Fin 2) (probability : Bool) (pc : Nat) :
    balance probability
      (outstanding stage (pc+1) probability + (isCredit stage pc probability).toNat)
      (outstanding stage pc probability + (isWait stage pc).toNat) := by
  have asIf (b : Bool) : b.toNat = if b then 1 else 0 := by cases b <;> rfl
  cases probability <;> fin_cases stage <;>
    simp [balance, outstanding, statsOutstanding, isCredit, isWait, creditSites, probabilitySites,
      correctionStatsSites, asIf] <;> split_ifs <;> omega

private instance (probability : Bool) (a b : Nat) : Decidable (balance probability a b) := by
  cases probability <;> unfold balance <;> infer_instance

private def arrivalOp : Op → Bool
  | .mbarArrive .. => true
  | _ => false

private def creditControl (stage : Fin 2) (probability : Bool) (pc : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || Epilogue.ordinaryEvent i.op) &&
  (!isWait stage pc || i.guard.isNone && barOp i.op) &&
  (!isCredit stage pc probability || i.guard.isNone && arrivalOp i.op) &&
  (match i.op with
    | .bra dst _ => decide (balance probability (outstanding stage dst probability)
      (outstanding stage pc probability))
    | .brx .. => false
    | _ => true)

private def checkedCreditControl (stage : Fin 2) (probability : Bool) : Bool :=
  kernel.code.zipIdx.all (fun (i, pc) => creditControl stage probability pc i)

set_option maxRecDepth 100000 in
private theorem creditControlStageZero : checkedCreditControl 0 false = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem creditControlStageOne : checkedCreditControl 1 false = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem probabilityControlStageZero : checkedCreditControl 0 true = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem probabilityControlStageOne : checkedCreditControl 1 true = true := by kernel_rfl

private theorem creditControlAt (stage : Fin 2) (probability : Bool) {pc : Nat} {ins : Instr}
    (hc : kernel.code[pc]? = some ins) : creditControl stage probability pc ins = true := by
  have hAudit : checkedCreditControl stage probability = true := by
    cases probability <;> fin_cases stage
    · exact creditControlStageZero
    · exact creditControlStageOne
    · exact probabilityControlStageZero
    · exact probabilityControlStageOne
  exact List.all_eq_true.mp hAudit _ (List.mk_mem_zipIdx_iff_getElem?.mpr hc)

private theorem segmentKeepsOutstanding (stage : Fin 2) (probability : Bool)
    {pc : Nat} {segment : SegMatch CuteSlot}
    (hs : pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel pc = some segment) :
    balance probability (outstanding stage segment.stop probability)
      (outstanding stage pc probability) := by
  have hAudit : Assumptions.swExp2Sites.all (fun p =>
      match cuteExp2.matchAt kernel p with
        | some m => decide (balance probability (outstanding stage m.stop probability)
            (outstanding stage p probability))
        | none => false) = true := by
    cases probability <;> fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  have hPc := List.all_eq_true.mp hAudit pc hs
  rw [hm] at hPc
  exact of_decide_eq_true hPc

private theorem markersNonlocal (stage : Fin 2) (probability : Bool) {pc : Nat} {i : Instr}
    (hc : kernel.code[pc]? = some i)
    (hMark : isWait stage pc = true ∨ isCredit stage pc probability = true) :
    i.guard = none ∧ i.op.isLocal = false := by
  have hControl := creditControlAt stage probability hc
  simp only [creditControl, Bool.and_eq_true] at hControl
  rcases hMark with h | h
  · obtain ⟨hg, ho⟩ : i.guard.isNone = true ∧ barOp i.op = true := by
      simpa only [h, Bool.not_true, Bool.false_or, Bool.and_eq_true] using hControl.1.1.2
    refine ⟨Option.isNone_iff_eq_none.mp hg, ?_⟩
    cases hOp : i.op <;> simp only [hOp, barOp, Bool.false_eq_true] at ho
    all_goals rfl
  · obtain ⟨hg, ho⟩ : i.guard.isNone = true ∧ arrivalOp i.op = true := by
      simpa only [h, Bool.not_true, Bool.false_or, Bool.and_eq_true] using hControl.1.2
    refine ⟨Option.isNone_iff_eq_none.mp hg, ?_⟩
    cases hOp : i.op <;> simp only [hOp, arrivalOp, Bool.false_eq_true] at ho
    all_goals rfl

private theorem correctionCreditTau {l : Launch} {g : Nat} {s u : TState}
    (stage : Fin 2) (probability : Bool) (ht : Tau kernel Assumptions.all l g s u) :
    balance probability (outstanding stage u.pc probability)
      (outstanding stage s.pc probability) := by
  obtain ⟨i, hc, _, hExec⟩ := tauScoreSource ht
  have hNo : ¬(isWait stage s.pc = true ∨ isCredit stage s.pc probability = true) := by
    intro hm
    obtain ⟨hg, hi⟩ := markersNonlocal stage probability hc hm
    rcases hExec with ⟨_, hSkip⟩ | ⟨_, hl, _⟩
    · rw [hg] at hSkip
      cases hSkip
    · rw [hi] at hl
      cases hl
  simp only [not_or, Bool.not_eq_true] at hNo
  have hNext : balance probability (outstanding stage (s.pc+1) probability)
      (outstanding stage s.pc probability) := by
    have h := sequentialBalance stage probability s.pc
    simpa only [hNo.1, hNo.2, Bool.toNat_false, Nat.add_zero] using h
  rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hExec⟩
  · exact hNext
  · rcases scoreExecLocal hExec with hf | ⟨m, hSite, hm, hRun⟩
    · have hPc := hf.pc
      have hAudit := creditControlAt stage probability hc
      simp only [creditControl, Bool.and_eq_true] at hAudit
      have hCode := hAudit.2
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra dst uni =>
        rw [hPc]
        exact of_decide_eq_true (by simpa only [ho] using hCode)
      case brx => simp [ho] at hCode
      all_goals exact hPc ▸ hNext
    · rw [(scoreSegmentFrame hRun).1]
      exact segmentKeepsOutstanding stage probability hSite hm

private theorem correctionCreditEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (probability : Bool) (he : EStep kernel Assumptions.all l g s e (some u)) :
    balance probability
      (outstanding stage u.pc probability + (isCredit stage e.pc probability).toNat)
      (outstanding stage s.pc probability + (isWait stage e.pc).toNat) := by
  rw [estep_source_pc he]
  obtain ⟨i, hc, hl, hFire⟩ := estep_event_source he
  have hAudit := creditControlAt stage probability hc
  simp only [creditControl, Bool.and_eq_true] at hAudit
  by_cases hWait : isWait stage s.pc = true
  · have hOp : barOp i.op = true := by
      have h := hAudit.1.1.2
      simp only [hWait, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
      exact h.2
    rw [followsMarkedBarrier rfl hc hOp he]
    exact sequentialBalance stage probability s.pc
  by_cases hCredit : isCredit stage s.pc probability = true
  · have hOp : arrivalOp i.op = true := by
      have h := hAudit.1.2
      simp only [hCredit, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
      exact h.2
    have hPc : u.pc = s.pc+1 := by
      cases ho : i.op <;> simp only [arrivalOp, ho, Bool.false_eq_true] at hOp
      rw [ho] at hFire
      obtain ⟨rfl, _⟩ := fires_arrive_state hFire
      cases ‹Option Nat› <;> rfl
    rw [hPc]
    exact sequentialBalance stage probability s.pc
  have hFrame := Epilogue.ordinaryEventFrame
    (A := Assumptions.all) (l := l) (g := g) (s := s)
    (by simpa only [hl, Bool.false_or] using hAudit.1.1.1)
  rcases callbackFrame_fires hFrame hFire with h | h
  · rw [h, Bool.eq_false_iff.mpr hWait, Bool.eq_false_iff.mpr hCredit]
    cases probability <;> simp [balance]
  · rw [h]
    exact sequentialBalance stage probability s.pc

/-- Marker for the first, repeated, or terminal statistics wait of one correction stage. -/
@[no_expose] def correctionStatsWaitMark (stage : Fin 2) (e : Event) : Bool := isWait stage e.pc

/-- Marker for statistics-buffer credit returned by one correction stage. -/
@[no_expose] def correctionStatsCreditMark (stage : Fin 2) (e : Event) : Bool := isCredit stage e.pc

theorem correctionStatsWaitMark_iff (stage : Fin 2) (e : Event) :
    correctionStatsWaitMark stage e = true ↔ e.pc ∈ correctionStatsSites stage := by
  simp [correctionStatsWaitMark, isWait]

theorem correctionStatsCreditMark_iff (stage : Fin 2) (e : Event) :
    correctionStatsCreditMark stage e = true ↔
      e.pc ∈ (if stage.val = 0 then [7987, 8443, 8468] else [8224, 8464, 8764]) := by
  simp [correctionStatsCreditMark, isCredit, creditSites]

/-- Every returning trace prefix preserves the difference between waits and credits.
At a credit event its lane has exactly one earlier wait that has not yet returned a credit. -/
private theorem balanceWithTau {strict : Bool} {a b c n : Nat}
    (h : balance strict b a) (ih : balance strict c (b+n)) : balance strict c (a+n) := by
  cases strict <;> dsimp [balance] at * <;> omega

private theorem balanceWithEvent {strict : Bool} {a b c d n x y : Nat}
    (h : balance strict (b+c) (a+d)) (ih : balance strict (n+x) (b+y)) :
    balance strict (n+(x+c)) (a+(y+d)) := by
  cases strict <;> dsimp [balance] at * <;> omega

private theorem correctionCreditBalance {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    (stage : Fin 2) (probability : Bool) (h : TraceReach kernel Assumptions.all l g s es u) :
    balance probability
      (outstanding stage u.pc probability + es.countP (fun e => isCredit stage e.pc probability))
      (outstanding stage s.pc probability + es.countP (correctionStatsWaitMark stage)) := by
  induction h with
  | refl => cases probability <;> simp [balance]
  | tau ht _ ih => exact balanceWithTau (correctionCreditTau stage probability ht) ih
  | @event s v u es e he _ ih =>
    have asIf (b : Bool) : b.toNat = if b then 1 else 0 := by cases b <;> rfl
    rw [List.countP_cons, List.countP_cons, ← asIf, ← asIf]
    exact balanceWithEvent (correctionCreditEvent stage probability he) ih

private theorem outstandingStatisticsCredit {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {i : EvId} {e : Event} (he : X.get i = some e) (hPending : statsOutstanding stage e.pc = true) :
    ((X.tr i.1).take i.2).countP (correctionStatsWaitMark stage) =
      ((X.tr i.1).take i.2).countP (correctionStatsCreditMark stage) + 1 := by
  obtain ⟨_, hr⟩ := hX.thr i.1 (event_thread_lt hX he)
  obtain ⟨u, _, hReach, hStep⟩ := hr.before_event he
  have ho : outstanding stage u.pc false = 1 := by
    rw [← estep_source_pc hStep]
    simp [outstanding, hPending]
  have hStart : outstanding stage ({} : TState).pc false = 0 := by fin_cases stage <;> decide
  have h := correctionCreditBalance stage false hReach
  rw [ho, hStart] at h
  change 1 + ((X.tr i.1).take i.2).countP (correctionStatsCreditMark stage) = _ at h
  simpa only [Nat.zero_add] using h.symm.trans (Nat.add_comm _ _)

/-- At an actual credit site, the lane has reached one more wait than credits for this stage. -/
theorem correctionCreditRequiresWait {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {i : EvId} {e : Event} (he : X.get i = some e) (hc : correctionStatsCreditMark stage e = true) :
    ((X.tr i.1).take i.2).countP (correctionStatsWaitMark stage) =
      ((X.tr i.1).take i.2).countP (correctionStatsCreditMark stage) + 1 := by
  apply outstandingStatisticsCredit hX stage he
  have hs : e.pc ∈ creditSites stage := by simpa [correctionStatsCreditMark, isCredit] using hc
  fin_cases stage <;> simp [creditSites] at hs
  all_goals rcases hs with h | h | h <;> rw [h] <;> decide

/-- Reading statistics retains the credit of the observed generation until after the read. -/
theorem statisticsReadBeforeCredit {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) (kind : StatsKind)
    {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (he : X.get i = some ⟨statsPc stage kind, .rd a bytes⟩) :
    ((X.tr i.1).take i.2).countP (correctionStatsWaitMark stage) =
      ((X.tr i.1).take i.2).countP (correctionStatsCreditMark stage) + 1 := by
  have hPending : statsOutstanding stage (statsPc stage kind) = true := by
    cases kind <;> fin_cases stage <;> decide
  exact outstandingStatisticsCredit hX stage he hPending

/-- Source-level marker for the startup, recurring, or terminal joint probability credit. -/
@[no_expose] def correctionProbabilityMark (stage : Fin 2) (e : Event) : Bool :=
  isCredit stage e.pc true

theorem correctionProbabilityMark_iff (stage : Fin 2) (e : Event) :
    correctionProbabilityMark stage e = true ↔
      e.pc ∈ (if stage.val = 0 then [7752, 8223, 8759] else [7754, 8442, 9055]) := by
  simp [correctionProbabilityMark, isCredit, probabilitySites]

private theorem correctionProbabilityWaitBudgetAt {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {i : EvId} {e : Event} (he : X.get i = some e) (hs : outstanding stage e.pc true = 2) :
    ((X.tr i.1).take i.2).countP (correctionProbabilityMark stage) + 1 ≤
      ((X.tr i.1).take i.2).countP (correctionStatsWaitMark stage) := by
  obtain ⟨_, hr⟩ := hX.thr i.1 (event_thread_lt hX he)
  obtain ⟨u, _, hReach, hStep⟩ := hr.before_event he
  have ho : outstanding stage u.pc true = 2 := (estep_source_pc hStep) ▸ hs
  have hStart : outstanding stage ({} : TState).pc true = 1 := by fin_cases stage <;> decide
  have h := correctionCreditBalance stage true hReach
  rw [ho, hStart] at h
  change 2 + ((X.tr i.1).take i.2).countP (correctionProbabilityMark stage) ≤
    1 + ((X.tr i.1).take i.2).countP (correctionStatsWaitMark stage) at h
  omega

/-- Each recurring or terminal joint credit has a returned statistics wait of its ordinal. -/
theorem correctionProbabilityWaitBudget {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {i : EvId} {e : Event} (he : X.get i = some e)
    (hc : e.pc ∈ (if stage.val = 0 then [8223, 8759] else [8442, 9055])) :
    ((X.tr i.1).take i.2).countP (correctionProbabilityMark stage) + 1 ≤
      ((X.tr i.1).take i.2).countP (correctionStatsWaitMark stage) := by
  apply correctionProbabilityWaitBudgetAt hX stage he
  fin_cases stage <;> simp at hc
  all_goals rcases hc with h | h <;> rw [h] <;> decide

/-- The current statistics generation also bounds joint credits while the
correction lane is still performing the rescale stores of that generation. -/
theorem correctionProbabilityWaitBudgetInsideRescale {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {i : EvId} {e : Event} (he : X.get i = some e)
    (hRange : if stage.val = 0 then 8007 ≤ e.pc ∧ e.pc ≤ 8223
      else 8226 ≤ e.pc ∧ e.pc ≤ 8442) :
    ((X.tr i.1).take i.2).countP (correctionProbabilityMark stage) + 1 ≤
      ((X.tr i.1).take i.2).countP (correctionStatsWaitMark stage) := by
  apply correctionProbabilityWaitBudgetAt hX stage he
  fin_cases stage <;> dsimp at hRange <;> simp [outstanding] <;> split_ifs <;> omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
include hp hX stage

private theorem namedWaitOperands {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hLen : j+1 < (X.tr g).length) (hm : correctionStatsWaitMark stage e = true) :
    Thread.BarrierArrival X (g,j) (statsBarrierId l g stage) (some 64) .sync := by
  obtain ⟨_, hRun⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨s, _, hStep, _⟩ := hRun.after_event he hLen
  obtain ⟨ins, hc, _, _⟩ := estep_event_source hStep
  have hw : isWait stage s.pc = true := by
    rwa [← estep_source_pc hStep]
  have hAudit := creditControlAt stage false hc
  simp only [creditControl, Bool.and_eq_true, hw, Bool.not_true, Bool.false_or] at hAudit
  have hOp := hAudit.1.1.2.2
  obtain ⟨_, id, cnt, mode, hKind⟩ := markedBarrierContinues rfl hc hOp hStep
  have ee : e = ⟨e.pc, .bar id cnt mode⟩ := by
    cases e
    exact congrArg (Event.mk _) hKind
  have hf := he.trans (congrArg some ee)
  have hSite : e.pc ∈ correctionStatsSites stage := by
    simpa [correctionStatsWaitMark, isWait] using hm
  have hId := actualCorrectionStatsBarrierId hp hX stage hSite hf
  obtain ⟨_, hCnt, hMode, _⟩ := actualNamedBarrier hp hX hf
  have hBoth : namedBarrierCount e.pc = some 64 ∧ namedBarrierMode e.pc = .sync := by
    fin_cases stage <;> simp [correctionStatsSites] at hSite
    all_goals rcases hSite with h | h | h <;> rw [h] <;> decide
  exact ⟨e, he, by rw [hKind, hId, hCnt, hMode, hBoth.1, hBoth.2]⟩

private theorem markerAgreesWithId {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hLen : j+1 < (X.tr g).length)
    (hWarp : 8 ≤ Prologue.warpIndex l g ∧ Prologue.warpIndex l g < 12) :
    correctionStatsWaitMark stage e = true ↔ Execution.isBarId (statsBarrierId l g stage) e =
      true := by
  constructor
  · intro hm
    obtain ⟨f, hf, hk⟩ := namedWaitOperands hp hX stage he hLen hm
    have hEq := Option.some.inj (he.symm.trans hf)
    rw [hEq]
    simp [Execution.isBarId, hk]
  · intro hm
    obtain ⟨pc, cnt, mode, rfl⟩ := NamedBar.isBarId_form hm
    obtain ⟨hSite, hCount, _, _⟩ := actualNamedBarrier hp hX he
    have hId : statsBarrierId l g stage < 11 := by
      have hW := Nat.mod_lt (Prologue.warpIndex l g) (by decide : 0 < 4)
      have hs := stage.isLt
      unfold statsBarrierId
      omega
    have hMin : 3 ≤ statsBarrierId l g stage := by unfold statsBarrierId; omega
    have hC : cnt = some 64 := by
      have h := actualNamedBarrierCountById hp hX he
      simpa [countOfBarrierId, hId, show statsBarrierId l g stage ≠ 0 by omega,
        show statsBarrierId l g stage ≠ 2 by omega] using h
    have hFamily := count64StatsSites hSite (hCount.symm.trans hC)
    have hRole := namedStatsRole hp hX he hFamily
    rcases hFamily with hS | ⟨other, hS⟩
    · simp only [softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hRole with h | h
      · omega
      · split_ifs at h <;> omega
    · have hh := actualCorrectionStatsBarrierId hp hX other hS he
      have hEq : stage = other := Fin.ext (by unfold statsBarrierId at hh; omega)
      subst other
      simpa [correctionStatsWaitMark, isWait] using hS

/-- Before a reached event, the correction stage's wait markers count exactly the actual
arrivals for its statistics barrier identifier. -/
theorem correctionWaitPrefixCount {g index : Nat} (hIndex : index < (X.tr g).length)
    (hWarp : 8 ≤ Prologue.warpIndex l g ∧ Prologue.warpIndex l g < 12) :
    ((X.tr g).take index).countP (correctionStatsWaitMark stage) =
      ((X.tr g).take index).countP (Execution.isBarId (statsBarrierId l g stage)) := by
  apply List.countP_congr
  intro x hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
  have hK := (List.getElem?_eq_some_iff.mp hk).1
  simp only [List.length_take] at hK
  rw [List.getElem?_take_of_lt (by omega)] at hk
  exact markerAgreesWithId hp hX stage (g := g) (j := k) hk (by omega) hWarp

/-- Find the actual returned statistics wait at a covered local ordinal. -/
theorem correctionNamedWaitAtOrdinal {g i n : Nat} (hLen : i < (X.tr g).length)
    (hn : n < ((X.tr g).take i).countP (correctionStatsWaitMark stage)) :
    ∃ j < i, Thread.BarrierArrival X (g,j) (statsBarrierId l g stage) (some 64) .sync ∧
      (Thread.correctionBefore X (g,j)).barrier (statsBarrierId l g stage) = n := by
  obtain ⟨j, f, hf, hm, hPrefix⟩ :=
    MbarRing.Slot.exists_nth_countP (correctionStatsWaitMark stage) hn
  have hj : j < i := by
    have ht := (List.getElem?_eq_some_iff.mp hf).1
    simp only [List.length_take] at ht
    omega
  rw [List.getElem?_take_of_lt hj] at hf
  have hFirst := namedWaitOperands hp hX stage (g := g) (j := j) hf (by omega) hm
  have hSite : f.pc ∈ correctionStatsSites stage := by
    simpa [correctionStatsWaitMark, isWait] using hm
  have hWarp : 8 ≤ Prologue.warpIndex l g ∧ Prologue.warpIndex l g < 12 := by
    have hPc : 7935 ≤ f.pc ∧ f.pc < 9205 := by
      fin_cases stage <;> simp [correctionStatsSites] at hSite <;> omega
    have hh : f.pc ∉ registerHintSites := by
      simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hR := roleBodyPcOfEvent hp hX (g := g) (index := j) hf (by omega) hh
    rcases hR with h | h
    · omega
    · split_ifs at h <;> omega
  refine ⟨j, hj, hFirst, ?_⟩
  rw [Thread.correctionBarrierOrdinal]
  change (((X.tr g).take j).countP (Execution.isBarId (statsBarrierId l g stage))) = n
  rw [← correctionWaitPrefixCount hp hX stage (by omega : j < (X.tr g).length) hWarp]
  simpa [List.take_take, Nat.min_eq_left hj.le] using hPrefix


/-- An actual statistics credit follows the lane's returned statistics wait of the same ordinal. -/
theorem correctionCreditAfterNamedWait {g i : Nat} {e : Event} (he : X.get (g,i) = some e)
    (hc : correctionStatsCreditMark stage e = true) :
    ∃ j < i, Thread.BarrierArrival X (g,j) (statsBarrierId l g stage) (some 64) .sync ∧
      (Thread.correctionBefore X (g,j)).barrier (statsBarrierId l g stage) =
        ((X.tr g).take i).countP (correctionStatsCreditMark stage) := by
  have hCount := correctionCreditRequiresWait hX stage he hc
  let n := ((X.tr g).take i).countP (correctionStatsCreditMark stage)
  have hn : n < ((X.tr g).take i).countP (correctionStatsWaitMark stage) :=
    (Nat.lt_succ_self n).trans_eq hCount.symm
  exact correctionNamedWaitAtOrdinal hp hX stage (List.getElem?_eq_some_iff.mp he).1 hn

omit hp hX stage in
/-- Both role groups share one correction-credit object per stage. -/
def statsCreditLoc (l : Launch) (cta : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, cta, l.sharedBase + (192 + 8 * stage.val)⟩

/-- A correction credit returns one unit to the shared stage resource. -/
theorem correctionStatsCreditPayload {i : EvId} {e : Event} (he : X.get i = some e)
    (hc : correctionStatsCreditMark stage e = true) {target : Loc} {tx units : Nat} {rel : Bool}
    {scope : MbarScope} (hk : e.kind = .arrive target tx units rel scope) :
    e.kind = .arrive (statsCreditLoc l (i.1 / l.block) stage) 0 1 rel scope := by
  have hSite : e.pc ∈ creditSites stage := by
    simpa [correctionStatsCreditMark, isCredit] using hc
  have hSet : e.pc ∈ [7987, 8224, 8443, 8464, 8468, 8764] := by
    fin_cases stage <;> simp [creditSites] at hSite ⊢ <;> tauto
  have hAddrSet : e.pc ∈ [7752, 7754, 7987, 8223, 8224, 8442, 8443, 8464, 8468,
      8759, 8760, 8764, 9055, 9056] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hSet ⊢
    tauto
  have ee : e = ⟨e.pc, .arrive target tx units rel scope⟩ := by
    cases e
    exact congrArg (Event.mk _) hk
  have hE := he.trans (congrArg some ee)
  have ⟨hTx, hN⟩ := correctionStatsCreditUnits hp hX hE hSet
  have hL := correctionArriveAddressExact hp hX hE hAddrSet
  rw [hk, hTx, hN, hL]
  fin_cases stage <;> simp [creditSites] at hSite
  all_goals rcases hSite with h | h | h <;> rw [h] <;> rfl


omit hp hX stage in
private theorem creditKindOfContinues {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (he : EStep kernel Assumptions.all l g s e (some u))
    (hm : correctionStatsCreditMark stage e = true) :
    ∃ target tx n rel scope, e.kind = .arrive target tx n rel scope := by
  have hSite : isCredit stage s.pc = true := (estep_source_pc he) ▸ hm
  obtain ⟨i, hc, _, hFire⟩ := estep_event_source he
  have hAudit := creditControlAt stage false hc
  simp only [creditControl, Bool.and_eq_true, hSite, Bool.not_true, Bool.false_or] at hAudit
  have hOp := hAudit.1.2.2
  cases ho : i.op <;> simp only [ho, arrivalOp, Bool.false_eq_true] at hOp
  rw [ho] at hFire
  obtain ⟨_, loc, tx, n, rel, scope, hk, _⟩ := fires_arrive_state hFire
  exact ⟨loc, tx, n, rel, scope, hk⟩

omit hp hX stage in
private theorem markedCreditReturnsForward {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (probability : Bool) (he : EStep kernel Assumptions.all l g s e (some u))
    (hm : isCredit stage e.pc probability = true) : u.pc = e.pc+1 := by
  have hSite : isCredit stage s.pc probability = true := (estep_source_pc he) ▸ hm
  obtain ⟨i, hc, _, hFire⟩ := estep_event_source he
  have hAudit := creditControlAt stage probability hc
  simp only [creditControl, Bool.and_eq_true, hSite, Bool.not_true, Bool.false_or] at hAudit
  have hOp := hAudit.1.2.2
  cases ho : i.op <;> simp only [ho, arrivalOp, Bool.false_eq_true] at hOp
  rw [ho] at hFire
  obtain ⟨rfl, _⟩ := fires_arrive_state hFire
  rw [estep_source_pc he]
  cases ‹Option Nat› <;> rfl

omit hp hX stage in
/-- A returning statistics credit advances past its decoded arrival. -/
theorem correctionCreditReturnsForward {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (he : EStep kernel Assumptions.all l g s e (some u))
    (hm : correctionStatsCreditMark stage e = true) : u.pc = e.pc+1 :=
  markedCreditReturnsForward stage false he hm

omit hp hX stage in
/-- A returning joint probability credit advances past its decoded arrival. -/
theorem correctionProbabilityReturnsForward {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (he : EStep kernel Assumptions.all l g s e (some u))
    (hm : correctionProbabilityMark stage e = true) : u.pc = e.pc+1 :=
  markedCreditReturnsForward stage true he hm

/-- A continuing correction credit site yields the corresponding role observation. -/
theorem creditObservationOfMark {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hMore : j+1 < (X.tr g).length) (hm : correctionStatsCreditMark stage e = true) :
    Thread.correctionAction e = some (.statsCredit stage) := by
  obtain ⟨_, hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨_, _, heStep, _⟩ := hr.after_event he hMore
  obtain ⟨loc, tx, n, rel, scope, hk⟩ := creditKindOfContinues stage heStep hm
  have hSite := (correctionStatsCreditMark_iff stage e).mp hm
  have hAll : e.pc ∈ [7987, 8224, 8443, 8464, 8468, 8764] := by
    fin_cases stage <;> simp at hSite ⊢ <;> tauto
  have ee : e = ⟨e.pc, .arrive loc tx n rel scope⟩ := by
    cases e
    exact congrArg (Event.mk _) hk
  obtain ⟨hTx, _, hRel, hScope⟩ :=
    correctionStatsCreditOperands hp hX (he.trans (congrArg some ee)) hAll
  rw [hTx, hRel, hScope] at hk
  exact (Thread.correctionStatsCreditObservation stage hk).mpr hSite

/-- The role cursor counts exactly the concrete credits before any reached event. -/
theorem correctionCreditCursor {i : EvId} {e : Event} (he : X.get i = some e) :
    (Thread.correctionBefore X i).count (.statsCredit stage) =
      ((X.tr i.1).take i.2).countP (correctionStatsCreditMark stage) := by
  have hi : i.2 < (X.tr i.1).length := (List.getElem?_eq_some_iff.mp he).1
  rw [Thread.correctionBefore_count]
  refine List.countP_congr (fun f hf => ?_)
  rw [decide_eq_true_eq]
  constructor
  · intro hc
    obtain ⟨loc, count, hk⟩ := Thread.correctionStatsCreditKind hc
    exact (correctionStatsCreditMark_iff stage f).mpr
      ((Thread.correctionStatsCreditObservation stage hk).mp hc)
  · intro hm
    obtain ⟨j, hJ⟩ := List.mem_iff_getElem?.mp hf
    have hj := (List.getElem?_eq_some_iff.mp hJ).1
    simp only [List.length_take] at hj
    rw [List.getElem?_take_of_lt (by omega)] at hJ
    exact creditObservationOfMark hp hX stage (g := i.1) (j := j) hJ (by omega) hm

/-- The statistics credit of a lane witnesses release of its rendezvous at that ordinal. -/
theorem correctionCreditWitnessesRelease {g i : Nat} {e : Event} (he : X.get (g,i) = some e)
    (hc : correctionStatsCreditMark stage e = true) :
    let id := statsBarrierId l g stage
    let n := ((X.tr g).take i).countP (correctionStatsCreditMark stage)
    CtaBarDone l X (g / l.block) (id + 16*n) := by
  obtain ⟨j, hj, ⟨⟨pc, k⟩, hw, hk⟩, hOrd⟩ := correctionCreditAfterNamedWait hp hX stage he hc
  change k = _ at hk
  subst k
  have hLen : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hPass : (g,j).2+1 < (X.tr (g,j).1).length := by
    change j+1 < (X.tr g).length
    omega
  obtain ⟨key, hRecorded, hDone⟩ := ctaBarDone_of_returned hX hw hPass
  have hW := Nat.mod_lt (Prologue.warpIndex l g) (by decide : 0 < 4)
  have hS := stage.isLt
  let warp : Fin 8 := ⟨Prologue.warpIndex l g % 4 + 4 * stage.val, by omega⟩
  have hId : 3 + warp.val = statsBarrierId l g stage := by
    simp only [warp, statsBarrierId]
    omega
  have hSources := hId ▸ statsBarrierSources hp hX warp
  have hShape := hId ▸ statsBarrierShape hp warp
  have hKey := hSources.arrival_key hX hShape hw (CtaBarK.arrival hRecorded)
  rw [Thread.correctionBarrierOrdinal] at hOrd
  rw [hKey, hOrd] at hDone
  exact hDone

/-- An observed correction credit releases the named rendezvous indexed by its role cursor. -/
theorem observedCorrectionCreditReleases {i : EvId} {e : Event} (he : X.get i = some e)
    (hCredit : Thread.correctionAction e = some (.statsCredit stage)) :
    let id := statsBarrierId l i.1 stage
    let n := (Thread.correctionBefore X i).count (.statsCredit stage)
    CtaBarDone l X (i.1 / l.block) (id + 16*n) := by
  obtain ⟨loc, units, hk⟩ := Thread.correctionStatsCreditKind hCredit
  have hs := (Thread.correctionStatsCreditObservation stage hk).mp hCredit
  dsimp only
  rw [correctionCreditCursor hp hX stage he]
  exact correctionCreditWitnessesRelease hp hX stage he
    ((correctionStatsCreditMark_iff stage e).mpr hs)

end PTX.Kernels.TmlFa4Fwd.Correction
