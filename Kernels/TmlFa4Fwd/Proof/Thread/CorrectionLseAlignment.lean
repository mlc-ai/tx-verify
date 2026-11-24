-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseProducer
public import Kernels.TmlFa4Fwd.Proof.CorrectionLseResult
import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixEvents
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
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction

private theorem compareReachedPrefixes {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {t u v : TState} {before other tail rest : List Event}
    (h : TraceReach K A l g t before u) (h' : TraceReach K A l g t other v)
    (hTrace : before ++ tail = other ++ rest) :
    (∃ es, TraceReach K A l g u es v) ∨ ∃ es, TraceReach K A l g v es u := by
  induction h generalizing other v with
  | refl => exact .inl ⟨_, h'⟩
  | @tau s t u es ht hu ih =>
    cases h' with
    | refl => exact .inr ⟨_, .tau ht hu⟩
    | tau ht' h' =>
      cases tau_det ht ht'
      exact ih h' hTrace
    | event he' _ => exact (not_tau_of_stops (stops_of_estep he') ht).elim
  | @event s t u es e he hu ih =>
    cases h' with
    | refl => exact .inr ⟨_, .event he hu⟩
    | tau ht _ => exact (not_tau_of_stops (stops_of_estep he) ht).elim
    | event he' h' =>
      simp only [List.cons_append, List.cons.injEq] at hTrace
      obtain ⟨rfl, hTail⟩ := hTrace
      cases estep_det he he'
      exact ih h' hTail

private def windowStart (stage : Fin 2) : Nat := if stage = 0 then 9061 else 9074

private def aboveWindow (lo : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || Epilogue.ordinaryEvent i.op) &&
    match i.op with
    | .bra dst _ => lo < dst
    | .brx .. => false
    | _ => true

private theorem aboveWindowAtCode (stage : Fin 2) {pc : Nat} {i : Instr}
    (hLo : windowStart stage ≤ pc) (hc : kernel.code[pc]? = some i) :
    aboveWindow (windowStart stage) i = true := by
  let lo := windowStart stage
  have hAll : (kernel.code.drop lo).all (aboveWindow lo) = true := by
    fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll i
  apply List.mem_of_getElem? (i := pc - lo)
  rw [List.getElem?_drop, Nat.add_sub_of_le hLo, hc]

private theorem windowInitialLocal (stage : Fin 2) :
    ∃ i, kernel.code[windowStart stage]? = some i ∧ i.op.isLocal = true := by
  fin_cases stage
  · exact ⟨_, Flow.code_9061, rfl⟩
  · exact ⟨_, Flow.code_9074, rfl⟩

private theorem staysAboveWindow (stage : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hs : windowStart stage ≤ s.pc)
    (hStep : WStep kernel Assumptions.all l g s e u) :
    windowStart stage < u.pc := by
  have hLo : 9061 ≤ s.pc := by
    have h := hs
    fin_cases stage <;> simp [windowStart] at h <;> omega
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, _, hT⟩ := correctionTauFrame hOff ht
    have hCode := (Bool.and_eq_true_iff.mp (aboveWindowAtCode stage hs hc)).2
    rcases hT with ⟨rfl, _⟩ | ⟨_, _, hF⟩
    · change windowStart stage < s.pc + 1
      omega
    have hPc := hF.pc
    cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
    case bra dst uni => rw [hPc]; simpa [ho] using hCode
    case brx => simp [ho] at hCode
    all_goals omega
  · obtain ⟨i, hc, hLocal, hFire⟩ := estep_event_source he
    have hStrict : windowStart stage < s.pc := by
      by_contra! hNo
      have hPc : s.pc = windowStart stage := by omega
      obtain ⟨j, hCode, hL⟩ := windowInitialLocal stage
      rw [hPc, hCode] at hc
      obtain rfl := Option.some.inj hc
      rw [hL] at hLocal
      cases hLocal
    have hOp := (Bool.and_eq_true_iff.mp (aboveWindowAtCode stage hs hc)).1
    simp only [hLocal, Bool.false_or] at hOp
    rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hOp) hFire with h | h <;> omega

private theorem reachedWindowOnce (stage : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} (hr : TraceReach kernel Assumptions.all l g s es u)
    (hLo : windowStart stage ≤ s.pc) (hAt : u.pc = windowStart stage) : u = s := by
  induction hr with
  | refl => rfl
  | tau ht hTail ih =>
    have hGt := staysAboveWindow stage hLo (.inl ⟨rfl, ht⟩)
    have hEq := ih hGt.le hAt
    rw [← hEq, hAt] at hGt
    exact (Nat.lt_irrefl _ hGt).elim
  | event he hTail ih =>
    have hGt := staysAboveWindow stage hLo (.inr ⟨_, rfl, he⟩)
    have hEq := ih hGt.le hAt
    rw [← hEq, hAt] at hGt
    exact (Nat.lt_irrefl _ hGt).elim

/-- Two cuts of the same selected correction trace at the LSE window have the same state. -/
theorem LseWindowInputs.sameReachedWindow {l : Launch} {X : Execution} {store : EvId}
    {stage : Fin 2} {pos : Nat} {initial s t : TState}
    {sum maximum : List (Option Byte)} {before other tail rest : List Event}
    (hWindow : LseWindowInputs l X store stage pos s sum maximum)
    (hPc : t.pc = (if stage = 0 then 9061 else 9074))
    (h : TraceReach kernel Assumptions.all l store.1 initial before s)
    (h' : TraceReach kernel Assumptions.all l store.1 initial other t)
    (hTrace : (X.tr store.1).drop pos = before ++ tail)
    (hTrace' : (X.tr store.1).drop pos = other ++ rest) : s = t := by
  have hs : s.pc = windowStart stage := hWindow.atWindow
  have ht : t.pc = windowStart stage := hPc
  rcases compareReachedPrefixes h h' (hTrace.symm.trans hTrace') with ⟨es, hR⟩ | ⟨es, hR⟩
  · exact (reachedWindowOnce stage hR (Nat.le_of_eq hs.symm) ht).symm
  · exact reachedWindowOnce stage hR (Nat.le_of_eq ht.symm) hs

/-- Inputs captured at the actual arithmetic window of a correction lane. -/
structure LseWindowObservation (p : Params) (l : Launch) (X : Execution) (store : EvId)
    (stage : Fin 2) (first : Nat) (state : TState) (sum maximum : List (Option Byte)) : Prop where
  inputs : LseWindowInputs l X store stage first state sum maximum
  scale : state.regs 7134 = some (b32 p.scaleLog2Bits)
  selector : stage = 0 → FirstLseSelector state sum

/-- The numerical cursor at the selected producer's terminal statistics publication. -/
structure TerminalLseProduction (p : Params) (l : Launch) (X : Execution) (g : Nat)
    (stage : Fin 2) (publication batch tile head : Nat) : Prop where
  payload :
    ∃ producer producerEnd blocks refs sums maxValue,
      TerminalSoftmaxStatistics p l g batch tile head stage producer blocks refs sums maxValue ∧
      Run kernel Assumptions.all l (terminalStatsProducer l g stage) producer
        ((X.tr (terminalStatsProducer l g stage)).drop (publication - 2)) producerEnd

/-- The window values for reads made by a specified CTA. -/
def LseWindowValuesFromReadsAt (p : Params) (l : Launch) (X : Execution) (cta : Nat) : Prop :=
  ∀ {store : EvId} {stage : Fin 2} {wait first batch : Nat} {state : TState}
    {sum maximum : List (Option Byte)},
    store.1 / l.block = cta → TerminalLseReads l X store stage wait sum maximum →
    LseWindowObservation p l X store stage first state sum maximum →
    batch < p.batch → tilePrefix p batch * p.heads ≤ store.1 / l.block →
    store.1 / l.block < tilePrefix p (batch + 1) * p.heads →
    let coords := assignedCoordinates p batch (store.1 / l.block)
    stageRow coords.1 stage + rowOf l store.1 < p.qLength batch →
    LseStatisticsAt p batch coords.2 (stageRow coords.1 stage + rowOf l store.1) stage state

/-- A semantic readout supplies the statistics at the selected lane's actual window. -/
theorem observedValidLseStatisticsAtOfReads {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (hValues : LseWindowValuesFromReadsAt p l X cta) :
    ObservedValidLseStatisticsAt p l X cta := by
  intro g batch lane pos j pc a bytes initial o hOwner hl hb hLo hHi hInitial hRun hIndex hGet
  dsimp only
  intro stage t consumed es visits hStage hRow hPc hTrace hReach _ _
  let thread := warpLane l g lane
  let store : EvId := (thread, j)
  have hCta : warpLane l g lane / l.block = g / l.block := by
    unfold warpLane laneOf
    rw [hp.block]
    omega
  have hStore : LseStored X store stage := LseStored.ofEvent (hStage ▸ hGet)
  obtain ⟨wait, sum, maximum, s, reached, rest, hSplit, hAt, hRead, hWindow, hScale, hSelector⟩ :=
    terminalInputsOfSelectedLse hp hX hb hInitial hRun hIndex hStore
  have hStats := hValues (hCta.trans hOwner) hRead ⟨hWindow, hScale, hSelector⟩ hb
    (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (by simpa only [hCta] using hRow)
  have hSame := hWindow.sameReachedWindow hPc hAt hReach hSplit hTrace
  rw [hSame] at hStats
  simpa only [hCta] using hStats

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
