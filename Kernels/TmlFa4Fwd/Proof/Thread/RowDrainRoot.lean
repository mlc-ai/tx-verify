-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
public import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import all Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainWords
import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerPrefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleRoute
import Kernels.TmlFa4Fwd.Proof.CorrectionLseFromSelected
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
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
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Lemmas.Flow.TcTmpl
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame Softmax Epilogue Prologue PTX.Assumption

/-- Both row-processing roles drain the request schedule after finishing their work. -/
inductive RowDrainRole where
  | softmax | correction

namespace RowDrainRole

def schedulerFloor : RowDrainRole → Nat
  | .softmax => 3155
  | .correction => 7807

def start : RowDrainRole → Nat
  | .softmax => 7605
  | .correction => 9083

def exitFloor : RowDrainRole → Nat
  | .softmax => 7733
  | .correction => 9201

def laneReg : RowDrainRole → Nat
  | .softmax => 1215
  | .correction => 1616

def ctaReg : RowDrainRole → Nat
  | .softmax => 1072
  | .correction => 1618

def firstRead : RowDrainRole → Nat
  | .softmax => 7621
  | .correction => 9089

def laterRead : RowDrainRole → Nat
  | .softmax => 7677
  | .correction => 9144

def frame (role : RowDrainRole) (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(role.laneReg,b32 (laneOf l g)),(7506,b64 p.cuQBase),(role.ctaReg,b32 (g/l.block))]

end RowDrainRole

/-- A decoded interval with one checkpoint and a forward bypass. -/
structure RowDrainSpan where
  lo : Nat
  stop : Nat
  bypass : Nat

namespace RowDrainSpan

def destinationsOk (span : RowDrainSpan) (op : Op) : Bool :=
  match op with
  | .bra dest _ => decide (span.lo ≤ dest) &&
      (decide (dest ≤ span.stop) || decide (span.bypass ≤ dest))
  | .brx .. => false
  | _ => true

def isWaitLd : Op → Bool
  | .tcWaitLd => true
  | _ => false

def inspected (span : RowDrainSpan) (regs : List Nat) (op : Op) : Bool :=
  (op.isLocal || (scoreEventOp op || isWaitLd op)) &&
    (0 :: regs).all
      (fun r => !((writesRegs op ++ scoreEventWrites op).contains r)) &&
    destinationsOk span op

private theorem inspectedAt (span : RowDrainSpan) {regs : List Nat} {pc : Nat} {i : Instr}
    (hAudit : ((kernel.code.drop span.lo).take (span.stop-span.lo)).all
      (fun i => span.inspected regs i.op) = true)
    (hLo : span.lo ≤ pc) (hHi : pc < span.stop)
    (hc : kernel.code[pc]? = some i) : span.inspected regs i.op = true := by
  apply List.all_eq_true.mp hAudit i
  apply List.mem_of_getElem? (i := pc-span.lo)
  rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]

/-- The audited software segments stay within the span and preserve its live registers. -/
def segmentKeeps (span : RowDrainSpan) (regs : List Nat) : Prop :=
  ∀ pc, span.lo ≤ pc → pc < span.stop → pc ∈ Assumptions.swExp2Sites →
    ∀ seg, cuteExp2.matchAt kernel pc = some seg →
      span.lo ≤ seg.stop ∧ seg.stop ≤ span.stop ∧
        ∀ r ∈ regs, r ∉ scoreSegmentWrites seg

theorem segmentKeeps_of_audit (span : RowDrainSpan) (regs : List Nat)
    (hAudit : Assumptions.swExp2Sites.all (fun site =>
      if span.lo ≤ site ∧ site < span.stop then
        match cuteExp2.matchAt kernel site with
        | some m => decide (span.lo ≤ m.stop ∧ m.stop ≤ span.stop) &&
            regs.all (fun r => !(scoreSegmentWrites m).contains r)
        | none => false
      else true) = true) : span.segmentKeeps regs := by
  intro pc hLo hHi hHere seg hm
  have h := List.all_eq_true.mp hAudit pc hHere
  rw [ite_eq_left ⟨hLo,hHi⟩,hm] at h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at h
  exact ⟨h.1.1,h.1.2,fun r hr => by simpa using List.all_eq_true.mp h.2 r hr⟩

theorem traceAboveExit (span : RowDrainSpan) {l : Launch} {g : Nat} {s t : TState}
    {es : List Event} (hr : TraceReach kernel Assumptions.all l g s es t)
    (hCode : (kernel.code.drop span.bypass).all
      (fun i => staysPastEvent span.bypass i.op) = true)
    (hSites : ∀ pc ∈ Assumptions.swExp2Sites, pc < span.bypass)
    (hs : span.bypass ≤ s.pc) : span.bypass ≤ t.pc := by
  have hNext {a b : TState} {e : Option Event} (ha : span.bypass ≤ a.pc)
      (he : WStep kernel Assumptions.all l g a e b) : span.bypass ≤ b.pc :=
    eventTailStep hCode (fun pc hlo hm _ _ => (Nat.not_lt_of_ge hlo (hSites pc hm)).elim) ha he
  induction hr with
  | refl => exact hs
  | tau ht _ ih => exact ih (hNext hs (.inl ⟨rfl,ht⟩))
  | event ht _ ih => exact ih (hNext hs (.inr ⟨_,rfl,ht⟩))

private theorem waitLdFrame {l : Launch} {g : Nat} {s t : TState} {e : Event}
    (hBlock : l.block % 32 = 0) {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
    (hOp : ins.op = .tcWaitLd) (he : EStep kernel Assumptions.all l g s e (some t)) :
    t = next s := by
  obtain ⟨i,hCode,_,hFire⟩ := estep_event_source he
  have hEq := Option.some.inj (hCode.symm.trans hc)
  rw [hEq,hOp] at hFire
  change Fires s.pc (tcTmpl l g s .tcWaitLd) e (some t) at hFire
  rw [tc_waitLd hBlock] at hFire
  exact Option.some.inj hFire.2

private theorem step (span : RowDrainSpan) {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {s t : TState} {e : Option Event} {F : List (Nat × Value)}
    (hAudit : ((kernel.code.drop span.lo).take (span.stop-span.lo)).all
      (fun i => span.inspected (F.map Prod.fst) i.op) = true)
    (hSegments : span.segmentKeeps (F.map Prod.fst))
    (hLo : span.lo ≤ s.pc) (hHi : s.pc < span.stop)
    (hSub : s.sub ≤ 3) (hS : ScoreScratchState s)
    (hR : Holds s.regs F) (he : WStep kernel Assumptions.all l g s e t) :
    span.lo ≤ t.pc ∧ (t.pc ≤ span.stop ∨ span.bypass ≤ t.pc) ∧
      t.sub ≤ 3 ∧ ScoreScratchState t ∧ Holds t.regs F := by
  have forward {n : Nat} (hn : n = s.pc + 1) : span.lo ≤ n ∧ n ≤ span.stop := by
    omega
  let regs := F.map Prod.fst
  have preserve (h : ∀ r ∈ regs, t.regs r = s.regs r) : Holds t.regs F :=
    holdsSchedulerFrame hR h (fun _ hm => List.mem_map_of_mem hm)
  rcases he with ⟨rfl,ht⟩ | ⟨ev,rfl,he⟩
  · have hScratch := scoreScratchTau ht hS
    obtain ⟨ins,hCode,_,hSkip | hLocal⟩ := tauScoreSource ht
    · obtain ⟨rfl,_⟩ := hSkip
      have h := forward (n := (skip s).pc) rfl
      exact ⟨h.1,.inl h.2,Nat.zero_le _,hScratch,hR⟩
    · rcases scoreExecLocal hLocal.2.2 with hFrame | ⟨seg,hSite,hMatch,hExec⟩
      · have hAudit := inspectedAt span hAudit hLo hHi hCode
        simp only [inspected,Bool.and_eq_true] at hAudit
        have hDest : span.lo ≤ t.pc ∧
            (t.pc ≤ span.stop ∨ span.bypass ≤ t.pc) := by
          have hPc := hFrame.pc
          cases hop : ins.op <;> simp only [hop,nextPc,BrxTarget,or_false] at hPc
          case bra dest uni =>
            rw [hPc]
            simpa [destinationsOk,hop] using hAudit.2
          case brx => simp [destinationsOk,hop] at hAudit
          all_goals have h := forward hPc; exact ⟨h.1,.inl h.2⟩
        refine ⟨hDest.1,hDest.2,hFrame.sub ▸ hSub,hScratch,?_⟩
        apply preserve
        intro r hm
        have hn := List.all_eq_true.mp hAudit.1.2 _ (List.mem_cons_of_mem _ hm)
        exact hFrame.regs r (by
          simpa using (show r ∉ writesRegs ins.op ∧ r ∉ scoreEventWrites ins.op by
            simpa using hn).1)
      · obtain ⟨hPc,hReset,_,hRegs⟩ := scoreSegmentFrame hExec
        have h := hSegments _ hLo hHi hSite _ hMatch
        exact ⟨hPc.symm ▸ h.1,.inl (hPc.symm ▸ h.2.1),hReset.symm ▸ Nat.zero_le _,
          hScratch, preserve (fun r hr => hRegs r (h.2.2 r hr))⟩
  · obtain ⟨ins,hCode,hLocal,_⟩ := estep_event_source he
    have hAudit := inspectedAt span hAudit hLo hHi hCode
    simp only [inspected,Bool.and_eq_true,hLocal,Bool.false_or,Bool.or_eq_true] at hAudit
    rcases hAudit.1.1 with hOp | hWait
    · have hKeep (r : Nat) (hr : r ∈ 0 :: regs) :
          r ∉ scoreEventWrites ins.op := by
        have hk := List.all_eq_true.mp hAudit.1.2 r hr
        exact (show r ∉ writesRegs ins.op ∧ r ∉ scoreEventWrites ins.op by
          simpa using hk).2
      have hk := hKeep 0 (by simp)
      have hP := (scoreEventStep hCode hOp hSub hk he).1
      have hReady : ScoreScratchReady ins.op s := by
        simpa only [ScoreScratchState,hCode,hLocal,Bool.false_eq_true,ite_false] using hS
      have hScratch := scoreEventScratch hCode hOp hSub hk he hReady
      have hh : span.lo ≤ t.pc ∧ t.pc ≤ span.stop := by
        rcases hP.pc with ⟨hPc,_⟩ | ⟨hPc,_⟩ <;> omega
      refine ⟨hh.1,.inl hh.2,hP.sub,?_,preserve
        (fun r hr => (scoreEventStep hCode hOp hSub (hKeep r (List.mem_cons_of_mem _ hr)) he).2)⟩
      by_cases hs : t.pc = s.pc
      · simpa only [ScoreScratchState,hs,hCode,hLocal,Bool.false_eq_true,ite_false,ite_true]
          using hScratch
      · exact scratchStateOfClear (by simpa only [hs,ite_false] using hScratch)
    · have invert : ∀ op, isWaitLd op = true → op = .tcWaitLd := by
        intro op
        cases op <;> simp [isWaitLd]
      have hOp := invert ins.op hWait
      have hBlock : l.block % 32 = 0 := by rw [hp.block]
      obtain rfl := waitLdFrame hBlock hCode hOp he
      have h := forward (n := (next s).pc) rfl
      have hClear : ScoreScratchClear s := by
        simpa [ScoreScratchState,hCode,hOp,Op.isLocal,ScoreScratchReady] using hS
      exact ⟨h.1,.inl h.2,hSub,scratchStateOfClear hClear,hR⟩

theorem cut (span : RowDrainSpan) {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {s t : TState} {events : List Event} {F : List (Nat × Value)}
    (hAudit : ((kernel.code.drop span.lo).take (span.stop-span.lo)).all
      (fun i => span.inspected (F.map Prod.fst) i.op) = true)
    (hSegments : span.segmentKeeps (F.map Prod.fst))
    (hBypass : ∀ {a b : TState} {es : List Event},
      TraceReach kernel Assumptions.all l g a es b → span.bypass ≤ a.pc → span.bypass ≤ b.pc)
    (h : TraceReach kernel Assumptions.all l g s events t)
    (hAt : span.lo ≤ s.pc ∧ s.pc ≤ span.stop)
    (hSub : s.sub ≤ 3) (hS : ScoreScratchState s) (hR : Holds s.regs F)
    (hTarget : ¬ (span.lo ≤ t.pc ∧ t.pc < span.stop) ∧ t.pc < span.bypass) :
    ∃ u pre tail, events = pre ++ tail ∧ u.pc = span.stop ∧ ScoreScratchState u ∧
      Holds u.regs F ∧ TraceReach kernel Assumptions.all l g s pre u := by
  have stepWithin {a b : TState} {ev : Option Event} {es : List Event}
      (hAt : span.lo ≤ a.pc ∧ a.pc < span.stop)
      (hSub : a.sub ≤ 3) (hS : ScoreScratchState a) (hR : Holds a.regs F)
      (he : WStep kernel Assumptions.all l g a ev b)
      (hTail : TraceReach kernel Assumptions.all l g b es t) :
      (span.lo ≤ b.pc ∧ b.pc ≤ span.stop) ∧
        b.sub ≤ 3 ∧ ScoreScratchState b ∧ Holds b.regs F := by
    obtain ⟨hLo,hHi,hSub,hS,hR⟩ := span.step hp hAudit hSegments hAt.1 hAt.2 hSub hS hR he
    exact ⟨⟨hLo,hHi.resolve_right (fun hb =>
      (Nat.not_le_of_lt hTarget.2) (hBypass hTail hb))⟩,hSub,hS,hR⟩
  induction h with
  | refl s =>
    have hStop : s.pc = span.stop :=
      Nat.le_antisymm hAt.2 (Nat.le_of_not_gt (fun ht => hTarget.1 ⟨hAt.1,ht⟩))
    exact ⟨s,[],[],rfl,hStop,hS,hR,.refl _⟩
  | @tau a b t es ht hTail ih =>
    by_cases hStart : a.pc = span.stop
    · exact ⟨a,[],es,rfl,hStart,hS,hR,.refl _⟩
    have hLt := lt_of_le_of_ne hAt.2 hStart
    obtain ⟨hAt',hSub',hS',hR'⟩ := stepWithin ⟨hAt.1,hLt⟩ hSub hS hR (.inl ⟨rfl,ht⟩) hTail
    obtain ⟨u,pre,tail,hSplit,hPc,hShape,hRegs,hPath⟩ := ih hAt' hSub' hS' hR' hTarget stepWithin
    exact ⟨u,pre,tail,hSplit,hPc,hShape,hRegs,.tau ht hPath⟩
  | @event a b t es e he hTail ih =>
    by_cases hStart : a.pc = span.stop
    · exact ⟨a,[],e::es,rfl,hStart,hS,hR,.refl _⟩
    have hLt := lt_of_le_of_ne hAt.2 hStart
    obtain ⟨hAt',hSub',hS',hR'⟩ :=
      stepWithin ⟨hAt.1,hLt⟩ hSub hS hR (.inr ⟨_,rfl,he⟩) hTail
    obtain ⟨u,pre,tail,hSplit,hPc,hShape,hRegs,hPath⟩ := ih hAt' hSub' hS' hR' hTarget stepWithin
    exact ⟨u,e::pre,tail,congrArg (List.cons e) hSplit,hPc,hShape,hRegs,.event he hPath⟩

/-- Resume the observed suffix at a local checkpoint of an audited span. -/
theorem replayTo (span : RowDrainSpan) {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos j : Nat} {s : TState} {ending : Option TState}
    {F : List (Nat × Value)} {target : Event} {ins : Instr}
    (hCut : span.lo ≤ span.stop)
    (hCode : ((kernel.code.drop span.lo).take (span.stop-span.lo)).all
      (fun i => span.inspected (F.map Prod.fst) i.op) = true)
    (hSegments : span.segmentKeeps (F.map Prod.fst))
    (hBypass : ∀ {a b : TState} {es : List Event},
      TraceReach kernel Assumptions.all l g a es b → span.bypass ≤ a.pc → span.bypass ≤ b.pc)
    (hLocal : kernel.code[span.stop]? = some ins) (hOp : ins.op.isLocal = true)
    (hs : At s span.lo F) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hIndex : pos ≤ j) (he : X.get (g,j) = some target)
    (hSafe : ∀ f, target.kind ≠ .ub f)
    (hBand : ¬ (span.lo ≤ target.pc ∧ target.pc < span.stop) ∧ target.pc < span.bypass) :
    ∃ nextPos ≤ j, ∃ t, At t span.stop F ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop nextPos) ending := by
  have hIndexed : ((X.tr g).drop pos)[j-pos]? = some target := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hIndex]
    exact he
  obtain ⟨t,_,hPath,hStep⟩ := hr.before_event hIndexed
  have hAt : span.lo ≤ s.pc ∧ s.pc ≤ span.stop := by rw [hs.1]; exact ⟨le_rfl,hCut⟩
  have hSub : s.sub ≤ 3 := by rw [hs.2.1]; decide
  have hScratch := scratchStateOfClear (s := s) ⟨hs.2.1,hs.2.2.1⟩
  obtain ⟨u,pre,_,hSplit,hu,hShape,hFrame,hPrefix⟩ :=
    span.cut hp hCode hSegments hBypass hPath hAt hSub hScratch hs.2.2.2.2
      (estep_source_pc hStep ▸ hBand)
  obtain ⟨hOrder,hTail⟩ := Loader.resumeAtCut hr hIndex he hSplit hPrefix
  have hClear := scratchClearOfLocal (hu.symm ▸ hLocal) hOp hShape
  have hFault : u.fault = none := by
    cases hf : u.fault with
    | none => rfl
    | some f =>
      have hIndex : ((X.tr g).drop (pos+pre.length))[j-(pos+pre.length)]? = some target := by
        rw [List.getElem?_drop,Nat.add_sub_of_le hOrder]
        exact he
      exact (hSafe f (hTail.eventOfFault hf hIndex)).elim
  exact ⟨_,hOrder,u,⟨hu,hClear.1,hClear.2,hFault,hFrame⟩,hTail⟩

end RowDrainSpan

namespace RowDrainRole

private def entrySpan (role : RowDrainRole) : RowDrainSpan :=
  ⟨role.schedulerFloor,role.start,role.exitFloor⟩

variable (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X) {g j pc : Nat}
    {a : Acc} {bytes : List (Option Byte)} (hSites : pc = role.firstRead ∨ pc = role.laterRead)
include role hp hX hCuQ hSites

private theorem sourceCheckpoint (he : X.get (g,j) = some ⟨pc,.rd a bytes⟩) :
    ∃ pos ≤ j, ∃ s ending, role.schedulerFloor ≤ s.pc ∧ s.pc ≤ role.start ∧
      s.sub = 0 ∧ s.acc = [] ∧ Holds s.regs (role.frame p l g) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending := by
  have hg : g < l.threads := event_thread_lt hX he
  have h173 : 173 < pc := by rcases hSites with rfl | rfl <;> cases role <;> decide
  have hPc : roleBodyPc (warpIndex l g) pc := roleBodyPcOfEvent hp hX he h173 (by
    change pc ∉ registerHintSites
    rcases hSites with rfl | rfl <;> cases role <;> decide)
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hEvent : X.get (warpLane l g lane,j) = some ⟨pc,.rd a bytes⟩ := hLane.symm ▸ he
  cases role with
  | softmax =>
    have hPcBounds : 7621 ≤ pc ∧ pc ≤ 7677 := by
      rcases hSites with rfl | rfl <;> decide
    have hw : warpIndex l g < 8 := by
      unfold roleBodyPc at hPc
      rcases hPc with h | h
      · omega
      · split_ifs at h <;> omega
    have hTarget : 3150 < pc := by omega
    obtain ⟨ends,entry,follow⟩ := firstSchedulerRouteOfEvent hp hX hg hw hl hCuQ hEvent hTarget
    have hs := entry.checkpoint lane hl
    have hRegs : Holds (entry.state lane).regs (RowDrainRole.softmax.frame p l g) := by
      have hF := hs.2.2.2.2
      have hEq := congrArg (fun thread => Holds (entry.state lane).regs
        (RowDrainRole.softmax.frame p l thread)) hLane
      apply hEq.mp
      dsimp only [frame,laneReg,ctaReg]
      refine ⟨holds_mem hF (by simp [firstRouteFacts,firstScanFacts,schedulerLane]),
        holds_mem hF ?_,holds_mem hF ?_,trivial⟩ <;>
        simp [firstRouteFacts,firstScanFacts,schedulerLane,schedulerEntry,
          dispatchOutput,dispatchInput]
    have hBound : RowDrainRole.softmax.schedulerFloor ≤ (entry.state lane).pc ∧
        (entry.state lane).pc ≤ RowDrainRole.softmax.start := by
      rw [hs.1]
      split_ifs <;> decide
    have hr := (entry.continuation lane hl).after_local_nonempty
      (entry.localSteps lane hl) follow.nonempty
    rw [hLane] at hr
    exact ⟨entry.pos lane,follow.before,entry.state lane,ends lane,
      hBound.1,hBound.2,hs.2.1,hs.2.2.1,hRegs,hr⟩
  | correction =>
    have hPcBounds : 9089 ≤ pc ∧ pc ≤ 9144 := by
      rcases hSites with rfl | rfl <;> decide
    have hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
      unfold roleBodyPc at hPc
      rcases hPc with h | h
      · omega
      · split_ifs at h <;> omega
    have hTarget : 7801 < pc := by omega
    obtain ⟨ends,entry,follow⟩ := Correction.correctionFirstRouteOfEvent
      hp hX hg hw.1 hw.2 hl hTarget hEvent
    have hs := entry.checkpoint lane hl
    have hRegs : Holds (entry.state lane).regs (RowDrainRole.correction.frame p l g) := by
      have hF := hs.2.2.2.2
      have hEq := congrArg (fun thread => Holds (entry.state lane).regs
        (RowDrainRole.correction.frame p l thread)) hLane
      apply hEq.mp
      dsimp only [frame,laneReg,ctaReg]
      refine ⟨holds_mem hF ?_,holds_mem hF ?_,?_,trivial⟩
      · simp [Correction.correctionFirstRouteFacts,Correction.firstCorrectionScanFacts,
          Correction.firstShuffleFacts]
      · simp [Correction.correctionFirstRouteFacts,Correction.firstCorrectionScanFacts,
          Correction.firstShuffleFacts,Correction.afterCreditFacts,Correction.creditFacts,
          Correction.entryFacts,nonzeroBarrierFacts,abiFacts]
      · have hc := holds_mem hF (show (1618,b32 (g/l.block)) ∈
            Correction.correctionFirstRouteFacts p l g lane by
              simp [Correction.correctionFirstRouteFacts])
        have hBlock : l.block % 32 = 0 := by rw [hp.block]
        have hCta : (warpLane l g lane)/l.block = g/l.block :=
          (Step.sameWarp_lane hBlock hg hl).1.1.2.2.symm
        simpa only [hCta] using hc
    have hBound : RowDrainRole.correction.schedulerFloor ≤ (entry.state lane).pc ∧
        (entry.state lane).pc ≤ RowDrainRole.correction.start := by
      rw [hs.1]
      split_ifs <;> decide
    have hr := (entry.continuation lane hl).after_local_nonempty
      (entry.localSteps lane hl) follow.nonempty
    rw [hLane] at hr
    exact ⟨entry.pos lane,follow.before,entry.state lane,ends lane,
      hBound.1,hBound.2,hs.2.1,hs.2.2.1,hRegs,hr⟩

/-- Recover the actual parameter reload before either drain lookup, with the launch
pointer and physical lane index preserved from the scheduler. -/
theorem checkpointOfRead (he : X.get (g,j) = some ⟨pc,.rd a bytes⟩) :
    ∃ pos ≤ j, ∃ s ending, At s role.start (role.frame p l g) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending := by
  obtain ⟨pos,hBefore,s,ending,hLow,hHigh,hSub,hAcc,hRegs,hr⟩ :=
    role.sourceCheckpoint hp hX hCuQ hSites he
  have hIndexed : ((X.tr g).drop pos)[j-pos]? = some ⟨pc,.rd a bytes⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hBefore]
    exact he
  obtain ⟨t,_,hPath,hStep⟩ := hr.before_event hIndexed
  have hBand : role.start ≤ pc ∧ pc < role.exitFloor := by
    rcases hSites with rfl | rfl <;> cases role <;> decide
  have hBound : role.start ≤ t.pc ∧ t.pc < role.exitFloor := (estep_source_pc hStep) ▸ hBand
  have hCode : ((kernel.code.drop role.entrySpan.lo).take
      (role.entrySpan.stop-role.entrySpan.lo)).all
      (fun i => role.entrySpan.inspected ((role.frame p l g).map Prod.fst) i.op) = true := by
    simp only [frame,List.map_cons,List.map_nil]
    cases role <;> set_option maxRecDepth 100000 in decide +kernel
  have hSegments : role.entrySpan.segmentKeeps ((role.frame p l g).map Prod.fst) := by
    apply role.entrySpan.segmentKeeps_of_audit
    simp only [frame,List.map_cons,List.map_nil]
    cases role <;> set_option maxRecDepth 100000 in decide +kernel
  have hExit {a b : TState} {events : List Event}
      (h : TraceReach kernel Assumptions.all l g a events b) (ha : role.exitFloor ≤ a.pc) :
      role.exitFloor ≤ b.pc :=
    role.entrySpan.traceAboveExit h (by cases role <;> decide +kernel)
      (by cases role <;> decide) ha
  obtain ⟨u,pre,_,hSplit,hu,hScratch,hFrame,hPrefix⟩ :=
    role.entrySpan.cut hp hCode hSegments hExit hPath ⟨hLow,hHigh⟩
      (by omega) (scratchStateOfClear ⟨hSub,hAcc⟩) hRegs
      ⟨fun h => Nat.not_lt_of_ge hBound.1 h.2,hBound.2⟩
  obtain ⟨hOrder,hTail⟩ := Loader.resumeAtCut hr hBefore he hSplit hPrefix
  have hClear : ScoreScratchClear u := by
    cases role
    · exact scratchClearOfLocal (by rw [hu]; exact Flow.code_7605) rfl hScratch
    · exact scratchClearOfLocal (by rw [hu]; exact Flow.code_9083) rfl hScratch
  have hFault : u.fault = none := by
    cases hf : u.fault with
    | none => rfl
    | some f =>
      have hIndex : ((X.tr g).drop (pos+pre.length))[j-(pos+pre.length)]? =
          some ⟨pc,.rd a bytes⟩ := by
        rw [List.getElem?_drop,Nat.add_sub_of_le hOrder]
        exact he
      cases hTail.eventOfFault hf hIndex
  exact ⟨_,hOrder,u,ending,⟨hu,hClear.1,hClear.2,hFault,hFrame⟩,hTail⟩

end RowDrainRole
end PTX.Kernels.TmlFa4Fwd.Thread
