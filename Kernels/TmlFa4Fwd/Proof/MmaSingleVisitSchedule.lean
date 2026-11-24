-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaInitialPolls
public import Kernels.TmlFa4Fwd.Proof.MmaReadyIntervals
import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
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
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Flow.Code.Part035

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem singleVisitSkipCore {l : Launch} {g : Nat} :
    Seg kernel [] l g 6 2279 [(1189, b32 1)] 2534 [] := by
  intro t ht
  seg_fp ht using seg_close

/-- The decoded trip test skips the entire steady QK/PV loop when there is one visit. -/
theorem singleVisitSkipSteady {l : Launch} {g : Nat} :
    Seg kernel Assumptions.all l g 6 2279 [(1189, b32 1)] 2534 [] := by
  intro t ht
  obtain ⟨u, hu, hU⟩ := (singleVisitSkipCore (l := l) (g := g)).apply ht
  exact ⟨u, localRun (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) hu, hU⟩

private def initialScoreOp (op : Op) : Bool :=
  (!(mmaWrites op).contains 1189 && !(mmaWrites op).contains 2535) &&
    (op.isLocal || Epilogue.ordinaryEvent op) &&
    match op with
    | .bra dst _ => decide (2148 ≤ dst ∧ dst ≤ 2279)
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem initialScoreCode :
    ((kernel.code.drop 2148).take (2279 - 2148)).all (fun i => initialScoreOp i.op) = true := by
  kernel_rfl

private theorem initialScoreCodeAt {pc : Nat} {i : Instr}
    (hLo : 2148 ≤ pc) (hHi : pc < 2279) (hc : kernel.code[pc]? = some i) :
    initialScoreOp i.op = true := by
  apply List.all_eq_true.mp initialScoreCode i
  apply List.mem_of_getElem? (i := pc - 2148)
  rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]

private theorem initialScoreStep {l : Launch} {g : Nat} {s u : TState} {event : Option Event}
    (hLo : 2148 ≤ s.pc) (hHi : s.pc < 2279)
    (hShape : RoleShape s)
    {r : Nat} {value : Value} (hReg : r = 1189 ∨ r = 2535)
    (hValue : s.regs r = some value) (hs : WStep kernel Assumptions.all l g s event u) :
    (2148 ≤ u.pc ∧ u.pc ≤ 2279) ∧
      RoleShape u ∧ u.regs r = some value := by
  have hFrame := roleRegionStep 2
    (by change 2042 ≤ s.pc; omega) (by change s.pc < 2286; omega) hShape hs
  have hKeep := mmaStepReg (r := r) (by omega) (by omega)
    (fun i hc => by
      have h := initialScoreCodeAt hLo hHi hc
      simp only [initialScoreOp, Bool.and_eq_true] at h
      rcases hReg with rfl | rfl
      · simpa using h.1.1.1
      · simpa using h.1.1.2) hs
  refine ⟨?_, hFrame.2, hKeep.trans hValue⟩
  rcases hs with ⟨rfl, hTau⟩ | ⟨e, rfl, hE⟩
  · have ht : Tau kernel [] l g s u := by
      unfold Tau at hTau ⊢
      rwa [← out_eq_core (by omega) (by omega)]
    obtain ⟨i, hCode⟩ := tau_core_has_code ht
    have hOK := initialScoreCodeAt hLo hHi hCode
    simp only [initialScoreOp, Bool.and_eq_true] at hOK
    rcases tau_core_frame hCode ht with rfl | hStep
    · change 2148 ≤ s.pc + 1 ∧ s.pc + 1 ≤ 2279
      omega
    have hNext := hStep.pc
    cases hop : i.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hNext
    case bra dst uni =>
      simpa only [hop, decide_eq_true_eq, hNext] using hOK.2
    case brx => simp [hop] at hOK
    all_goals omega
  · obtain ⟨i, hc, hLocal, hFire⟩ := estep_event_source hE
    have hOK := initialScoreCodeAt hLo hHi hc
    simp only [initialScoreOp, Bool.and_eq_true, hLocal, Bool.false_or] at hOK
    have hf := Epilogue.ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g)
      (s := s) hOK.1.2
    rcases callbackFrame_fires hf hFire with hNext | hSame <;> omega

set_option maxRecDepth 100000 in
private theorem afterInitialScoreCode :
    (kernel.code.drop 2534).all (fun i => Thread.staysPastEvent 2534 i.op) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterInitialScoreSegments :
    Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | some seg => decide (2534 ≤ seg.stop)
      | none => false) = true := by
  kernel_rfl

/-- A lane with a single real trip can emit the initial QK fragments and final PV fragments,
while no continuing event in that trace occurs in the steady-loop instruction range. -/
theorem oneVisitNoSteadyEvents {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {visits : List Visit} (hWalk : Walk kernel Assumptions.all l g s es visits)
    (hPc : 2148 ≤ s.pc ∧ s.pc ≤ 2279)
    (hShape : RoleShape s)
    (hTrip : s.regs 1189 = some (b32 1))
    {e : Event} (he : e ∈ es) (hCont : ¬ Ends e) : e.pc < 2279 ∨ 2534 ≤ e.pc := by
  induction hWalk with
  | stop => cases he
  | @tau s u es visits hs hWalk ih =>
    rcases hPc.2.eq_or_lt with hEq | hLt
    · have hAt : At s 2279 [(1189, b32 1)] := by
        exact ⟨hEq, hShape.2.2 (by omega), hShape.2.1,
          Loader.walkWithContinuingEventClean (.tau hs hWalk) he hCont, hTrip, trivial⟩
      obtain ⟨v, hv, hV⟩ := singleVisitSkipSteady.apply hAt
      obtain hz | ⟨post, _, _, hTail⟩ := advanceWalkLocals hv (.tau hs hWalk)
      · simp [hz] at he
      exact .inr (Thread.eventTailEvents afterInitialScoreCode afterInitialScoreSegments
        hTail hV.1.ge e he)
    · obtain ⟨hP, hS, hT⟩ := initialScoreStep hPc.1 hLt hShape (.inl rfl) hTrip (.inl ⟨rfl, hs⟩)
      exact ih hP hS hT he
  | @ev s u actual es visits hs hWalk ih =>
    have hLt : s.pc < 2279 := by
      rcases hPc.2.eq_or_lt with hEq | hLt
      · rw [← estep_source_pc hs] at hEq
        obtain ⟨i, hc, hl, _⟩ := estep_event_source hs
        rw [← estep_source_pc hs, hEq, Flow.code_2279] at hc
        obtain rfl := Option.some.inj hc
        cases hl
      · exact hLt
    rcases List.mem_cons.mp he with rfl | he
    · exact .inl ((estep_source_pc hs).trans_lt hLt)
    · obtain ⟨hP, hS, hT⟩ := initialScoreStep hPc.1 hLt hShape (.inl rfl) hTrip (.inr ⟨_, rfl, hs⟩)
      exact ih hP hS hT he
  | @last s actual hs =>
    obtain rfl := List.mem_singleton.mp he
    obtain ⟨_, _, hf⟩ := hs
    exact (hCont (fires_none_ends hf)).elim

set_option maxRecDepth 100000 in
private theorem initialReadyCode :
    (kernel.code.drop 2148).all (fun i => Thread.staysPastEvent 2148 i.op) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem initialReadySegments :
    Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | some seg => decide (2148 ≤ seg.stop)
      | none => false) = true := by
  kernel_rfl

/-- The selected request's real trip count excludes steady QK/PV issues on a one-visit lane.
It is computed from the protected metadata before the first Q0 and K0 waits. -/
theorem selectedOneVisitNoSteadyEvents {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos batch tile : Nat} (hb : batch < p.batch) (htile : 256 * tile < p.qLength batch)
    (hTrip : trips p batch tile = 1) {t : TState}
    (ht : At t 2109 [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
      (7202, b32 (256 * (tile + 1))), (2535, b32 l.sharedBase)])
    (writes : ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∀ index e, X.get (g, index) = some e → ¬ Ends e → e.pc < 2279 ∨ 2534 ≤ e.pc := by
  have hCuQ off (ho : off ≤ 1) k (hk : k < 4) w a bytes (hw : X.MemWrites w a bytes) :
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (batch + off))).at k) :=
    hp.inputByte_unwritten writes (region := ⟨p.cuQBase, 4 * (p.batch + 1)⟩)
      (by simp [Params.inputRegions])
      (by simp only [Region.Contains, globalLoc, Loc.at, true_and]; omega) hw
  have hUsedK k (hk : k < 4) w a bytes (hw : X.MemWrites w a bytes) :
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k) :=
    hp.inputByte_unwritten writes (region := ⟨p.usedKBase, 4 * p.batch⟩)
      (by simp [Params.inputRegions])
      (by simp only [Region.Contains, globalLoc, Loc.at, true_and]; omega) hw
  obtain ⟨_, nq, nk, u, _, hWait, hU, hRun⟩ :=
    firstQKFromSelected hp hX hb htile ht hCuQ hUsedK hr
  have hShape : RoleShape u := ⟨by rw [hU.2.1]; decide, hU.2.2.1, fun _ => hU.2.1⟩
  have hCount : u.regs 1189 = some (b32 1) := by
    rw [← hTrip]
    exact hU.2.2.2.2.2.2.2.1
  obtain ⟨_, hWalk⟩ := walkFromRun hRun
  intro index e he hCont
  by_cases hEarly : e.pc < 2279
  · exact .inl hEarly
  have hPos := Thread.traceOrderOfPcFloor hX initialReadyCode initialReadySegments hWait he
    (by change 2145 < 2148; decide) (by omega)
  let first := pos + 3 + nq + 1 + nk + 1
  have hMem : e ∈ (X.tr g).drop first := by
    apply List.mem_of_getElem? (i := index - first)
    rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
    exact he
  exact oneVisitNoSteadyEvents hWalk ⟨hU.1.ge, by rw [hU.1]; decide⟩ hShape hCount hMem hCont

/-- An observed post-opening event forces the initial score window to
deliver the live trip count at its exit. -/
theorem initialScoreTripExit {l : Launch} {g n : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hPc : 2148 ≤ s.pc ∧ s.pc ≤ 2279)
    (hAt : At s s.pc [(1189, b32 n), (2535, b32 l.sharedBase)])
    {e : Event} (he : e ∈ es) (hLater : 2279 < e.pc) (hCont : ¬ Ends e) :
    ∃ u pre tail post, es = pre ++ tail ∧ e ∈ tail ∧
      (∀ event ∈ pre, 2148 ≤ event.pc ∧ event.pc < 2279) ∧
      At u 2279 [(1189, b32 n), (2535, b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g u tail post := by
  induction hWalk with
  | stop => cases he
  | @tau s u es vs hs hw ih =>
    rcases hPc.2.eq_or_lt with hExit | hMore
    · exact ⟨s, [], es, _, rfl, he, by simp, ⟨hExit, hAt.2⟩, .tau hs hw⟩
    have hShape : RoleShape s := ⟨hAt.2.1.symm ▸ Nat.zero_le _, hAt.2.2.1, fun _ => hAt.2.1⟩
    obtain ⟨hp, hS, hTrip⟩ :=
      initialScoreStep hPc.1 hMore hShape (.inl rfl) hAt.2.2.2.2.1 (.inl ⟨rfl, hs⟩)
    obtain ⟨_, _, hBase⟩ :=
      initialScoreStep hPc.1 hMore hShape (.inr rfl) hAt.2.2.2.2.2.1 (.inl ⟨rfl, hs⟩)
    have hu : At u u.pc [(1189, b32 n), (2535, b32 l.sharedBase)] :=
      ⟨rfl, hS.2.2 (by omega), hS.2.1, Loader.walkWithContinuingEventClean hw he hCont,
        hTrip, hBase, trivial⟩
    exact ih hp hu he
  | @ev s u actual es vs hs hw ih =>
    rcases hPc.2.eq_or_lt with hExit | hMore
    · exact ⟨s, [], actual :: es, _, rfl, he, by simp, ⟨hExit, hAt.2⟩, .ev hs hw⟩
    have hTail := (List.mem_cons.mp he).resolve_left (fun h => by
      rw [h, estep_source_pc hs] at hLater
      omega)
    have hShape : RoleShape s := ⟨hAt.2.1.symm ▸ Nat.zero_le _, hAt.2.2.1, fun _ => hAt.2.1⟩
    obtain ⟨hp, hS, hTrip⟩ :=
      initialScoreStep hPc.1 hMore hShape (.inl rfl) hAt.2.2.2.2.1 (.inr ⟨_, rfl, hs⟩)
    obtain ⟨_, _, hBase⟩ :=
      initialScoreStep hPc.1 hMore hShape (.inr rfl) hAt.2.2.2.2.2.1 (.inr ⟨_, rfl, hs⟩)
    have hu : At u u.pc [(1189, b32 n), (2535, b32 l.sharedBase)] :=
      ⟨rfl, hS.2.2 (by omega), hS.2.1, Loader.walkWithContinuingEventClean hw hTail hCont,
        hTrip, hBase, trivial⟩
    obtain ⟨v, pre, tail, post, hSplit, hMember, hPre, hv, hRest⟩ := ih hp hu hTail
    refine ⟨v, actual :: pre, tail, post, congrArg (actual :: ·) hSplit, hMember, ?_, hv, hRest⟩
    intro event hm
    rcases List.mem_cons.mp hm with rfl | hMem
    · rw [estep_source_pc hs]
      exact ⟨hPc.1, hMore⟩
    · exact hPre event hMem
  | last hs =>
    obtain rfl := List.mem_singleton.mp he
    obtain ⟨_, _, hf⟩ := hs
    exact (hCont (fires_none_ends hf)).elim

private theorem signed32Trip {n : Nat} (hn : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left hn]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem prepareSteadyAddress {l : Launch} {g n : Nat} :
    Seg kernel [] l g 1 2285 [(1189, b32 n), (2535, b32 l.sharedBase)]
      2286 [(1189, b32 n)] := by
  intro t ht
  seg_fp ht using rfl

/-- A selected request with at least two trips initializes the actual signed
steady counter from the trip register after the first score banks. -/
theorem selectedTripInitSteady {l : Launch} {g n : Nat} (hn : 2 ≤ n) (hN : n < 2 ^ 31) :
    Seg kernel Assumptions.all l g 12 2279 [(1189, b32 n), (2535, b32 l.sharedBase)]
      2291 [(7204, wideCounterWord n)] := by
  have hn32 : n < 2 ^ 32 := by omega
  have hLower : ¬ ((n : Int) < 2) := by omega
  have hTwo : toSigned 32 (truncBits 32 (BitVec.ofInt 64 2)) = 2 := rfl
  have hFirst : Seg kernel [] l g 5 2279 [(1189, b32 n), (2535, b32 l.sharedBase)]
      2284 [(388, .pred false), (1189, b32 n), (2535, b32 l.sharedBase)] := by
    intro t ht
    seg_fp ht using
      simp only [truncBits_ofNat hn32 (by decide), signed32Trip hN,
        compare, Option.getD_some, hTwo, hLower, decide_false]
  intro t ht
  obtain ⟨pred, hRun, hPred⟩ := hFirst t ht
  obtain ⟨u, hBranch, hu⟩ :=
    run_bra (K := kernel) (A := []) (L := l) (g := g)
      Flow.code_2284 false hPred hPred.2.2.2.2.1 (by simp)
  have hu' : At u 2285 [(1189, b32 n), (2535, b32 l.sharedBase)] := by
    at_select hu
  obtain ⟨v, hPlus, hv⟩ := prepareSteadyAddress (g := g) u hu'
  obtain ⟨w, hNeg, hw⟩ := initializeCounter (l := l) (g := g) (n := n) (by omega) hn32 v hv
  have hLocal := localRun (by decide : 1904 ≤ 2279) (by decide : 2279 + 6 ≤ 2768)
    ht.1 (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp hRun hBranch)
  have hBody := localRun (by decide : 1904 ≤ 2285) (by decide : 2285 + 6 ≤ 2768)
    hu'.1 (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp hPlus hNeg)
  refine ⟨w, run_comp hLocal hBody, ?_⟩
  rw [wideCounterWord, ite_eq_right (by omega)]
  exact hw

private theorem walkRun {l : Launch} {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (h : Walk kernel Assumptions.all l g s es vs) :
    ∃ o, Run kernel Assumptions.all l g s es o := by
  induction h with
  | stop => exact ⟨some _, .nil _⟩
  | tau ht _ ih =>
    obtain ⟨_, hTail⟩ := ih
    cases hTail with
    | nil => exact ⟨some _, .nil _⟩
    | step hLocal he hr => exact ⟨_, .step (.head ht hLocal) he hr⟩
    | last hLocal he => exact ⟨none, .last (.head ht hLocal) he⟩
  | ev he _ ih => obtain ⟨r, hr⟩ := ih; exact ⟨r, .step .refl he hr⟩
  | last he => exact ⟨none, .last .refl he⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g pos index batch tile : Nat}
    (hb : batch < p.batch) (htile : 256 * tile < p.qLength batch) (hTrips : 2 ≤ trips p batch tile)
    {t : TState} {ending : Option TState}
    (ht : At t 2109 [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
      (7202, b32 (256 * (tile + 1))), (2535, b32 l.sharedBase)])
    (writes : ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending) {event : Event}
    (he : X.get (g, index) = some event) (hReaches : ending = none ∨ pos ≤ index)
include hp hX hb htile hTrips ht writes hr he hReaches

/-- The actual selected-request reads set the steady counter before a
demanded output event. The cut retains the exact suffix of the issuing trace. -/
theorem selectedSteadyCursorAndInitialReady (hLater : 2279 < event.pc) (hCont : ¬ Ends event) :
    ∃ start u out, start ≤ index ∧ At u 2291 [(7204, wideCounterWord (trips p batch tile))] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop start) out ∧
      (((X.tr g).take start).filterMap readyEvent).length = 1 := by
  have hCuQ off (ho : off ≤ 1) k (hk : k < 4) w a bytes (hw : X.MemWrites w a bytes) :
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (batch + off))).at k) :=
    hp.inputByte_unwritten writes (region := ⟨p.cuQBase, 4 * (p.batch + 1)⟩)
      (by simp [Params.inputRegions])
      (by simp only [Region.Contains, globalLoc, Loc.at, true_and]; omega) hw
  have hUsedK k (hk : k < 4) w a bytes (hw : X.MemWrites w a bytes) :
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k) :=
    hp.inputByte_unwritten writes (region := ⟨p.usedKBase, 4 * p.batch⟩)
      (by simp [Params.inputRegions])
      (by simp only [Region.Contains, globalLoc, Loc.at, true_and]; omega) hw
  have hDemand : Loader.PrefixDemand X g pos 2145 ending :=
    hReaches.imp_right (fun hPos => ⟨index, event, hPos, by omega, he⟩)
  obtain ⟨_, nq, nk, u, _, hWait, hu, hRun⟩ :=
    firstQKFromSelectedInPrefix hp hX hb htile ht hCuQ hUsedK hr hDemand
  have hOrder := Thread.traceOrderOfPcFloor hX initialReadyCode initialReadySegments hWait he
    (by change 2145 < 2148; decide) (by omega)
  let key := pos + 3 + nq + 1 + nk
  let first := key + 1
  have hEvent : ((X.tr g).drop first)[index - first]? = some event := by
    rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
    exact he
  obtain ⟨visits, hWalk⟩ := walkFromRun hRun
  have hOpening : At u u.pc [(1189, b32 (trips p batch tile)), (2535, b32 l.sharedBase)] :=
    ⟨rfl, (by at_select hu :
      At u 2148 [(1189, b32 (trips p batch tile)), (2535, b32 l.sharedBase)]).2⟩
  obtain ⟨v, pre, tail, post, hSplit, hMember, hPre, hv, hRest⟩ :=
    initialScoreTripExit hWalk ⟨hu.1.ge, by rw [hu.1]; decide⟩ hOpening
      (List.mem_of_getElem? hEvent) hLater hCont
  have hFirst : first + pre.length ≤ index := by
    by_contra! hBad
    rw [hSplit, List.getElem?_append_left (by omega)] at hEvent
    have hPc := (hPre event (List.mem_of_getElem? hEvent)).2
    omega
  have hBound : trips p batch tile < 2 ^ 31 := by
    have h := (trips_bounds hp hb htile).2.1
    have hKeys := (hp.lengths batch hb).2.2
    change trips p batch tile ≤ (p.kLength batch + 127) / 128 at h
    omega
  obtain ⟨z, hLocals, hz⟩ := selectedTripInitSteady hTrips hBound v hv
  obtain ⟨out, hSuffix⟩ := walkRun hRest
  have hDrop : (X.tr g).drop (first + pre.length) = tail := by
    rw [← List.drop_drop, hSplit, List.drop_append_length]
  refine ⟨first + pre.length, z, out, hFirst, hz,
    hDrop.symm ▸ hSuffix.after_local_nonempty (run_rtg hLocals) (List.ne_nil_of_mem hMember), ?_⟩
  have hw : Prologue.warpIndex l g = 12 := by
    have hRole := roleBodyPcOfEvent hp hX hWait
      (show 173 < 2145 by decide) (show 2145 ∉ registerHintSites by decide)
    change roleBodyPc (Prologue.warpIndex l g) 2145 at hRole
    unfold roleBodyPc at hRole
    rcases hRole with hExit | hBody
    · omega
    · split_ifs at hBody <;> omega
  have hPoll : Thread.Mma.ReadyPoll l X g key 0 0 true .cta := ⟨_, hWait, rfl⟩
  obtain ⟨site,hGet,hUse⟩ := hPoll.useSite hp hX hw
  have hSite : site = 2145 := congrArg Event.pc (Option.some.inj (hGet.symm.trans hWait))
  have hBefore : (((X.tr g).take key).filterMap readyEvent).length = 0 := by
    simpa [hSite, ReadyUseSite, readyHead] using hUse
  have hKey : (X.tr g)[key]? = some
      ⟨2145, .wait ⟨.shared, g/l.block, l.sharedBase+32⟩ 0 true true .cta⟩ := hWait
  have hFirstReady : (((X.tr g).take first).filterMap readyEvent).length = 1 := by
    rw [show first = key + 1 from rfl, List.take_add_one, hKey]
    simp [readyEvent, show (List.finRange 4).any (fun i => readyHead i == 2145) = true by decide,
      hBefore]
  have hNoMore : pre.filterMap readyEvent = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    rintro ⟨site, kind⟩ hm
    obtain ⟨hLo,hHi⟩ := hPre ⟨site,kind⟩ hm
    have hNone : (List.finRange 4).any (fun i => readyHead i == site) = false := by
      by_contra hYes
      obtain ⟨i,_,hi⟩ := List.any_eq_true.mp (Bool.eq_true_of_ne_false hYes)
      have hPc := beq_iff_eq.mp hi
      have hGap : readyHead i < 2148 ∨ 2279 ≤ readyHead i :=
        (by decide : ∀ i, readyHead i < 2148 ∨ 2279 ≤ readyHead i) i
      change 2148 ≤ site at hLo
      change site < 2279 at hHi
      omega
    cases kind <;> try rfl
    case wait loc parity ok acquire scope => cases ok <;> simp [readyEvent,hNone]
  rw [List.take_add, hSplit, List.take_left, List.filterMap_append, hNoMore, List.append_nil]
  exact hFirstReady

/-- Recover the initialized steady-loop state from its actual selected request. -/
theorem selectedSteadyCursorInPrefix (hLater : 2279 < event.pc) (hCont : ¬ Ends event) :
    ∃ start u out, start ≤ index ∧ At u 2291 [(7204, wideCounterWord (trips p batch tile))] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop start) out := by
  obtain ⟨start,u,out,hStart,hAt,hRun,_⟩ :=
    selectedSteadyCursorAndInitialReady hp hX hb htile hTrips ht writes hr he hReaches hLater hCont
  exact ⟨start,u,out,hStart,hAt,hRun⟩
end

end PTX.Kernels.TmlFa4Fwd.Mma
