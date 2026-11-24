-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyGuard
public import Kernels.TmlFa4Fwd.Proof.LoaderCopyLaneFrame
public import Kernels.TmlFa4Fwd.Proof.LoaderObservedCut
public import Kernels.TmlFa4Fwd.Proof.LoaderRingMbarAddress
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
import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
public import Kernels.TmlFa4Fwd.Proof.LoaderPacketSites
import Kernels.TmlFa4Fwd.Proof.GlobalWrites
import Kernels.TmlFa4Fwd.Flow.Code.Part005
import Kernels.TmlFa4Fwd.Flow.Code.Part008
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Kernels.TmlFa4Fwd.Flow.Code.Part025
import Kernels.TmlFa4Fwd.Flow.Code.Part029

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.AsyncCopy Epilogue Prologue Mma Softmax

noncomputable section

/-- The first instruction of a recurring packet's paired barrier address calculation. -/
def reuseEntry (site : Fin 4) : Nat := (recurringEmptyWait site).pc - 3

/-- The arrival that closes this recurring packet. -/
def reuseArrival (site : Fin 4) : Nat := copyCommitPc (recurringPacketSite site) + 1

/-- The start of the address calculation used for each recurring publication. -/
def recurringSelectionStart : Fin 4 → Nat
  | 0 => 957
  | 1 => 1203
  | 2 => 1427
  | 3 => 1451

private inductive ReuseCutpoint
  | barrier | copy | seed | priming | packet | steadySwizzle | primingPacket | primingSwizzle
  | recurringCopyEntry | primingCopyEntry

private def cutPc (cut : ReuseCutpoint) (site : Fin 4) : Nat :=
  match cut with
  | .barrier => reuseEntry site
  | .copy => packetPlanePc (recurringPacketSite site) 15 true
  | .seed => 909
  | .steadySwizzle => if site = 3 then 1451 else reuseEntry site
  | .priming => if site = 0 then 515 else 780
  | .packet => copyPacketFirst (recurringPacketSite site)
  | .primingPacket => copyPacketFirst (if site = 0 then 0 else 1)
  | .primingSwizzle | .primingCopyEntry => 356
  | .recurringCopyEntry => recurringSelectionStart site

private def cutTarget (cut : ReuseCutpoint) (site : Fin 4) : Nat :=
  match cut with
  | .priming | .primingPacket | .primingSwizzle => if site = 0 then 674 else 904
  | .primingCopyEntry => copyPacketFirst (if site = 0 then 0 else 1)
  | .recurringCopyEntry => copyPacketFirst (recurringPacketSite site)
  | _ => reuseArrival site

private def cutStop (cut : ReuseCutpoint) (site : Fin 4) : Nat :=
  match cut with
  | .seed => 1744
  | .primingCopyEntry => copyCommitPc (if site = 0 then 0 else 1)
  | .recurringCopyEntry => copyCommitPc (recurringPacketSite site)
  | _ => cutTarget cut site + 1

private theorem reuseBounds (cut : ReuseCutpoint) (site : Fin 4) :
    179 < cutPc cut site ∧ cutPc cut site < cutTarget cut site ∧
      cutTarget cut site < cutStop cut site ∧ cutStop cut site ≤ 1901 := by
  cases cut <;> fin_cases site <;> decide

private def reuseWindow (cut : ReuseCutpoint) (site : Fin 4) (pc : Nat) : Bool :=
  decide (cutPc cut site ≤ pc ∧ pc < cutStop cut site)

private def reuseBranches (cut : ReuseCutpoint) (site : Fin 4) (pc : Nat) (op : Op) : Bool :=
  match op with
  | .bra dest _ =>
    !reuseWindow cut site dest || reuseWindow cut site pc || dest == cutPc cut site
  | .brx .. => false
  | _ => true

private theorem reuseCode (cut : ReuseCutpoint) (site : Fin 4) {pc : Nat} {instr : Instr}
    (hLo : 174 ≤ pc) (hHi : pc < 1901) (hc : kernel.code[pc]? = some instr) :
    reuseBranches cut site pc instr.op = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hCode : code.all (fun (ins, atPc) => reuseBranches cut site atPc ins.op) = true := by
    cases cut <;> fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hMem : (instr, pc) ∈ code := by
    apply List.mem_of_getElem? (i := pc - 174)
    dsimp [code]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hLo, hc]
    rfl
  exact List.all_eq_true.mp hCode _ hMem

private theorem entersReuseWindow {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (cut : ReuseCutpoint) (site : Fin 4) (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (h : WStep kernel Assumptions.all l g s ev u) (hIn : reuseWindow cut site u.pc = true) :
    reuseWindow cut site s.pc = true ∨ u.pc = cutPc cut site := by
  have fall (hPc : u.pc = s.pc + 1) :
      reuseWindow cut site s.pc = true ∨ u.pc = cutPc cut site := by
    simp only [reuseWindow, decide_eq_true_eq] at hIn ⊢
    omega
  rcases h with ⟨_, hTau⟩ | ⟨e, _, hEvent⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at *
      rwa [← loaderOutCore (by omega) (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code hCore
    have hCode := reuseCode cut site hLo hHi hc
    rcases tau_core_frame hc hCore with rfl | hFrame
    · exact fall rfl
    have hPc := hFrame.pc
    cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc
    case bra dest uniform =>
      rw [hPc] at hIn ⊢
      simpa [reuseBranches, hop, hIn] using hCode
    case brx => simp [reuseBranches, hop] at hCode
    all_goals exact fall hPc
  · have hCore : EStep kernel [] l g s e (some u) := by
      obtain ⟨tmpl, ho, hf⟩ := hEvent
      exact ⟨tmpl, by rwa [← loaderOutCore (by omega) (by omega)], hf⟩
    rcases (estep_return_pc hCore (fun _ _ _ ht => execLocal_frame ht)).2 with hPc | hPc
    · exact .inl (hPc ▸ hIn)
    · exact fall hPc

private def reuseEvents (cut : ReuseCutpoint) (site : Fin 4) (visits : List Visit) : List Event :=
  loaderSliceEvents (cutPc cut site) (cutStop cut site) visits

private theorem reuseEventsCons {l : Launch} {g : Nat} {s : TState} {ev : Option Event}
    {vs : List Visit} (cut : ReuseCutpoint) (site : Fin 4)
    (hIn : reuseWindow cut site s.pc = true) :
    reuseEvents cut site (visit kernel l g s ev :: vs) = ev.toList ++ reuseEvents cut site vs := by
  cases ev <;> simp [reuseEvents, loaderSliceEvents, visit, reuseWindow, Bool.and_eq_true] at *
  all_goals simp_all

/-- A walk with a continuing event cannot start in a faulted state. -/
theorem walkWithContinuingEventClean {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} {e : Event}
    (hw : Walk kernel Assumptions.all l g s es vs) (he : e ∈ es)
    (hContinue : ¬ Ends e) : s.fault = none := by
  cases hf : s.fault
  · rfl
  cases hw with
  | stop => cases he
  | tau ht _ => simp [Tau, out, hf] at ht
  | ev hStep _ =>
    obtain ⟨tmpl, ho, hFire⟩ := hStep
    simp only [out, hf, Out.ev.injEq] at ho
    subst tmpl
    cases hFire.2
  | last hStep =>
    obtain rfl := List.mem_singleton.mp he
    obtain ⟨_, _, hFire⟩ := hStep
    exact (hContinue (fires_none_ends hFire)).elim

/-- A walk containing a publication cannot start in a faulted state. -/
theorem walkWithArrivalClean {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} {e : Event} {loc : Loc}
    (hw : Walk kernel Assumptions.all l g s es vs) (he : e ∈ es)
    (hk : e.kind = .asyncArrive loc true) : s.fault = none :=
  walkWithContinuingEventClean hw he (by simp [Ends, hk])

private def reuseCut (cut : ReuseCutpoint) (site : Fin 4) (l : Launch) (g : Nat)
    (warp : Fin 2) (es : List Event) (index : Nat) (e : Event) : Prop :=
  ∃ (n : Nat) (t : TState) (tail : List Visit), n ≤ index ∧ t.pc = cutPc cut site ∧
    (LoaderRingFrame l warp t ∧ LoaderCopyLaneFrame l g t) ∧
    Walk kernel Assumptions.all l g t (es.drop n) tail ∧
    (reuseEvents cut site tail)[index - n]? = some e

private theorem takeReuseCut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (warp : Fin 2) (cut : ReuseCutpoint) (site : Fin 4)
    {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : 174 ≤ s.pc ∧ s.pc ≤ 1901) (hFrame : LoaderRingFrame l warp s ∧ LoaderCopyLaneFrame l g s)
    {index : Nat} {e : Event} (hContinue : ¬ Ends e)
    (hSource : reuseWindow cut site e.pc = true) (he : es[index]? = some e) :
    reuseCut cut site l g warp es index e ∨
      (reuseWindow cut site s.pc = true ∧ (reuseEvents cut site vs)[index]? = some e) := by
  have hBounds := reuseBounds cut site
  have hRange := of_decide_eq_true hSource
  have step {s u : TState} {ev : Option Event} {tail : List Event} {rest : List Visit}
      (hW : WStep kernel Assumptions.all l g s ev u)
      (hTail : Walk kernel Assumptions.all l g u tail rest)
      (hs : 174 ≤ s.pc ∧ s.pc ≤ 1901) (hr : LoaderRingFrame l warp s ∧ LoaderCopyLaneFrame l g s)
      {j : Nat} (hGet : tail[j]? = some e)
      (ih : (174 ≤ u.pc ∧ u.pc ≤ 1901) → (LoaderRingFrame l warp u ∧ LoaderCopyLaneFrame l g u) →
        reuseCut cut site l g warp tail j e ∨
          (reuseWindow cut site u.pc = true ∧ (reuseEvents cut site rest)[j]? = some e)) :
      reuseCut cut site l g warp (ev.toList ++ tail) (ev.toList.length + j) e ∨
        (reuseWindow cut site s.pc = true ∧
          (reuseEvents cut site (visit kernel l g s ev :: rest))[ev.toList.length + j]? =
            some e) := by
    have hWhole : Walk kernel Assumptions.all l g s (ev.toList ++ tail)
        (visit kernel l g s ev :: rest) := by
      rcases hW with ⟨rfl, ht⟩ | ⟨event, rfl, ht⟩
      · exact .tau ht hTail
      · exact .ev ht hTail
    by_cases hExit : s.pc = 1901
    · have hMem : e ∈ ev.toList ++ tail := List.mem_append_right _ (List.mem_of_getElem? hGet)
      have hClean := walkWithContinuingEventClean hWhole hMem hContinue
      have hAt := pipelineAtCut hExit hr.1.1 hr.1.2.1 hClean ⟨_, Flow.code_1901, rfl⟩
      have hEnd := loaderTailEventPcs warp hAt hWhole e hMem
      omega
    obtain ⟨hLo, hHi, hRing⟩ := loaderRingStep hp hs.1 (by omega) hr.1 hW
    have hNext := And.intro hRing (loaderCopyLaneFrameStep hp hs.1 (by omega) hr.1.1 hr.2 hW)
    rcases ih ⟨hLo, hHi⟩ hNext with ⟨n, t, trail, hn, hPc, hF, hWalk, hSaw⟩ | ⟨hIn, hSaw⟩
    · refine .inl ⟨ev.toList.length + n, t, trail, by omega, hPc, hF, ?_, ?_⟩
      · rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
          Nat.add_sub_cancel_left]
        exact hWalk
      · simpa only [Nat.add_sub_add_left] using hSaw
    · rcases entersReuseWindow cut site hs.1 (by omega) hW hIn with hInside | hEntry
      · refine .inr ⟨hInside, ?_⟩
        rw [reuseEventsCons cut site hInside, List.getElem?_append_right (by omega),
          Nat.add_sub_cancel_left]
        exact hSaw
      · refine .inl ⟨ev.toList.length, u, rest, by omega, hEntry, hNext, ?_, ?_⟩
        · simpa using hTail
        · simpa only [Nat.add_sub_cancel_left] using hSaw
  induction hw generalizing index with
  | stop => simp at he
  | tau ht hTail ih =>
    simpa using step (.inl ⟨rfl, ht⟩) hTail hPc hFrame he (ih · · he)
  | @ev t u event tail rest hStep hTail ih =>
    cases index with
    | zero =>
      obtain rfl := Option.some.inj he
      have hIn : reuseWindow cut site t.pc = true := by
        exact estep_source_pc hStep ▸ hSource
      exact .inr ⟨hIn, by rw [reuseEventsCons cut site hIn]; rfl⟩
    | succ index =>
      have hGet : tail[index]? = some e := he
      simpa only [Nat.add_comm, Option.toList_some, List.length_singleton,
        List.singleton_append] using step (.inr ⟨_, rfl, hStep⟩) hTail hPc hFrame hGet
        (ih · · hGet)
  | last hStep =>
    cases index with
    | zero =>
      obtain rfl := Option.some.inj he
      obtain ⟨_, _, hFire⟩ := hStep
      exact (hContinue (fires_none_ends hFire)).elim
    | succ index => simp at he

private theorem reuseEntryCode (site : Fin 4) :
    ∃ ins, kernel.code[reuseEntry site]? = some ins ∧ ins.op.isLocal = true := by
  fin_cases site
  · exact ⟨_, Flow.code_957, rfl⟩
  · exact ⟨_, Flow.code_1203, rfl⟩
  · exact ⟨_, Flow.code_1427, rfl⟩
  · exact ⟨_, Flow.code_1608, rfl⟩

private theorem reuseStageFact (site : Fin 4) :
    ∃ f ∈ loaderRingFacts,
      f.value = .slot (recurringStageInputs site).1 ∧ f.active (reuseEntry site) := by
  fin_cases site
  · exact ⟨⟨.slot 7179, 372, 1869, [371, 910, 914, 1345, 1738]⟩, by decide, rfl, by decide⟩
  · exact ⟨⟨.slot 1139, 1141, 1343, [1140]⟩, by decide, rfl, by decide⟩
  · exact ⟨⟨.slot 7179, 372, 1869, [371, 910, 914, 1345, 1738]⟩, by decide, rfl, by decide⟩
  · exact ⟨⟨.slot 1170, 1606, 1736, [1605]⟩, by decide, rfl, by decide⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem actualIndexedLoaderFrame (cut : ReuseCutpoint) (site : Fin 4) {g index : Nat}
    {e : Event} (he : X.get (g, index) = some e) (hContinue : ¬ Ends e)
    (hIn : reuseWindow cut site e.pc = true) :
    ∃ (warp : Fin 2) (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ s.pc = cutPc cut site ∧
      (LoaderRingFrame l warp s ∧ LoaderCopyLaneFrame l g s) ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents (cutPc cut site) (cutStop cut site) vs)[index - start]? =
        some e := by
  have hBounds := reuseBounds cut site
  have hRange := of_decide_eq_true hIn
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hLate : 173 < e.pc := by omega
  have hWarp : 14 ≤ warpIndex l g := by
    rcases roleBodyPcOfEvent hp hX he hLate hHint with h | h
    · omega
    · split_ifs at h <;> omega
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWord : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hWarp
  have hg := event_thread_lt hX he
  obtain ⟨t, o, hIndex, hAt, hTid, hr⟩ :=
    nonzeroCommonPrefixOfLateEventWithTid hp hX hg (by omega : 0 < warpIndex l g) he hLate
  let pos := 5
  have hRoot : At t 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] :=
    hAt.mono ⟨hAt.2.2.2.2.2.1, hWord.symm ▸ hAt.2.2.2.2.1, trivial⟩
  obtain ⟨visits, hWalk⟩ := walkFromRun hr
  have hPos : pos ≤ index := hIndex
  have hGet : ((X.tr g).drop pos)[index - pos]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hPos]
    exact he
  rcases takeReuseCut hp warp cut site hWalk ⟨by rw [hAt.1], by rw [hAt.1]; decide⟩
      ⟨loaderRingFrameAtDispatch hRoot, loaderCopyLaneFrameAtDispatch hAt.1 hTid⟩
      hContinue hIn hGet with
    ⟨n, s, tail, hn, hPc, hFrame, hs, hSaw⟩ | ⟨hIn, _⟩
  · exact ⟨warp, pos + n, s, tail, by omega, hPc, hFrame, by simpa only [List.drop_drop] using hs,
      by simpa only [reuseEvents, show index - (pos + n) = index - pos - n by omega] using hSaw⟩
  · rw [hAt.1, reuseWindow] at hIn
    have h := of_decide_eq_true hIn
    omega

private theorem actualReuseFrame (cut : ReuseCutpoint) (site : Fin 4) {g index : Nat} {loc : Loc}
    (he : X.get (g, index) = some ⟨cutTarget cut site, .asyncArrive loc true⟩) :
    ∃ (warp : Fin 2) (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ s.pc = cutPc cut site ∧
      (LoaderRingFrame l warp s ∧ LoaderCopyLaneFrame l g s) ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents (cutPc cut site) (cutStop cut site) vs)[index - start]? =
        some ⟨cutTarget cut site, .asyncArrive loc true⟩ := by
  have hBounds := reuseBounds cut site
  exact actualIndexedLoaderFrame hp hX cut site he (by simp [Ends])
    (decide_eq_true ⟨hBounds.2.1.le, hBounds.2.2.1⟩)

private theorem actualBarrierCheckpoint (site : Fin 4) {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e) (hContinue : ¬ Ends e)
    (hSite : reuseEntry site ≤ e.pc ∧ e.pc < reuseArrival site + 1) :
    ∃ (stage : Fin 3) (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ At s (reuseEntry site)
        [((recurringStageInputs site).1, b32 stage), (2535, b32 l.sharedBase)] ∧
      LoaderCopyLaneFrame l g s ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents (reuseEntry site) (reuseArrival site + 1) vs)[index - start]? =
        some e := by
  obtain ⟨warp, start, s, tail, hStart, hPc, ⟨hFrame, hLane⟩, hs, hSaw⟩ :=
    actualIndexedLoaderFrame hp hX .barrier site he hContinue (decide_eq_true hSite)
  have hMem : e ∈ (X.tr g).drop start := by
    rw [hs.events]
    obtain ⟨v, hv, hEv⟩ := List.mem_filterMap.mp (List.mem_of_getElem? hSaw)
    exact List.mem_filterMap.mpr ⟨v, List.takeWhile_subset _ hv, hEv⟩
  have hClean := walkWithContinuingEventClean hs hMem hContinue
  have hAt := pipelineAtCut hPc hFrame.1 hFrame.2.1 hClean (reuseEntryCode site)
  obtain ⟨f, hFact, hValue, hLive⟩ := reuseStageFact site
  have hSlot := hFrame.2.2 f hFact (hPc.symm ▸ hLive)
  rw [hValue] at hSlot
  obtain ⟨stage, hStage, _⟩ := hSlot
  exact ⟨stage, start, s, tail, hStart, hAt.mono ⟨hStage, hAt.2.2.2.2.1, trivial⟩, hLane, hs, hSaw⟩

/-- Each actual recurring publication has a precisely indexed suffix at the start of
its paired barrier calculations. All events from that checkpoint through the specified
publication belong to the same packet. -/
theorem actualReuseCheckpointWithLane (site : Fin 4) {g index : Nat} {loc : Loc}
    (he : X.get (g, index) = some ⟨reuseArrival site, .asyncArrive loc true⟩) :
    ∃ (stage : Fin 3) (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ At s (reuseEntry site)
        [((recurringStageInputs site).1, b32 stage), (2535, b32 l.sharedBase)] ∧
      LoaderCopyLaneFrame l g s ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents (reuseEntry site) (reuseArrival site + 1) vs)[index - start]? =
        some ⟨reuseArrival site, .asyncArrive loc true⟩ := by
  apply actualBarrierCheckpoint hp hX site he (by simp [Ends])
  have hBounds := reuseBounds .barrier site
  exact ⟨hBounds.2.1.le, hBounds.2.2.1⟩

/-- Each actual recurring publication has a precisely indexed suffix at the start of
its paired barrier calculations. All events from that checkpoint through the specified
publication belong to the same packet. -/
theorem actualReuseCheckpoint (site : Fin 4) {g index : Nat} {loc : Loc}
    (he : X.get (g, index) = some ⟨reuseArrival site, .asyncArrive loc true⟩) :
    ∃ (stage : Fin 3) (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ At s (reuseEntry site)
        [((recurringStageInputs site).1, b32 stage), (2535, b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents (reuseEntry site) (reuseArrival site + 1) vs)[index - start]? =
        some ⟨reuseArrival site, .asyncArrive loc true⟩ := by
  obtain ⟨stage, start, s, vs, hi, hs, _, hw, hSeen⟩ := actualReuseCheckpointWithLane hp hX site he
  exact ⟨stage, start, s, vs, hi, hs, hw, hSeen⟩

omit hp hX in
private theorem sliceContainsEvent {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} {e : Event} {lower stop : Nat}
    (hw : Walk kernel Assumptions.all l g s es vs) (he : e ∈ loaderSliceEvents lower stop vs) :
    e ∈ es := by
  rw [hw.events]
  obtain ⟨v, hv, he⟩ := List.mem_filterMap.mp he
  exact List.mem_filterMap.mpr ⟨v, List.takeWhile_subset _ hv, he⟩

/-- A steady V publication has an actual suffix beginning at its paired K packet's
shared-vector swizzle, including the current K stage and the lane-column frame. -/
theorem actualSteadyVSwizzleCheckpoint {g index : Nat} {loc : Loc}
    (he : X.get (g, index) = some ⟨reuseArrival 3, .asyncArrive loc true⟩) :
    ∃ (stage : Fin 3) (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ At s 1451 [(7179, b32 stage), (2535, b32 l.sharedBase)] ∧
      LoaderCopyLaneFrame l g s ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents 1451 (reuseArrival 3 + 1) vs)[index - start]? =
        some ⟨reuseArrival 3, .asyncArrive loc true⟩ := by
  obtain ⟨warp, start, s, tail, hStart, hPc, ⟨hFrame, hLane⟩, hs, hSaw⟩ :=
    actualReuseFrame hp hX .steadySwizzle 3 he
  have ht : s.pc = 1451 := hPc
  have hi : ⟨reuseArrival 3, .asyncArrive loc true⟩ ∈ (X.tr g).drop start :=
    sliceContainsEvent hs (List.mem_of_getElem? hSaw)
  have hAt := pipelineAtCut ht hFrame.1 hFrame.2.1 (walkWithArrivalClean hs hi rfl)
    ⟨_, Flow.code_1451, rfl⟩
  let f : RingFact := ⟨.slot 7179, 372, 1869, [371, 910, 914, 1345, 1738]⟩
  have hf : f.active 1451 := by decide
  obtain ⟨stage, hStage, _⟩ := hFrame.2.2 f (by decide) (ht.symm ▸ hf)
  exact ⟨stage, start, s, tail, hStart, hAt.mono ⟨hStage, hAt.2.2.2.2.1, trivial⟩, hLane, hs, hSaw⟩

/-- Every actual recurring publication has an indexed suffix from the initial cursor write.
The visit slice retains the same publication index up to the drain boundary. -/
theorem actualEmptySeedPrefix (site : Fin 4) {g index : Nat} {loc : Loc}
    (he : X.get (g, index) = some ⟨reuseArrival site, .asyncArrive loc true⟩) :
    ∃ (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ At s 909 [(2535, b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents 909 1744 vs)[index - start]? =
        some ⟨reuseArrival site, .asyncArrive loc true⟩ := by
  obtain ⟨warp, start, s, tail, hStart, hPc, ⟨hFrame, _⟩, hs, hSaw⟩ :=
    actualReuseFrame hp hX .seed site he
  have hMem := sliceContainsEvent hs (List.mem_of_getElem? hSaw)
  have hClean := walkWithArrivalClean hs hMem rfl
  have hAt := pipelineAtCut hPc hFrame.1 hFrame.2.1 hClean ⟨_, Flow.code_909, rfl⟩
  exact ⟨start, s, tail, hStart, hAt.mono ⟨hAt.2.2.2.2.1, trivial⟩, hs, hSaw⟩

/-- The checked suffix for either priming publication starts at its fixed empty wait prep. -/
theorem actualPrimingEmptyPrefix (slot : Fin 2) {g index : Nat} {loc : Loc}
    (he : X.get (g, index) = some ⟨(if slot = 0 then 674 else 904), .asyncArrive loc true⟩) :
    ∃ (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ At s (if slot = 0 then 515 else 780) [(2535, b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents (if slot = 0 then 515 else 780) (if slot = 0 then 675 else 905)
        vs)[index - start]? = some ⟨(if slot = 0 then 674 else 904), .asyncArrive loc true⟩ := by
  let site : Fin 4 := ⟨slot, by have := slot.isLt; omega⟩
  have hCond : (site = 0) = (slot = 0) := by fin_cases slot <;> decide
  have hTarget : cutTarget .priming site = (if slot = 0 then 674 else 904) := by
    simp only [cutTarget, hCond]
  have hPc : cutPc .priming site = (if slot = 0 then 515 else 780) := by
    simp only [cutPc, hCond]
  have hStop : cutStop .priming site = (if slot = 0 then 675 else 905) := by
    fin_cases slot <;> rfl
  have hCode : ∃ ins, kernel.code[cutPc .priming site]? = some ins ∧ ins.op.isLocal = true := by
    rw [hPc]
    fin_cases slot
    · exact ⟨_, Flow.code_515, rfl⟩
    · exact ⟨_, Flow.code_780, rfl⟩
  obtain ⟨warp, start, s, tail, hStart, ht, ⟨hFrame, _⟩, hs, hSaw⟩ :=
    actualReuseFrame hp hX .priming site (hTarget.symm ▸ he)
  have hMem := sliceContainsEvent hs (List.mem_of_getElem? hSaw)
  have hClean := walkWithArrivalClean hs hMem rfl
  have hAt := pipelineAtCut ht hFrame.1 hFrame.2.1 hClean hCode
  rw [hPc, hStop, hTarget] at hSaw
  rw [hPc] at hAt
  exact ⟨start, s, tail, hStart, hAt.mono ⟨hAt.2.2.2.2.1, trivial⟩, hs, hSaw⟩

omit hp hX in
/-- The decoded packet corresponding to one of the two priming slots. -/
def primingPacketSite (slot : Fin 2) : Fin 6 :=
  ⟨slot, by have := slot.isLt; omega⟩

/-- Each actual priming publication has an indexed suffix starting at the
common K/V swizzle, with the true CTA-local lane and shared base. -/
theorem actualPrimingSwizzleCheckpoint (slot : Fin 2) {g index : Nat} {loc : Loc}
    (he : X.get (g, index) =
      some ⟨copyCommitPc (primingPacketSite slot) + 1, .asyncArrive loc true⟩) :
    ∃ (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ At s 356 [(1061, b32 (g % l.block)), (2535, b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents 356 (copyCommitPc (primingPacketSite slot) + 2) vs)[index - start]? =
        some ⟨copyCommitPc (primingPacketSite slot) + 1, .asyncArrive loc true⟩ := by
  let site : Fin 4 := ⟨slot, by have := slot.isLt; omega⟩
  have hTarget : cutTarget .primingSwizzle site = copyCommitPc (primingPacketSite slot) + 1 := by
    fin_cases slot <;> rfl
  obtain ⟨warp, start, s, vs, hStart, hs, ⟨hFrame, hLane⟩, hWalk, hSaw⟩ :=
    actualReuseFrame hp hX .primingSwizzle site (hTarget.symm ▸ he)
  change s.pc = 356 at hs
  change (loaderSliceEvents 356 (cutTarget .primingSwizzle site + 1) vs)[index - start]? =
    _ at hSaw
  rw [hTarget] at hSaw
  have hClean := walkWithArrivalClean hWalk
    (sliceContainsEvent hWalk (List.mem_of_getElem? hSaw)) rfl
  have hAt := pipelineAtCut hs hFrame.1 hFrame.2.1 hClean ⟨_, Flow.code_356, rfl⟩
  exact ⟨start, s, vs, hStart, hAt.mono ⟨hLane.1, hAt.2.2.2.2.1, trivial⟩, hWalk, hSaw⟩

/-- The actual initial swizzle is already available when either priming copy is issued. -/
theorem actualPrimingCopyCheckpoint (slot : Fin 2) {g index pc : Nat} {spec : AsyncCopy.Spec}
    (he : X.get (g, index) = some ⟨pc, .copy spec⟩)
    (hFirst : copyPacketFirst (primingPacketSite slot) ≤ pc)
    (hLast : pc < copyCommitPc (primingPacketSite slot)) :
    ∃ (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ At s 356 [(1061, b32 (g % l.block)), (2535, b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents 356 (copyCommitPc (primingPacketSite slot)) vs)[index - start]? =
        some ⟨pc, .copy spec⟩ := by
  let site : Fin 4 := ⟨slot, by have := slot.isLt; omega⟩
  have hFirstPc : 356 ≤ copyPacketFirst (primingPacketSite slot) := by fin_cases slot <;> decide
  have hStop : cutStop .primingCopyEntry site = copyCommitPc (primingPacketSite slot) := by
    fin_cases slot <;> rfl
  let e : Event := ⟨pc, .copy spec⟩
  have hNext : ¬ Ends e := by simp [e, Ends]
  have hInside : reuseWindow .primingCopyEntry site pc = true := by
    rw [reuseWindow, hStop]
    exact decide_eq_true ⟨hFirstPc.trans hFirst, hLast⟩
  obtain ⟨warp, start, s, vs, hStart, hs, ⟨hFrame, hLane⟩, hw, hSeen⟩ :=
    actualIndexedLoaderFrame hp hX .primingCopyEntry site he hNext hInside
  have hClean := walkWithContinuingEventClean hw
    (sliceContainsEvent hw (List.mem_of_getElem? hSeen)) hNext
  change s.pc = 356 at hs
  have hAt := pipelineAtCut hs hFrame.1 hFrame.2.1 hClean ⟨_, Flow.code_356, rfl⟩
  change (loaderSliceEvents 356 (cutStop .primingCopyEntry site) vs)[index - start]? = _ at hSeen
  rw [hStop] at hSeen
  exact ⟨start, s, vs, hStart, hAt.mono ⟨hLane.1, hAt.2.2.2.2.1, trivial⟩, hw, hSeen⟩
end

/-- The steady V address cut starts at its paired K swizzle and carries K's stage word. -/
def recurringSelectionStageReg (site : Fin 4) : Nat :=
  if site = 3 then 7179 else (recurringStageInputs site).1

private theorem recurringSelectionCodeAt (site : Fin 4) :
    ∃ ins, kernel.code[recurringSelectionStart site]? = some ins ∧ ins.op.isLocal = true := by
  fin_cases site
  · exact ⟨_, Flow.code_957, rfl⟩
  · exact ⟨_, Flow.code_1203, rfl⟩
  · exact ⟨_, Flow.code_1427, rfl⟩
  · exact ⟨_, Flow.code_1451, rfl⟩

private theorem recurringSelectionStageFact (site : Fin 4) :
    ∃ f ∈ loaderRingFacts, f.value = .slot (recurringSelectionStageReg site) ∧
      f.active (recurringSelectionStart site) := by
  let k : RingFact := ⟨.slot 7179, 372, 1869, [371, 910, 914, 1345, 1738]⟩
  let v : RingFact := ⟨.slot 1139, 1141, 1343, [1140]⟩
  fin_cases site
  · exact ⟨k, by decide, rfl, by decide⟩
  · exact ⟨v, by decide, rfl, by decide⟩
  · exact ⟨k, by decide, rfl, by decide⟩
  · exact ⟨k, by decide, rfl, by decide⟩

section
variable {p : Params}

/-- Each actual recurring copy has its address-calculation checkpoint even if
the execution stops before the packet's commit or publication. -/
theorem actualRecurringCopyCheckpoint {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (site : Fin 4) {g index pc : Nat}
    {spec : AsyncCopy.Spec} (he : X.get (g, index) = some ⟨pc, .copy spec⟩)
    (hFirst : copyPacketFirst (recurringPacketSite site) ≤ pc)
    (hLast : pc < copyCommitPc (recurringPacketSite site)) :
    ∃ (stage : Fin 3) (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ At s (recurringSelectionStart site)
        [(recurringSelectionStageReg site, b32 stage), (2535, b32 l.sharedBase)] ∧
      LoaderCopyLaneFrame l g s ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents (recurringSelectionStart site) (copyCommitPc (recurringPacketSite site))
        vs)[index - start]? = some ⟨pc, .copy spec⟩ := by
  let e : Event := ⟨pc, .copy spec⟩
  have hNext : ¬ Ends e := by simp [e, Ends]
  have hEarly : recurringSelectionStart site ≤ copyPacketFirst (recurringPacketSite site) := by
    fin_cases site <;> decide
  have hInside : reuseWindow .recurringCopyEntry site pc = true :=
    decide_eq_true ⟨hEarly.trans hFirst, hLast⟩
  obtain ⟨warp, start, s, vs, hStart, hPc, ⟨hFrame, hLane⟩, hw, hSeen⟩ :=
    actualIndexedLoaderFrame hp hX .recurringCopyEntry site he hNext hInside
  have hClean := walkWithContinuingEventClean hw
    (sliceContainsEvent hw (List.mem_of_getElem? hSeen)) hNext
  have hs := pipelineAtCut hPc hFrame.1 hFrame.2.1 hClean (recurringSelectionCodeAt site)
  obtain ⟨f, hf, hValue, hLive⟩ := recurringSelectionStageFact site
  have hSlot := hFrame.2.2 f hf (hPc.symm ▸ hLive)
  rw [hValue] at hSlot
  obtain ⟨stage, hWord, _⟩ := hSlot
  exact ⟨stage, start, s, vs, hStart, hs.mono ⟨hWord, hs.2.2.2.2.1, trivial⟩,
    hLane, hw, hSeen⟩

/-- The concrete trace of each issued ready publication passes the start of
that packet's ordinary-copy instructions. The slice indexes the same occurrence
as the execution even when this static packet has run more than once. -/
theorem actualPacketEntry {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (packet : Fin 6) {g index : Nat} {loc : Loc}
    (he : X.get (g, index) = some ⟨copyCommitPc packet + 1, .asyncArrive loc true⟩) :
    ∃ (start : Nat) (s : TState) (vs : List Visit),
      start ≤ index ∧ s.pc = copyPacketFirst packet ∧
      Holds s.regs [(2535, b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs ∧
      (loaderSliceEvents (copyPacketFirst packet) (copyCommitPc packet + 2) vs)[index - start]? =
        some ⟨copyCommitPc packet + 1, .asyncArrive loc true⟩ := by
  have hPacket : ∃ (cut : ReuseCutpoint) (site : Fin 4),
      cutPc cut site = copyPacketFirst packet ∧
      cutTarget cut site = copyCommitPc packet + 1 ∧
      cutStop cut site = copyCommitPc packet + 2 := by
    fin_cases packet
    · exact ⟨.primingPacket, 0, rfl, rfl, rfl⟩
    · exact ⟨.primingPacket, 1, rfl, rfl, rfl⟩
    · exact ⟨.packet, 0, rfl, rfl, rfl⟩
    · exact ⟨.packet, 1, rfl, rfl, rfl⟩
    · exact ⟨.packet, 2, rfl, rfl, rfl⟩
    · exact ⟨.packet, 3, rfl, rfl, rfl⟩
  obtain ⟨cut, site, hPc, hTarget, hStop⟩ := hPacket
  obtain ⟨warp, start, s, vs, hStart, hs, ⟨hFrame, _⟩, hw, hSaw⟩ :=
    actualReuseFrame hp hX cut site (hTarget.symm ▸ he)
  rw [hPc, hTarget, hStop] at hSaw
  exact ⟨start, s, vs, hStart, hs.trans hPc, ⟨hFrame.2.1.1, trivial⟩, hw, hSaw⟩

private theorem rejectsContinuingEvent {l : Launch} {g : Nat} {t : TState} {es : List Event}
    {vs : List Visit} {f : Fault} {e : Event}
    (hOut : out kernel Assumptions.all l g t = .ev (.ub f))
    (hw : Walk kernel Assumptions.all l g t es vs) (he : e ∈ es)
    (hc : ¬ Ends e) : False := by
  cases hw with
  | stop => cases he
  | tau h _ => rw [Tau, hOut] at h; cases h
  | ev h _ =>
    obtain ⟨tmpl, h, hFire⟩ := h
    rw [hOut] at h
    obtain rfl := Out.ev.inj h
    cases hFire.2
  | last h =>
    obtain rfl := List.mem_singleton.mp he
    obtain ⟨_, _, hFire⟩ := h
    exact hc (fires_none_ends hFire)

private theorem reuseEmptySpinBefore {l : Launch} {m : Mem0} (hp : Pre p l m) (site : Fin 4)
    (stage : Fin 3) {g lower : Nat} (hScopeLower : lower ≤ reuseEntry site) {s : TState}
    {es : List Event} {vs : List Visit} {event : Event} {stop : Nat}
    (hs : At s (reuseEntry site)
      [((recurringStageInputs site).1, b32 stage), (2535, b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g s es vs) (hContinue : ¬ Ends event)
    (hLater : (recurringEmptyWait site).pc < event.pc)
    (hUpper : (recurringEmptyWait site).pc < stop) (hSeen : event ∈ loaderSliceEvents lower stop vs)
    :
    ∃ (retries phase : Nat) (u : TState) (rest : List Event) (tail : List Visit),
      phase < 2 ∧
      es = List.replicate retries ⟨(recurringEmptyWait site).pc,
          .wait (initObject l (g / l.block) (emptySlot stage)) phase false true .cta⟩ ++
        ⟨(recurringEmptyWait site).pc,
          .wait (initObject l (g / l.block) (emptySlot stage)) phase true true .cta⟩ :: rest ∧
      At u ((recurringEmptyWait site).pc + 3)
        [((copyArrivalAddress (recurringPacketSite site)).1, b32 (l.sharedBase + 8 * stage.val))] ∧
      Walk kernel Assumptions.all l g u rest tail ∧ event ∈ loaderSliceEvents lower stop tail := by
  let w := recurringEmptyWait site
  let F := recurringBarrierFactsWith l site stage none
  let addr := l.sharedBase + 8 * stage.val + 56
  let empty : Loc := ⟨.shared, g / l.block, addr⟩
  obtain ⟨t, hLocal, ht⟩ := recurringBarrierPrepWith hp site stage none s hs
  obtain ⟨tail, hWalk, _, hSaw⟩ := loaderEventAfterLocal hLocal hw hSeen
  have hRange : 174 ≤ w.pc ∧ w.pc + 3 < 1906 := by fin_cases site <;> decide
  have hAddr : addr < 2 ^ 32 := by
    have := hp.shared.2.1
    have := stage.isLt
    dsimp [addr]
    omega
  have hAlign : addr % 8 = 0 := by
    have := hp.shared.1
    dsimp [addr]
    omega
  have template (u : TState) (hPc : u.pc = w.pc) (hClean : u.fault = none)
      (hReg : u.regs w.base = some (b32 addr)) :
      out kernel Assumptions.all l g u =
        .ev (ofExec (do
          let bits ← readBits l g u 32 (.reg w.phase)
          pure (.wait empty (bits.toNat % 2) (fun ok => next (setReg u w.result (.pred ok)))
            true .cta))) := by
    have hCode := (recurringEmptyWaitCode site).1
    change kernel.code[w.pc]? = _ at hCode
    rw [← hPc] at hCode
    rw [loaderOutCore (by omega) (by omega), out_event hClean hCode rfl rfl]
    have hEff : effAddr l g u .shared w.base 0 = .ok empty := by
      simpa only [Nat.cast_zero, Nat.add_zero, empty] using
        (effAddr_b32_off (g := g) (L := l) (off := 0) hReg (by omega))
    have hLoc : mbarLoc l g u w.base 0 = .ok empty := by
      simp [mbarLoc, hEff, empty, hAlign, bind, Except.bind, pure, Except.pure]
    dsimp only [w] at hLoc ⊢
    simp [eventTmpl, widenMbarScope, tmaTmpl, hLoc, bind, Except.bind, pure, Except.pure]
  have hOut := template t ht.1 ht.2.2.2.1 ht.2.2.2.2.1
  cases hRead : readBits l g t 32 (.reg w.phase) with
  | error f =>
    rw [hRead] at hOut
    exact (rejectsContinuingEvent hOut hWalk (sliceContainsEvent hWalk hSaw) hContinue).elim
  | ok bits =>
    obtain ⟨word, hWord⟩ : ∃ v, t.regs w.phase = some v := by
      cases hr : t.regs w.phase with
      | none => simp [readBits, readReg, hr, bind, Except.bind] at hRead
      | some v => exact ⟨v, rfl⟩
    let pFrame := (w.phase, word) :: F
    have ht' : At t w.pc pFrame :=
      ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, hWord, ht.2.2.2.2⟩
    have hFresh : ∀ pair ∈ pFrame, pair.1 ≠ w.result := by
      fin_cases site <;> simp [pFrame, F, w, recurringBarrierFactsWith, recurringEmptyWait,
        recurringPacketSite, copyArrivalAddress]
    have hTemplate (u : TState) (hAt : At u w.pc pFrame) :
        out kernel Assumptions.all l g u = .ev
          (.wait empty (bits.toNat % 2) (fun ok => next (setReg u w.result (.pred ok)))
            true .cta) := by
      have hp : u.regs w.phase = some word := hAt.2.2.2.2.1
      have hBits : readBits l g u 32 (.reg w.phase) = .ok bits := by
        simpa only [readBits, readReg, hp, hWord, bind, Except.bind] using hRead
      rw [template u hAt.1 hAt.2.2.2.1 hAt.2.2.2.2.2.1, hBits]
      rfl
    have hLower : lower ≤ w.pc := hScopeLower.trans (Nat.sub_le ..)
    obtain ⟨n, u, rest, later, hEvents, hu, hw', hIn⟩ :=
      pollBeforeSliceEvent (l := l) (g := g) (addr := addr) (phase := bits.toNat % 2)
        w (recurringEmptyWaitCode site) hRange hLower hUpper hFresh hTemplate
        ht' hWalk hLater hSaw
    have hAt : At u (w.pc + 3)
        [((copyArrivalAddress (recurringPacketSite site)).1, b32 (l.sharedBase + 8 * stage.val))] :=
      hu.mono ⟨hu.2.2.2.2.2.2.1, trivial⟩
    exact ⟨n, bits.toNat % 2, u, rest, later, Nat.mod_lt _ (by decide),
      by simpa only [emptySlot_address] using hEvents, hAt, hw', hIn⟩

/-- The checked suffix at a recurring packet's entry starts with the empty acquire. -/
theorem reuseEmptyPrefixFromEarlierScope {l : Launch} {m : Mem0} (hp : Pre p l m) (site : Fin 4)
    (stage : Fin 3) {g lower : Nat} (hScopeLower : lower ≤ reuseEntry site) {s : TState}
    {es : List Event} {vs : List Visit} {loc : Loc}
    (hs : At s (reuseEntry site)
      [((recurringStageInputs site).1, b32 stage), (2535, b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSeen : ⟨reuseArrival site, .asyncArrive loc true⟩ ∈
      loaderSliceEvents lower (reuseArrival site + 1) vs) :
    ∃ (retries phase : Nat) (rest : List Event),
      phase < 2 ∧ loc = initObject l (g / l.block) (readySlot stage) ∧
      es = List.replicate retries ⟨(recurringEmptyWait site).pc,
          .wait (initObject l (g / l.block) (emptySlot stage)) phase false true .cta⟩ ++
        ⟨(recurringEmptyWait site).pc,
          .wait (initObject l (g / l.block) (emptySlot stage)) phase true true .cta⟩ :: rest := by
  have hLater : (recurringEmptyWait site).pc < reuseArrival site := by fin_cases site <;> decide
  obtain ⟨n, phase, u, rest, tail, hPhase, hEvents, hAt, hw', hIn⟩ :=
    reuseEmptySpinBefore hp site stage hScopeLower hs hw (by simp [Ends]) hLater
      (by omega) hSeen
  have hScope : lower ≤ (recurringEmptyWait site).pc + 3 :=
    hScopeLower.trans (by fin_cases site <;> decide)
  exact ⟨n, phase, rest, hPhase, recurringReadyArrivalFromBase hp site stage hScope hAt hw' hIn,
    hEvents⟩

/-- The checked suffix at a recurring packet's entry starts with the empty acquire. -/
theorem reuseEmptyPrefixFromCheckpoint {l : Launch} {m : Mem0} (hp : Pre p l m) (site : Fin 4)
    (stage : Fin 3) {g : Nat} {s : TState} {es : List Event} {vs : List Visit} {loc : Loc}
    (hs : At s (reuseEntry site)
      [((recurringStageInputs site).1, b32 stage), (2535, b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSeen : ⟨reuseArrival site, .asyncArrive loc true⟩ ∈
      loaderSliceEvents (reuseEntry site) (reuseArrival site + 1) vs) :
    ∃ (retries phase : Nat) (rest : List Event),
      phase < 2 ∧ loc = initObject l (g / l.block) (readySlot stage) ∧
      es = List.replicate retries ⟨(recurringEmptyWait site).pc,
          .wait (initObject l (g / l.block) (emptySlot stage)) phase false true .cta⟩ ++
        ⟨(recurringEmptyWait site).pc,
          .wait (initObject l (g / l.block) (emptySlot stage)) phase true true .cta⟩ :: rest := by
  exact reuseEmptyPrefixFromEarlierScope hp site stage le_rfl hs hw hSeen

/-- Reaching a recurring publication supplies the preceding successful acquire of the
same physical slot, with exactly its failed retries after the packet checkpoint. -/
theorem actualReuseEmptyPrefix {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (site : Fin 4) {g index : Nat} {loc : Loc}
    (he : X.get (g, index) = some ⟨reuseArrival site, .asyncArrive loc true⟩) :
    ∃ (stage : Fin 3) (start retries phase : Nat) (rest : List Event),
      start ≤ index ∧ phase < 2 ∧ loc = initObject l (g / l.block) (readySlot stage) ∧
      (X.tr g).drop start =
        List.replicate retries ⟨(recurringEmptyWait site).pc,
          .wait (initObject l (g / l.block) (emptySlot stage)) phase false true .cta⟩ ++
        ⟨(recurringEmptyWait site).pc,
          .wait (initObject l (g / l.block) (emptySlot stage)) phase true true .cta⟩ :: rest := by
  obtain ⟨stage, start, s, vs, hStart, hs, hw, hTarget⟩ := actualReuseCheckpoint hp hX site he
  obtain ⟨n, phase, rest, hPhase, hSlot, hPrefix⟩ :=
    reuseEmptyPrefixFromCheckpoint hp site stage hs hw (List.mem_of_getElem? hTarget)
  exact ⟨stage, start, n, phase, rest, hStart, hPhase, hSlot, hPrefix⟩
end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (site : Fin 4) (stage : Fin 3)
    {g index pc start lower stop : Nat} {s : TState} {vs : List Visit} {spec : AsyncCopy.Spec}
    (he : X.get (g, index) = some ⟨pc, .copy spec⟩) (hStart : start ≤ index)
    (hs : At s (reuseEntry site)
      [((recurringStageInputs site).1, b32 stage), (2535, b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs)
    (hScope : lower ≤ reuseEntry site) (hLater : (recurringEmptyWait site).pc < pc)
include hp hX site stage he hStart hs hw hScope hLater

/-- Recover the successful empty wait from the same actual checkpoint that
supplies a selected recurring copy's physical destination. -/
theorem recurringCopyEmptyFromCheckpointWithResume (hWait : (recurringEmptyWait site).pc < stop)
    (hSeen : ⟨pc, .copy spec⟩ ∈ loaderSliceEvents lower stop vs) :
    ∃ (retries phase : Nat) (rest : List Event), phase < 2 ∧
      (X.tr g).drop start =
        List.replicate retries ⟨(recurringEmptyWait site).pc,
          .wait (initObject l (g / l.block) (emptySlot stage)) phase false true .cta⟩ ++
        ⟨(recurringEmptyWait site).pc,
          .wait (initObject l (g / l.block) (emptySlot stage)) phase true true .cta⟩ :: rest ∧
      Resumes kernel X (g, start + retries) (g, index) ∧
      ∃ (u : TState) (visits : List Visit), u.pc = (recurringEmptyWait site).pc + 3 ∧
        RingShape u ∧ Walk kernel Assumptions.all l g u rest visits := by
  let event : Event := ⟨pc, .copy spec⟩
  obtain ⟨retries, phase, u, rest, post, hPhase, hEvents, hu, hWalk, _⟩ :=
    reuseEmptySpinBefore hp site stage hScope hs hw (by simp [Ends]) hLater
      hWait hSeen
  let empty := initObject l (g / l.block) (emptySlot stage)
  let poll : Bool → Event := fun ok => ⟨(recurringEmptyWait site).pc,
    .wait empty phase ok true .cta⟩
  change (X.tr g).drop start = List.replicate retries (poll false) ++
    poll true :: rest at hEvents
  have hIndex : retries < index - start := by
    by_contra! hBad
    have hGet : ((X.tr g).drop start)[index - start]? = some event := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hStart]
      exact he
    rcases hBad.lt_or_eq with hLt | hEq
    · rw [hEvents, List.getElem?_append_left (by simpa using hLt), List.getElem?_replicate,
        ite_eq_left hLt] at hGet
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj hGet))
    · rw [hEvents, hEq, List.getElem?_append_right (by simp), List.length_replicate,
        Nat.sub_self] at hGet
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj hGet))
  have hPoll : X.get (g, start + retries) = some (poll true) := by
    change (X.tr g)[start + retries]? = _
    rw [← List.getElem?_drop, hEvents, List.getElem?_append_right (by simp),
      List.length_replicate, Nat.sub_self]
    rfl
  obtain ⟨exit, hSpin⟩ := actualCanonicalPoll hX hPoll
  have hTrace : TraceBefore X (g, start + retries) (g, index) :=
    ⟨rfl, by omega, len_of_get he⟩
  refine ⟨retries, phase, rest, hPhase, hEvents, ⟨hTrace, ?_⟩,
    u, post, hu.1, ringShapeOfAt hu, hWalk⟩
  simp only [hPoll, Option.map_some, poll, Kind.resume]
  exact ⟨_, exit, empty, phase, true, .cta, hPoll, hSpin, hTrace⟩

end

section
variable {l : Launch}

private theorem noLocalAtEvent {g pc : Nat} {t u : TState} {op : Op} (hAt : t.pc = pc)
    (hLo : 174 ≤ pc) (hHi : pc < 1906) (hc : kernel.code[pc]? = some ⟨none, op⟩)
    (hop : op.isLocal = false) (h : Tau kernel Assumptions.all l g t u) : False := by
  have hCore : Tau kernel [] l g t u := by
    unfold Tau at *
    rwa [← loaderOutCore (by omega) (by omega)]
  exact tau_core_not_event (hAt.symm ▸ hc) hop hCore

private theorem returnsBeforeArrival {g : Nat} {t : TState} {es : List Event} {vs : List Visit}
    {loc : Loc} {pc lower stop finish : Nat} {op : Op} (ht : t.pc = pc) (hLo : 174 ≤ pc)
    (hHi : pc < 1906) (hc : kernel.code[pc]? = some ⟨none, op⟩) (hop : op.isLocal = false)
    (hScope : lower ≤ pc ∧ pc < stop) (hBefore : pc < finish)
    (hw : Walk kernel Assumptions.all l g t es vs)
    (hSaw : ⟨finish, .asyncArrive loc true⟩ ∈ loaderSliceEvents lower stop vs) :
    ∃ next event rest tail,
      es = event :: rest ∧ vs = visit kernel l g t (some event) :: tail ∧
      EStep kernel Assumptions.all l g t event (some next) ∧
      Walk kernel Assumptions.all l g next rest tail ∧
      ⟨finish, .asyncArrive loc true⟩ ∈ loaderSliceEvents lower stop tail := by
  cases hw with
  | stop => simp [loaderSliceEvents] at hSaw
  | tau h _ => exact (noLocalAtEvent ht hLo hHi hc hop h).elim
  | last h =>
    obtain ⟨_, _, hf⟩ := h
    have hEnd := fires_none_ends hf
    obtain hEq : (⟨finish, .asyncArrive loc true⟩ : Event) = _ := by
      simpa [loaderSliceEvents, visit, ht, hScope.1, hScope.2] using hSaw
    simp [← hEq, Ends] at hEnd
  | @ev _ next event rest tail h hw =>
    have hPc := estep_source_pc h
    have hNe : (⟨finish, .asyncArrive loc true⟩ : Event) ≠ event := by
      intro hEq
      have he := congrArg Event.pc hEq
      change finish = event.pc at he
      omega
    refine ⟨next, event, rest, tail, rfl, rfl, h, hw, ?_⟩
    simpa [loaderSliceEvents, visit, ht, hScope.1, hScope.2, hNe] using hSaw

/-- A packet publication retains the issuing frame and advances exactly one instruction. -/
theorem packetArrivalStepFrame {g : Nat} {t u : TState} {e : Event} (site : Fin 6)
    (ht : t.pc = copyCommitPc site + 1) (hc : EStep kernel Assumptions.all l g t e (some u)) :
    ∃ loc, e.kind = .asyncArrive loc true ∧ u = next t := by
  have hLo : 174 ≤ copyCommitPc site + 1 := by fin_cases site <;> decide
  have hHi : copyCommitPc site + 1 < 1906 := by fin_cases site <;> decide
  obtain ⟨tmpl, hOut, hFires⟩ := hc
  have hf : t.fault = none := by
    cases hf : t.fault
    · rfl
    · simp only [out, hf, Out.ev.injEq] at hOut
      subst tmpl
      cases hFires.2
  have hCode := (copyCommitCode site).2
  change kernel.code[copyCommitPc site + 1]? = _ at hCode
  rw [← ht] at hCode
  rw [loaderOutCore (by omega) (by omega), out_event hf hCode rfl rfl] at hOut
  change Out.ev (cpAsyncTmpl l g t
    (.cpAsyncArrive true (copyArrivalAddress site).1 (copyArrivalAddress site).2 false)) =
      .ev tmpl at hOut
  cases hm : mbarLoc l g t (copyArrivalAddress site).1 (copyArrivalAddress site).2 with
  | error f =>
    simp [cpAsyncTmpl, hm, Except.bind, bind, ofExec] at hOut
    subst tmpl
    cases hFires.2
  | ok loc =>
    rw [cpAsyncTmpl_arrive_noinc hm] at hOut
    obtain rfl := Out.ev.inj hOut
    obtain ⟨rfl, hNext⟩ := hFires
    obtain rfl := Option.some.inj hNext
    exact ⟨loc, rfl, rfl⟩

/-- The return from a packet publication is at the following loader instruction. -/
theorem packetArrivalStep {g : Nat} {t u : TState} {e : Event} (site : Fin 6)
    (ht : t.pc = copyCommitPc site + 1) (hc : EStep kernel Assumptions.all l g t e (some u)) :
    ∃ loc, e.kind = .asyncArrive loc true ∧ u.pc = copyCommitPc site + 2 := by
  obtain ⟨loc, hKind, rfl⟩ := packetArrivalStepFrame site ht hc
  exact ⟨loc, hKind, by simp [next, ht]⟩

private theorem arrivalOnlyInSlice {g lower : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (site : Fin 6) {loc : Loc} (hLower : lower ≤ copyCommitPc site + 1)
    (ht : t.pc = copyCommitPc site + 1) (hw : Walk kernel Assumptions.all l g t es vs)
    (hSaw : ⟨copyCommitPc site + 1, .asyncArrive loc true⟩ ∈
      loaderSliceEvents lower (copyCommitPc site + 2) vs) :
    loaderSliceEvents lower (copyCommitPc site + 2) vs =
      [⟨copyCommitPc site + 1, .asyncArrive loc true⟩] := by
  have hLo : 174 ≤ copyCommitPc site + 1 := by fin_cases site <;> decide
  have hHi : copyCommitPc site + 1 < 1906 := by fin_cases site <;> decide
  cases hw with
  | stop => simp [loaderSliceEvents] at hSaw
  | tau h _ => exact (noLocalAtEvent ht hLo hHi (copyCommitCode site).2 rfl h).elim
  | @last _ event _ =>
    have hEq : (⟨copyCommitPc site + 1, .asyncArrive loc true⟩ : Event) = event := by
      simpa [loaderSliceEvents, visit, ht, hLower] using hSaw
    simpa [loaderSliceEvents, visit, ht, hLower] using congrArg (fun ev : Event => [ev]) hEq.symm
  | @ev _ u event es rest h hw =>
    obtain ⟨_, _, hu⟩ := packetArrivalStep site ht h
    have hempty : loaderSliceEvents lower (copyCommitPc site + 2) rest = [] := by
      cases rest with
      | nil => rfl
      | cons first rest =>
        have hPc := hw.zero_pc rfl
        simp [loaderSliceEvents, hPc, hu]
    simp only [loaderSliceEvents, List.takeWhile_cons, visit, ht, hLower, decide_true,
      Bool.true_and] at hSaw ⊢
    have hLess : copyCommitPc site + 1 < copyCommitPc site + 2 := by omega
    simp only [hLess, decide_true, ↓reduceIte, List.filterMap_cons] at hSaw ⊢
    change _ ∈ event :: loaderSliceEvents lower _ rest at hSaw
    change event :: loaderSliceEvents lower _ rest = _
    rw [hempty] at hSaw ⊢
    exact congrArg (fun ev : Event => [ev]) (List.mem_singleton.mp hSaw).symm

private theorem packetObservedCommitTail {g lower : Nat} {t : TState} {es : List Event}
    {vs : List Visit} (site : Fin 6) {loc : Loc} (hLower : lower ≤ copyCommitPc site)
    (hw : Walk kernel Assumptions.all l g t es vs) (ht : t.pc = copyCommitPc site)
    (hSaw : ⟨copyCommitPc site + 1, .asyncArrive loc true⟩ ∈
      loaderSliceEvents lower (copyCommitPc site + 2) vs) :
    ∃ (first : Visit) (tail : List Visit), vs = first :: tail ∧ first.pc = copyCommitPc site ∧
      loaderSliceEvents lower (copyCommitPc site + 2) vs =
        [⟨copyCommitPc site, .asyncCommit⟩, ⟨copyCommitPc site + 1, .asyncArrive loc true⟩] := by
  have hb := loaderPacketBounds site
  obtain ⟨u, event, tail, rest, _, hVs, hStep, hWalk, hRest⟩ :=
    returnsBeforeArrival ht (by omega) hb.2.2 (copyCommitCode site).1 rfl
      ⟨hLower, by omega⟩ (by omega) hw hSaw
  have hClean := walkWithArrivalClean hw (sliceContainsEvent hw hSaw) rfl
  have hc := (copyCommitCode site).1
  rw [← ht] at hc
  obtain ⟨tmpl, ho, hf⟩ := hStep
  have hOut : out kernel Assumptions.all l g t = .ev (.asyncCommit (next t)) := by
    rw [loaderOutCore (by omega) (by omega), out_event hClean hc rfl rfl]
    rfl
  rw [hOut] at ho
  obtain rfl := Out.ev.inj ho
  obtain ⟨rfl, huv⟩ := hf
  obtain rfl := Option.some.inj huv
  have hAt : (next t).pc = copyCommitPc site + 1 := by simp [next, ht]
  have hTail := arrivalOnlyInSlice site (by omega) hAt hWalk hRest
  refine ⟨_, rest, hVs, by simpa only [visit_pc] using ht, ?_⟩
  rw [hVs]
  have hStop : copyCommitPc site < copyCommitPc site + 2 := by omega
  simpa [loaderSliceEvents, visit, ht, hLower, hStop] using
    congrArg (List.cons ⟨copyCommitPc site, .asyncCommit⟩) hTail

private theorem packetSliceToCommit {g : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (site : Fin 6) {loc : Loc} (hw : Walk kernel Assumptions.all l g t es vs)
    (hLo : copyPacketFirst site ≤ t.pc) (hHi : t.pc ≤ copyCommitPc site)
    (hSaw : ⟨copyCommitPc site + 1, .asyncArrive loc true⟩ ∈
      loaderSliceEvents (copyPacketFirst site) (copyCommitPc site + 2) vs) :
    (∃ v ∈ vs, v.pc = copyCommitPc site) ∧
    loaderSliceEvents (copyPacketFirst site) (copyCommitPc site + 2) vs =
      (vs.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev ++
      [⟨copyCommitPc site, .asyncCommit⟩, ⟨copyCommitPc site + 1, .asyncArrive loc true⟩] := by
  have hb := loaderPacketBounds site
  have hBase {t : TState} {es : List Event} {vs : List Visit}
      (hw : Walk kernel Assumptions.all l g t es vs) (ht : t.pc = copyCommitPc site)
      (hSaw : ⟨copyCommitPc site + 1, .asyncArrive loc true⟩ ∈
        loaderSliceEvents (copyPacketFirst site) (copyCommitPc site + 2) vs) :
      (∃ v ∈ vs, v.pc = copyCommitPc site) ∧
      loaderSliceEvents (copyPacketFirst site) (copyCommitPc site + 2) vs =
        (vs.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev ++
        [⟨copyCommitPc site, .asyncCommit⟩, ⟨copyCommitPc site + 1, .asyncArrive loc true⟩] := by
    obtain ⟨head, tl, hVs, hPc, hTail⟩ :=
      packetObservedCommitTail site (by omega) hw ht hSaw
    refine ⟨⟨head, by rw [hVs]; simp, hPc⟩, ?_⟩
    simpa [hVs, hPc] using hTail
  induction hw with
  | stop => simp [loaderSliceEvents] at hSaw
  | @tau t u es vs ht hw ih =>
    by_cases hLt : t.pc < copyCommitPc site
    · have hNext := packetTauNext hLo hLt ht
      have hStop : t.pc < copyCommitPc site + 2 := by omega
      have hTail : ⟨copyCommitPc site + 1, .asyncArrive loc true⟩ ∈
          loaderSliceEvents (copyPacketFirst site) (copyCommitPc site + 2) vs := by
        simpa [loaderSliceEvents, visit, hLo, hStop] using hSaw
      obtain ⟨⟨v, hv, hp⟩, hEq⟩ := ih (by omega) (by omega) hTail
      exact ⟨⟨v, List.mem_cons_of_mem _ hv, hp⟩,
        by simpa [loaderSliceEvents, visit, hLo, hStop, hLt] using hEq⟩
    · exact hBase (.tau ht hw) (by omega) hSaw
  | @ev t u event es vs he hw ih =>
    by_cases hLt : t.pc < copyCommitPc site
    · have hNext := packetEventNext (by omega) (by omega) he
      have hHere := estep_source_pc he
      have hStop : t.pc < copyCommitPc site + 2 := by omega
      have hNe : (⟨copyCommitPc site + 1, .asyncArrive loc true⟩ : Event) ≠ event := by
        intro h
        have hp := congrArg Event.pc h
        change copyCommitPc site + 1 = event.pc at hp
        omega
      have hTail : ⟨copyCommitPc site + 1, .asyncArrive loc true⟩ ∈
          loaderSliceEvents (copyPacketFirst site) (copyCommitPc site + 2) vs := by
        simpa [loaderSliceEvents, visit, hLo, hStop, hNe] using hSaw
      obtain ⟨⟨v, hv, hp⟩, hEq⟩ := ih (by omega) (by omega) hTail
      exact ⟨⟨v, List.mem_cons_of_mem _ hv, hp⟩,
        by simpa [loaderSliceEvents, visit, hLo, hStop, hLt] using congrArg (List.cons event) hEq⟩
    · exact hBase (.ev he hw) (by omega) hSaw
  | @last t event he =>
    have hStop : t.pc < copyCommitPc site + 2 := by omega
    have h := (List.mem_singleton.mp (by simpa [loaderSliceEvents, visit, hLo, hStop] using hSaw))
    have hPc : copyCommitPc site + 1 = event.pc := congrArg Event.pc h
    have := estep_source_pc he
    omega

/-- Each recorded emitting visit has the program counter of its event. -/
theorem walkVisitIssuePc {g : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g t es vs) {v : Visit} {e : Event} (hv : v ∈ vs)
    (he : v.ev = some e) : e.pc = v.pc := by
  induction hw with
  | stop => simp at hv
  | tau ht hw ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · cases he
    · exact ih hv
  | ev h hw ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · obtain rfl := Option.some.inj he
      exact estep_source_pc h
    · exact ih hv
  | last h =>
    obtain rfl := List.mem_singleton.mp hv
    obtain rfl := Option.some.inj he
    exact estep_source_pc h

private theorem splitSlice {g lower stop : Nat} {s : TState} {pre : List Event}
    {front post : List Visit} (hw : Walk kernel Assumptions.all l g s pre front)
    (hRange : ∀ v ∈ front, lower ≤ v.pc ∧ v.pc < stop) :
    loaderSliceEvents lower stop (front ++ post) = pre ++ loaderSliceEvents lower stop post := by
  unfold loaderSliceEvents
  rw [List.takeWhile_append_of_pos, List.filterMap_append, ← hw.events]
  intro v hv
  obtain ⟨hl, hh⟩ := hRange v hv
  simp [hl, hh]

theorem preCutEventPc {g cut : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) (h : ∀ v ∈ vs, v.pc < cut) {e : Event}
    (he : e ∈ es) : e.pc < cut := by
  rw [hw.events] at he
  obtain ⟨v, hv, hev⟩ := List.mem_filterMap.mp he
  rw [walkVisitIssuePc hw hv hev]
  exact h v hv

private theorem recurringSelectionCode (site : Fin 4) (atCommit : Bool) :
    let lower := recurringSelectionStart site
    let packet := recurringPacketSite site
    let cut := if atCommit then copyCommitPc packet else copyPacketFirst packet
    let last := reuseArrival site
    ((kernel.code.drop lower).take (cut - lower)).all
      (fun i => loaderPipelineCutOp lower cut last [] i.op) = true := by
  fin_cases site <;> cases atCommit <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem recurringBodyToCommit (site : Fin 4) :
    let packet := recurringPacketSite site
    let first := copyPacketFirst packet
    let commit := copyCommitPc packet
    ((kernel.code.drop first).take (commit - first)).all
      (fun i => loaderPipelineCutOp first commit (reuseArrival site) [] i.op) = true := by
  fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem packetGeometryWindow {X : Execution} {g start index lower : Nat} {s : TState}
    {vs : List Visit} {loc : Loc} (packet : Fin 6)
    (hBounds : 174 ≤ lower ∧ lower ≤ copyPacketFirst packet ∧
      copyPacketFirst packet < copyCommitPc packet ∧ copyCommitPc packet < 1901)
    (hFirstCode : ((kernel.code.drop lower).take (copyPacketFirst packet - lower)).all
      (fun i => loaderPipelineCutOp lower (copyPacketFirst packet) (copyCommitPc packet + 1)
        [] i.op) = true)
    (hCommitCode : ((kernel.code.drop lower).take (copyCommitPc packet - lower)).all
      (fun i => loaderPipelineCutOp lower (copyCommitPc packet) (copyCommitPc packet + 1)
        [] i.op) = true)
    (hBodyCode : ((kernel.code.drop (copyPacketFirst packet)).take
      (copyCommitPc packet - copyPacketFirst packet)).all
      (fun i => loaderPipelineCutOp (copyPacketFirst packet) (copyCommitPc packet)
        (copyCommitPc packet + 1) [] i.op) = true) (hp : s.pc = lower) (hs : RingShape s)
    (hw : Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs) (hStart : start ≤ index)
    (hSeen : (loaderSliceEvents lower (copyCommitPc packet + 2)
      vs)[index - start]? = some ⟨copyCommitPc packet + 1, .asyncArrive loc true⟩) :
    let commit := copyCommitPc packet
    (∃ (first : Nat) (spec : AsyncCopy.Spec), start ≤ first ∧ first + 1 < index ∧
      X.get (g, first) = some ⟨copyPacketFirst packet, .copy spec⟩ ∧
      ∀ j e, first ≤ j → j + 1 < index → X.get (g, j) = some e →
        copyPacketFirst packet ≤ e.pc ∧ e.pc < commit) ∧
    ∀ j e, start ≤ j → j + 1 < index → X.get (g, j) = some e →
      e ∈ loaderSliceEvents lower commit vs :=  by
  dsimp only
  let first := copyPacketFirst packet
  let commit := copyCommitPc packet
  let e : Event := ⟨(copyCommitPc packet + 1), .asyncArrive loc true⟩
  let limit := commit + 2
  have hLimit : limit - 1 = commit + 1 := by omega
  have hCut : commit < limit := by omega
  have hEvent : commit ≤ e.pc := by dsimp only [e]; omega
  have hReturns : ¬ Ends e := by simp [e, Ends]
  have hMem := List.mem_of_getElem? hSeen
  obtain ⟨u, pre, tail, front, post, hEs, hVs, hBefore, hPc, _, _, hPre, hTail, hSaw⟩ :=
    loaderObservedCut (F := []) le_rfl hBounds.1 (by omega) hCut
      (by simpa only [List.map_nil, hLimit] using hCommitCode)
      hw ⟨hp.ge, by omega⟩ hs trivial hMem hEvent hReturns
  obtain ⟨head, rest, hPost, hHead, hTrailing⟩ :=
    packetObservedCommitTail packet (by omega) hTail hPc hSaw
  change head.pc = commit at hHead
  have hShort : loaderSliceEvents lower commit vs = pre := by
    rw [hVs, splitSlice hPre hBefore, hPost]
    simp [loaderSliceEvents, hHead]
  have hBroad : loaderSliceEvents lower limit vs =
      pre ++ [⟨commit, .asyncCommit⟩, e] := by
    rw [hVs, splitSlice hPre (fun v hv => ⟨(hBefore v hv).1,
      (hBefore v hv).2.trans hCut⟩)]
    exact congrArg (pre ++ ·) hTrailing
  have hIndex : index - start = pre.length + 1 := by
    rw [show loaderSliceEvents lower limit vs = _ from hBroad] at hSeen
    have hN := (List.getElem?_eq_some_iff.mp hSeen).1
    simp only [List.length_append, List.length_cons, List.length_nil] at hN
    by_cases hin : index - start < pre.length
    · rw [List.getElem?_append_left hin] at hSeen
      have hBad := preCutEventPc hPre (fun v hv => (hBefore v hv).2) (List.mem_of_getElem? hSeen)
      change (copyCommitPc packet + 1) < commit at hBad
      omega
    by_cases heq : index - start = pre.length
    · rw [List.getElem?_append_right (by omega), heq, Nat.sub_self] at hSeen
      have h := congrArg Event.kind (Option.some.inj hSeen)
      cases h
    omega
  refine ⟨?_, ?_⟩
  · have hFirstOut : first < limit := by omega
    have hFirstEvent : first ≤ e.pc := by omega
    obtain ⟨t, firstPre, firstTail, leading, after, hE, hV, hLeading, ht, hTShape, _, hP, hW, hS⟩ :=
      loaderObservedCut (F := []) le_rfl hBounds.1 (by omega) hFirstOut
        (by simpa only [List.map_nil, hLimit] using hFirstCode)
        hw ⟨hp.ge, by omega⟩ hs trivial hMem hFirstEvent hReturns
    have hFirstPc : packetPlanePc packet 0 false = first := by fin_cases packet <;> decide
    have hc : kernel.code[first]? = some ⟨none, packetCopyOpCode packet 0 false⟩ := by
      rw [← hFirstPc]
      exact packetFullCode packet 0 false
    obtain ⟨next, firstEvent, events, visits, hfE, hfV, hStep, _, _⟩ :=
      returnsBeforeArrival ht (by omega) (by omega) hc rfl
        ⟨hBounds.2.1, hFirstOut⟩ (by omega) hW hS
    have hPcFirst : firstEvent.pc = first := (estep_source_pc hStep).trans ht
    have hCopyAt : packetCopyAt t.pc = true := by rw [ht]; simp [packetCopyAt, hc, packetCopyOpCode,
      packetCopyOp]
    have hCopy := (loaderReturningCopyKind (by omega) (by omega) hStep).trans hCopyAt
    obtain ⟨spec, hKind⟩ : ∃ spec, firstEvent.kind = .copy spec := by
      cases hk : firstEvent.kind <;> simp [loaderCopyEvent, hk] at hCopy
      exact ⟨_, rfl⟩
    have hFirstEq : firstEvent = ⟨first, .copy spec⟩ := by
      cases firstEvent
      rw [Event.mk.injEq]
      exact ⟨hPcFirst, hKind⟩
    have hFirstAt : (loaderSliceEvents lower limit vs)[firstPre.length]? = some firstEvent := by
      rw [hV, splitSlice hP (fun v hv => ⟨(hLeading v hv).1,
        (hLeading v hv).2.trans hFirstOut⟩), List.getElem?_append_right (by omega), Nat.sub_self,
        hfV]
      rw [loaderSliceEvents, List.takeWhile_cons_of_pos]
      · simp [visit_ev]
      · rw [visit_pc, ht]
        exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hBounds.2.1, decide_eq_true hFirstOut⟩
    have hFirstLt : firstPre.length < pre.length := by
      rw [hBroad] at hFirstAt
      by_contra! hGe
      have hb := (List.getElem?_eq_some_iff.mp hFirstAt).1
      simp only [List.length_append, List.length_cons, List.length_nil] at hb
      rw [List.getElem?_append_right hGe] at hFirstAt
      have hq : firstPre.length - pre.length = 0 ∨ firstPre.length - pre.length = 1 := by omega
      rcases hq with hq | hq <;> rw [hq] at hFirstAt
      all_goals have h := congrArg Event.kind (Option.some.inj hFirstAt)
                rw [hKind] at h
                cases h
    obtain ⟨q, body, bodyTail, bodyFront, bodyPost, hBodyEs, hBodyVs, hBodyBounds, hQ,
        _, _, hBodyWalk, hB, hBSeen⟩ :=
      loaderObservedCut (F := []) (scopeLower := lower) (lower := first) (cut := commit)
        hBounds.2.1 (by omega) (by omega) hCut
        (by simpa only [List.map_nil, hLimit] using hBodyCode)
        hW ⟨ht.ge, ht.le.trans hBounds.2.2.1.le⟩ hTShape trivial hS hEvent hReturns
    obtain ⟨_, _, _, _, hBodyEnd⟩ :=
      packetObservedCommitTail packet (by omega) hB hQ hBSeen
    have hBetween : pre = firstPre ++ body := by
      apply List.append_cancel_right (bs := [⟨commit, .asyncCommit⟩, e])
      rw [← hBroad, hV, splitSlice hP (fun v hv => ⟨(hLeading v hv).1,
        (hLeading v hv).2.trans hFirstOut⟩), hBodyVs,
        splitSlice hBodyWalk (fun v hv =>
          ⟨hBounds.2.1.trans (hBodyBounds v hv).1, (hBodyBounds v hv).2.trans hCut⟩)]
      change loaderSliceEvents lower limit bodyPost = _ at hBodyEnd
      rw [hBodyEnd, List.append_assoc]
    refine ⟨start + firstPre.length, spec, by omega, by omega, ?_, ?_⟩
    · change (X.tr g)[start + firstPre.length]? = _
      rw [← List.getElem?_drop, hE, hfE, List.getElem?_append_right (by omega), Nat.sub_self]
      exact congrArg some hFirstEq
    · intro j a hJ hJ' hGet
      have hLength : pre.length = firstPre.length + body.length := by
        rw [hBetween, List.length_append]
      have hRaw : ((X.tr g).drop start)[j - start]? = some a := by
        rw [List.getElem?_drop, Nat.add_sub_of_le (by omega : start ≤ j)]
        exact hGet
      rw [hE, hBodyEs, ← List.append_assoc, List.getElem?_append_left (by
          rw [List.length_append]; omega), List.getElem?_append_right (by omega)] at hRaw
      have hMem := List.mem_of_getElem? hRaw
      rw [hBodyWalk.events] at hMem
      obtain ⟨v, hv, he⟩ := List.mem_filterMap.mp hMem
      rw [walkVisitIssuePc hBodyWalk hv he]
      exact hBodyBounds v hv
  · intro j a hJ hBefore hGet
    have hl : j - start < pre.length := by omega
    have hRaw : ((X.tr g).drop start)[j - start]? = some a := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hJ]
      exact hGet
    rw [hEs, List.getElem?_append_left hl] at hRaw
    rw [hShort]
    exact List.mem_of_getElem? hRaw

/-- The actual pre-publication geometry slice contains its first ordinary copy, and
each selected trace record prior to the commit has its original address-walk membership. -/
theorem recurringPacketGeometryWindow {X : Execution} {g start index : Nat} {s : TState}
    {vs : List Visit} {loc : Loc} (site : Fin 4) (hp : s.pc = recurringSelectionStart site)
    (hs : RingShape s) (hw : Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs)
    (hStart : start ≤ index)
    (hSeen : (loaderSliceEvents (recurringSelectionStart site) (reuseArrival site + 1)
      vs)[index - start]? = some ⟨reuseArrival site, .asyncArrive loc true⟩) :
    let lower := recurringSelectionStart site
    let packet := recurringPacketSite site
    let commit := copyCommitPc packet
    (∃ (first : Nat) (spec : AsyncCopy.Spec), start ≤ first ∧ first + 1 < index ∧
      X.get (g, first) = some ⟨copyPacketFirst packet, .copy spec⟩ ∧
      ∀ j e, first ≤ j → j + 1 < index → X.get (g, j) = some e →
        copyPacketFirst packet ≤ e.pc ∧ e.pc < commit) ∧
    ∀ j e, start ≤ j → j + 1 < index → X.get (g, j) = some e →
      e ∈ loaderSliceEvents lower commit vs :=by
  exact packetGeometryWindow (recurringPacketSite site) (by fin_cases site <;> decide)
    (recurringSelectionCode site false) (recurringSelectionCode site true)
    (recurringBodyToCommit site) hp hs hw hStart hSeen

/-- Align the original swizzle suffix with the actual priming group's copy issues. -/
theorem primingPacketGeometryWindow {X : Execution} {g start index : Nat} {s : TState}
    {vs : List Visit} {loc : Loc} (slot : Fin 2) (hp : s.pc = 356) (hs : RingShape s)
    (hw : Walk kernel Assumptions.all l g s ((X.tr g).drop start) vs) (hStart : start ≤ index)
    (hSeen : (loaderSliceEvents 356 (copyCommitPc (primingPacketSite slot) + 2)
      vs)[index - start]? =
        some ⟨copyCommitPc (primingPacketSite slot) + 1, .asyncArrive loc true⟩) :
    let packet := primingPacketSite slot
    let commit := copyCommitPc packet
    (∃ (first : Nat) (spec : AsyncCopy.Spec), start ≤ first ∧ first + 1 < index ∧
      X.get (g, first) = some ⟨copyPacketFirst packet, .copy spec⟩ ∧
      ∀ j e, first ≤ j → j + 1 < index → X.get (g, j) = some e →
        copyPacketFirst packet ≤ e.pc ∧ e.pc < commit) ∧
    ∀ j e, start ≤ j → j + 1 < index → X.get (g, j) = some e →
      e ∈ loaderSliceEvents 356 commit vs := by
  apply packetGeometryWindow (primingPacketSite slot) _ _ _ _ hp hs hw hStart hSeen
  · fin_cases slot <;> decide
  all_goals fin_cases slot <;> (set_option maxRecDepth 100000 in kernel_rfl)
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The exact issuing-thread prefix ending at an arbitrary actual ready publication
contains the packet body followed by its commit and no-increment arrival. -/
theorem actualPacketPrefix (site : Fin 6) {g index : Nat} {loc : Loc}
    (he : X.get (g, index) = some ⟨copyCommitPc site + 1, .asyncArrive loc true⟩) :
    ∃ (start : Nat) (t : TState) (vs : List Visit) (body : List Event),
      index = start + body.length + 1 ∧ t.pc = copyPacketFirst site ∧
      Walk kernel Assumptions.all l g t ((X.tr g).drop start) vs ∧
      (∃ v ∈ vs, v.pc = copyCommitPc site) ∧
      body = (vs.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev ∧
      (body ++ [⟨copyCommitPc site, .asyncCommit⟩, ⟨copyCommitPc site + 1, .asyncArrive loc true⟩])
        <+: (X.tr g).drop start := by
  obtain ⟨start, t, vs, hStart, ht, _, hw, hGet⟩ := actualPacketEntry hp hX site he
  let body := (vs.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev
  let arrival : Event := ⟨copyCommitPc site + 1, .asyncArrive loc true⟩
  obtain ⟨hReach, hSlice⟩ := packetSliceToCommit site hw ht.ge
    (by rw [ht]; exact (loaderPacketBounds site).2.1.le) (List.mem_of_getElem? hGet)
  change _ = body ++ [_, arrival] at hSlice
  have hPrefix : loaderSliceEvents (copyPacketFirst site) (copyCommitPc site + 2) vs
      <+: (X.tr g).drop start := by
    rw [hw.events]
    exact (List.takeWhile_prefix _).filterMap Visit.ev
  rw [hSlice] at hGet hPrefix
  have hBefore : ∀ e ∈ body, e.pc < copyCommitPc site := by
    intro e h
    obtain ⟨v, hv, hEv⟩ := List.mem_filterMap.mp h
    rw [walkVisitIssuePc hw ((List.takeWhile_prefix _).subset hv) hEv]
    exact of_decide_eq_true (List.all_eq_true.mp List.all_takeWhile v hv)
  have hIndex : body.length + 1 = index - start := by
    have hLen := (List.getElem?_eq_some_iff.mp hGet).1
    simp only [List.length_append, List.length_cons, List.length_nil] at hLen
    by_cases hInside : index - start < body.length
    · rw [List.getElem?_append_left hInside] at hGet
      have h := hBefore arrival (List.mem_of_getElem? hGet)
      change copyCommitPc site + 1 < copyCommitPc site at h
      omega
    by_cases hCommit : index - start = body.length
    · rw [List.getElem?_append_right (by omega), hCommit, Nat.sub_self] at hGet
      have h := congrArg Event.pc (Option.some.inj hGet)
      change copyCommitPc site = copyCommitPc site + 1 at h
      omega
    omega
  exact ⟨start, t, vs, body, by omega, ht, hw, hReach, rfl, hPrefix⟩

/-- Every recurring publication is preceded immediately by its group commit and its
last actual ordinary copy. -/
theorem actualReuseLastCopy (site : Fin 4) {g index : Nat} {loc : Loc}
    (he : X.get (g, index) = some ⟨reuseArrival site, .asyncArrive loc true⟩) :
    ∃ pos spec, pos + 2 = index ∧ X.Copy (g, pos) spec ∧ spec.completion = .asyncGroup ∧
      X.get (g, pos + 1) = some ⟨copyCommitPc (recurringPacketSite site), .asyncCommit⟩ := by
  obtain ⟨warp, start, s, vs, hStart, hs, ⟨hf, _⟩, hw, hTarget⟩ :=
    actualReuseFrame hp hX .copy site he
  let packet := recurringPacketSite site
  let copyPc := cutPc .copy site
  let stop := reuseArrival site + 1
  have hb := reuseBounds .copy site
  have : cutTarget .copy site = reuseArrival site := rfl
  have : cutStop .copy site = reuseArrival site + 1 := rfl
  have hLane : copyPc + 1 = copyCommitPc packet := by fin_cases site <;> decide
  have hCommit : copyCommitPc packet + 1 = reuseArrival site := rfl
  have hC := packetFullCode packet 15 true
  have hOp : (packetCopyOpCode packet 15 true).isLocal = false := rfl
  obtain ⟨u, copy, rest, trail, hEs, hTrail, hCopy, hWalk, hSaw⟩ :=
    returnsBeforeArrival hs (by omega) (by omega) hC hOp
      ⟨le_rfl, by omega⟩ (by omega) hw (List.mem_of_getElem? hTarget)
  have hAtCopy : packetCopyAt s.pc = true := by
    rw [hs]
    change (kernel.code[packetPlanePc packet 15 true]?).any
      (fun ins => packetCopyOp ins.op) = true
    rw [hC]
    rfl
  have hUs : u.pc = copyCommitPc packet := by
    rcases packetEventNext (by omega) (by omega) hCopy with h | h
    · rw [h, hs, hLane]
    · rw [hAtCopy] at h
      exact Bool.noConfusion h.2
  have hIsCopy := (loaderReturningCopyKind (by omega) (by omega) hCopy).trans hAtCopy
  obtain ⟨sp, hKind⟩ : ∃ sp, copy.kind = .copy sp := by
    cases hk : copy.kind <;> simp [loaderCopyEvent, hk] at hIsCopy
    exact ⟨_, rfl⟩
  obtain ⟨v, commit, post, visits, hRest, hVisit, hStep, hW, hSeen⟩ :=
    returnsBeforeArrival hUs (by omega) (by omega) (copyCommitCode packet).1 rfl
      ⟨by omega, by omega⟩ (by omega) hWalk hSaw
  have hClean := walkWithArrivalClean hWalk (sliceContainsEvent hWalk hSaw) (by rfl)
  have hOut : out kernel Assumptions.all l g u = .ev (.asyncCommit (next u)) := by
    have hInst := (copyCommitCode packet).1
    rw [← hUs] at hInst
    rw [loaderOutCore (by omega) (by omega), out_event hClean hInst rfl rfl]
    rfl
  obtain ⟨tmpl, hOut', hFires⟩ := hStep
  rw [hOut] at hOut'
  obtain rfl := Out.ev.inj hOut'
  obtain ⟨rfl, hv⟩ := hFires
  obtain rfl := Option.some.inj hv
  have hV : (next u).pc = reuseArrival site := by simp [next, hUs, hCommit]
  have hSingle : reuseEvents .copy site visits =
      [⟨reuseArrival site, .asyncArrive loc true⟩] :=
    arrivalOnlyInSlice packet (by omega) hV hW hSeen
  have hWindowS : reuseWindow .copy site s.pc = true := by
    rw [hs]
    exact decide_eq_true ⟨le_rfl, by omega⟩
  have hWindowU : reuseWindow .copy site u.pc = true := by
    rw [hUs]
    exact decide_eq_true ⟨by omega, by omega⟩
  change (reuseEvents .copy site vs)[index - start]? = _ at hTarget
  rw [hTrail, reuseEventsCons .copy site hWindowS, hVisit, reuseEventsCons .copy site hWindowU,
    hSingle] at hTarget
  have hSelected := (List.getElem?_eq_some_iff.mp hTarget).1
  simp only [Option.toList_some, List.singleton_append, List.length_cons,
    List.length_nil] at hSelected hTarget
  have hIndex : start + 2 = index := by
    have hj : index - start = 0 ∨ index - start = 1 ∨ index - start = 2 := by omega
    rcases hj with hj | hj | hj
    · rw [hj] at hTarget
      have h := congrArg Event.kind (Option.some.inj hTarget)
      rw [hKind] at h
      cases h
    · rw [hj] at hTarget
      have h := congrArg Event.kind (Option.some.inj hTarget)
      cases h
    · omega
  have hGetCopy : X.get (g, start) = some copy := by
    change (X.tr g)[start]? = some copy
    rw [← Nat.add_zero start, ← List.getElem?_drop, hEs]
    rfl
  have hCopyActual : X.Copy (g, start) sp := by
    obtain ⟨pc, kind⟩ := copy
    change kind = .copy sp at hKind
    subst kind
    exact ⟨pc, hGetCopy⟩
  refine ⟨start, sp, hIndex, hCopyActual, (actualCopyShape hX hCopyActual).completion, ?_⟩
  change (X.tr g)[start + 1]? = _
  rw [← List.getElem?_drop, hEs, hRest]
  simp [hUs, packet]

/-- A recurring packet's exact empty-retry prefix and final copy identify its guard. -/
theorem recurringGuardOfEmptyPrefix (site : Fin 4) (stage : Fin 3) {g index start n phase : Nat}
    {loc : Loc} {tail : List Event}
    (he : X.get (g, index) = some ⟨reuseArrival site, .asyncArrive loc true⟩)
    (hStart : start ≤ index)
    (hEvents : (X.tr g).drop start =
      List.replicate n ⟨(recurringEmptyWait site).pc,
        .wait (initObject l (g / l.block) (emptySlot stage)) phase false true .cta⟩ ++
      ⟨(recurringEmptyWait site).pc,
        .wait (initObject l (g / l.block) (emptySlot stage)) phase true true .cta⟩ :: tail) :
    ∃ wait copy, start ≤ wait ∧
      X.get (g, wait) = some ⟨(recurringEmptyWait site).pc,
        .wait (initObject l (g / l.block) (emptySlot stage)) phase true true .cta⟩ ∧
      Resumes kernel X (g, wait) (g, copy) ∧ TracksCpAsync X (g, copy) (g, index) := by
  obtain ⟨copy, spec, hCopyIndex, hCopy, hGroup, hCommit⟩ :=
    actualReuseLastCopy hp hX site he
  let empty := initObject l (g / l.block) (emptySlot stage)
  let ev : Bool → Event := fun ok =>
    ⟨(recurringEmptyWait site).pc, .wait empty phase ok true .cta⟩
  change (X.tr g).drop start = List.replicate n (ev false) ++ ev true :: tail at hEvents
  have hSuccess : ((X.tr g).drop start)[n]? = some (ev true) := by
    rw [hEvents, List.getElem?_append_right (by simp), List.length_replicate, Nat.sub_self]
    rfl
  rw [List.getElem?_drop] at hSuccess
  have hs : X.get (g, start + n) = some (ev true) := hSuccess
  have hAfter : start + n < index := by
    by_contra hBad
    let k := index - start
    have hK : k ≤ n := by dsimp [k]; omega
    have hEq : start + k = index := Nat.add_sub_of_le hStart
    have hArrival : ((X.tr g).drop start)[k]? =
        some ⟨reuseArrival site, .asyncArrive loc true⟩ := by
      rw [List.getElem?_drop, hEq]
      exact he
    rcases hK.lt_or_eq with hLt | hEqual
    · rw [hEvents, List.getElem?_append_left (by simpa using hLt),
        List.getElem?_replicate, ite_eq_left hLt] at hArrival
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj hArrival))
    · subst k
      rw [← hEqual, ← List.getElem?_drop, hArrival] at hSuccess
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj hSuccess))
  obtain ⟨pc, hc⟩ := hCopy
  have hEarlier : start + n < copy := by
    by_contra hBad
    have hIndex : start + n = copy ∨ start + n = copy + 1 := by omega
    rcases hIndex with h | h
    · rw [h, hc] at hs
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj hs))
    · rw [h, hCommit] at hs
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj hs))
  obtain ⟨exit, hSpin⟩ := actualCanonicalPoll hX hs
  have hTrace : TraceBefore X (g, start + n) (g, copy) := ⟨rfl, hEarlier, len_of_get hc⟩
  have hResume : Resumes kernel X (g, start + n) (g, copy) := by
    refine ⟨hTrace, ?_⟩
    simp only [hs, Option.map_some, ev, Kind.resume]
    exact ⟨_, exit, empty, phase, true, .cta, hs, hSpin, hTrace⟩
  exact ⟨start + n, copy, by omega, hs, hResume,
    rfl, by omega, ⟨spec, ⟨pc, hc⟩, hGroup⟩, ⟨loc, true, _, he⟩⟩

/-- Every actual recurring packet has a matching successful empty wait before the
last copy tracked by that exact publication. -/
theorem actualRecurringGuard (site : Fin 4) {g index : Nat} {loc : Loc}
    (he : X.get (g, index) = some ⟨reuseArrival site, .asyncArrive loc true⟩) :
    ∃ (stage : Fin 3) (phase wait copy : Nat),
      loc = initObject l (g / l.block) (readySlot stage) ∧
      X.get (g, wait) = some ⟨(recurringEmptyWait site).pc,
        .wait (initObject l (g / l.block) (emptySlot stage)) phase true true .cta⟩ ∧
      Resumes kernel X (g, wait) (g, copy) ∧ TracksCpAsync X (g, copy) (g, index) := by
  obtain ⟨stage, start, _, phase, _, hStart, _, hLoc, hEvents⟩ :=
    actualReuseEmptyPrefix hp hX site he
  obtain ⟨wait, copy, _, hWait, hGuard, hTrack⟩ :=
    recurringGuardOfEmptyPrefix hp hX site stage he hStart hEvents
  exact ⟨stage, phase, wait, copy, hLoc, hWait, hGuard, hTrack⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
