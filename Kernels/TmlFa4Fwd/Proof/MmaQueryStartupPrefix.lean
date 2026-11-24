-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQRegisters
public import Kernels.TmlFa4Fwd.Proof.RegisterHint
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
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
import Lemmas.Execution.EventFrameSource
import Lemmas.Flow.NotShfl
import Lemmas.Flow.WarpScan
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.MmaAllocationRead
import Kernels.TmlFa4Fwd.Proof.MmaSchedulerEntry
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAllocationExclusion

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

private theorem suffixNonempty {X : Execution} {g index pos : Nat} {e : Event}
    (he : X.get (g, index) = some e) (h : pos ≤ index) : (X.tr g).drop pos ≠ [] := by
  intro hn
  have hl : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have := List.drop_eq_nil_iff.mp hn
  omega

private theorem beforeTarget {X : Execution} {g index pos : Nat} {a e : Event}
    (he : X.get (g, index) = some e) (ha : X.get (g, pos) = some a)
    (hle : pos ≤ index) (hDifferent : a.pc ≠ e.pc) : pos + 1 ≤ index := by
  by_contra! h
  have hEq : pos = index := by omega
  rw [hEq, he] at ha
  exact hDifferent (congrArg Event.pc (Option.some.inj ha.symm))

private theorem startupFenceAndBar {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) (hLen : 3 < (X.tr g).length) :
    X.get (g, 3) = some ⟨172, .fenceMbarInit⟩ ∧
      (4 < (X.tr g).length → X.get (g, 4) = some ⟨173, .bar 0 none .sync⟩) := by
  let e₀ := (X.tr g)[0]'(by omega)
  let e₁ := (X.tr g)[1]'(by omega)
  let e₂ := (X.tr g)[2]'(by omega)
  have hTrace : X.tr g = e₀ :: e₁ :: e₂ :: (X.tr g).drop 3 := by
    have h0 := List.drop_eq_getElem_cons (by omega : 0 < (X.tr g).length)
    have h1 := List.drop_eq_getElem_cons (by omega : 1 < (X.tr g).length)
    have h2 := List.drop_eq_getElem_cons (by omega : 2 < (X.tr g).length)
    rw [h2] at h1
    rw [h1] at h0
    exact h0
  obtain ⟨t, _, hPc, hFault, hBase, hWarp, _, _, _, _, hTail, _⟩ :=
    broadcastPrefixRun hp hX g hg hTrace
  obtain ⟨s, hs, hS, hClean, _⟩ := nonzeroWarpWith (A := Assumptions.all) hp g (warpIndex l g) t
    (show 0 < warpIndex l g by rw [hw]; decide) (warpIndex_lt hp g) hPc hFault hWarp hBase
  have hCore : out kernel [] l g s = .ev (.fenceMbarInit (next s)) := by
    unfold out
    rw [hS, hClean, Flow.code_172]
    rfl
  let hNext : Next kernel Assumptions.all l g t s (.fenceMbarInit (next s)) :=
    ⟨run_rtg hs, startupOut (.inl (by rw [hS]; decide)) hCore⟩
  obtain ⟨_, u, he, hFire, hRun⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, hNone⟩; cases hNone) hTail (by
    intro hNone
    have := List.drop_eq_nil_iff.mp hNone
    omega)
  obtain ⟨rfl, hEq⟩ := hFire
  obtain rfl := Option.some.inj hEq
  refine ⟨by simpa only [hS] using he, ?_⟩
  intro hLen'
  have hPc' : (next s).pc = 173 := by change s.pc + 1 = 173; rw [hS]
  have hCore' : out kernel [] l g (next s) = .ev (.bar 0 (next (next s)) none .sync) := by
    unfold out
    have hFault : (next s).fault = none := hClean
    rw [hPc', hFault, Flow.code_173]
    rfl
  let hBar : Next kernel Assumptions.all l g (next s) (next s)
      (.bar 0 (next (next s)) none .sync) :=
    ⟨.refl, startupOut (.inl (by rw [hPc']; decide)) hCore'⟩
  obtain ⟨_, _, he', hFire, _⟩ := hBar.continuing_at_nonempty (by
    rintro e ⟨_, hNone⟩; cases hNone) hRun (by
    intro hNone
    have := List.drop_eq_nil_iff.mp hNone
    omega)
  obtain ⟨rfl, _⟩ := hFire
  simpa only [hPc'] using he'

private theorem shuffleCountAfter {X : Execution} {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e) :
    ((X.tr g).take (index + 1)).countP Execution.isShfl =
      ((X.tr g).take index).countP Execution.isShfl + if Execution.isShfl e then 1 else 0 := by
  rw [List.take_add_one, show (X.tr g)[index]? = some e from he]
  simp only [Option.toList_some, List.countP_append, List.countP_singleton]

private theorem startupShuffleCount {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) (hLen : 4 < (X.tr g).length) :
    ((X.tr g).take 5).countP Execution.isShfl = 3 := by
  obtain ⟨hFence, hBar⟩ := startupFenceAndBar hp hX hg hw (by omega)
  have h0 := List.getElem?_eq_getElem (by omega : 0 < (X.tr g).length)
  have h1 := List.getElem?_eq_getElem (by omega : 1 < (X.tr g).length)
  have h2 := List.getElem?_eq_getElem (by omega : 2 < (X.tr g).length)
  rw [firstSharedValue hp hX g hg h0] at h0
  rw [secondWarpValue hp hX g hg h1] at h1
  rw [thirdWarpValue hp hX g hg h2] at h2
  rw [shuffleCountAfter (hBar hLen), shuffleCountAfter hFence, shuffleCountAfter h2,
    shuffleCountAfter h1, shuffleCountAfter h0]
  rfl

private def baseFrame (l : Launch) : List (Nat × Value) :=
  [(1062, b32 12), (2535, b32 l.sharedBase)]

private def schedulerAbiFrame (p : Params) (l : Launch) : List (Nat × Value) :=
  [(1062, b32 12), (2535, b32 l.sharedBase), (7203, b32 p.batch), (7506, b64 p.cuQBase)]

private theorem allocationPrefixToRead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLate : 1911 ≤ e.pc) (hIndex : 6 ≤ index) {s : TState} {o : Option TState}
    (hs : At s 1908 (schedulerAbiFrame p l))
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop 6) o) :
    ∃ t, At t 1911 (schedulerAbiFrame p l) ∧
      X.get (g, 6) = some ⟨1909, .tc (.resource .one (some (allocationSlot l g)) (.alloc 512))⟩ ∧
      (laneOf l g = 0 → ∃ col, col < 2 ^ 16 ∧ X.get (g, 7) =
        some ⟨1909, .wr {loc := allocationSlot l g, size := 4} (b32 col).toBytes⟩) ∧
      X.get (g, allocationBarrierPos l g) = some ⟨1910, .bar 2 (some 416) .sync⟩ ∧
      allocationBarrierPos l g + 1 ≤ index ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (allocationBarrierPos l g + 1)) o := by
  let u := next (setReg s 2451 (b32 512))
  have hCore : run kernel [] l g 1 s = some u := by
    apply run_local Flow.code_1908 rfl hs
    rfl
  have hLocal := schedulerLocalTransport (A := Assumptions.all) (lo := 1908) (len := 1)
    rfl (fun hlo hhi => startupOut_eq_nil (by omega) (by omega)) hCore
    (by rw [hs.1]) (by rw [hs.1])
  have hu : At u 1909 ((2451, b32 512) :: schedulerAbiFrame p l) := hs.set (by
    intro pair hm
    simp only [schedulerAbiFrame, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact (by decide : 1062 ≠ 2451)
    · exact (by decide : 2535 ≠ 2451)
    · exact (by decide : 7203 ≠ 2451)
    · exact (by decide : 7506 ≠ 2451))
  have hBase : u.regs 2535 = some (b32 l.sharedBase) := hu.2.2.2.2.2.2.1
  let after := if laneOf l g = 0 then { u with sub := 1 } else next u
  let tm := Tmpl.tc (.resource .one (some (allocationSlot l g)) (.alloc 512)) after
  have hAt : out kernel Assumptions.all l g u = .ev tm := by
    rw [allocationTemplate hp hu.1 hu.2.2.2.1 hBase hu.2.2.2.2.1, hu.2.1]
    rfl
  let hn : Next kernel Assumptions.all l g s u tm := ⟨run_rtg hLocal, hAt⟩
  obtain ⟨alloc, v, hAlloc, hFire, hv⟩ := hn.continuing_at_nonempty (by
    rintro e ⟨_, hNone⟩; cases hNone) hRun (suffixNonempty he hIndex)
  obtain ⟨rfl, hEq⟩ := hFire
  obtain rfl := Option.some.inj hEq
  have hAlloc' : X.get (g, 6) = some ⟨1909,
      .tc (.resource .one (some (allocationSlot l g)) (.alloc 512))⟩ := by
    simpa only [hu.1, tm] using hAlloc
  have hSeven : 7 ≤ index := beforeTarget he hAlloc' hIndex (by dsimp; omega)
  have hStore (hZero : laneOf l g = 0) := allocationStorePrefix hp hZero hu hBase
    hu.2.2.2.2.1 hv (suffixNonempty he hSeven)
  have hBarIndex : allocationBarrierPos l g ≤ index := by
    by_cases hZero : laneOf l g = 0
    · obtain ⟨_, _, he', _⟩ := hStore hZero
      simp only [allocationBarrierPos, hZero, ↓reduceIte]
      exact beforeTarget he he' hSeven (by dsimp; omega)
    · simpa [allocationBarrierPos, hZero] using hSeven
  have hRunBar : Run kernel Assumptions.all l g (next u)
      ((X.tr g).drop (allocationBarrierPos l g)) o := by
    by_cases hZero : laneOf l g = 0
    · obtain ⟨_, _, _, hStore⟩ := hStore hZero
      simpa [allocationBarrierPos, hZero] using hStore
    · simpa [allocationBarrierPos, hZero, after] using hv
  have hU : At (next u) 1910 (schedulerAbiFrame p l) := hu.next.mono hu.2.2.2.2.2
  have hOut : out kernel Assumptions.all l g (next u) =
      .ev (.bar 2 (next (next u)) (some 416) .sync) := by
    rw [startupOut_eq_nil (by rw [hU.1]; decide) (by rw [hU.1]; decide)]
    rw [out_event hU.2.2.2.1 (by rw [hU.1]; exact Flow.code_1910) rfl rfl]
    change Out.ev (barTmpl l g (next u) (.imm 2) (some (.imm 416)) .sync) = _
    have hId : readBits l g (next u) 32 (.imm 2) = .ok (BitVec.ofNat 64 2) := rfl
    have hN : readBits l g (next u) 32 (.imm 416) = .ok (BitVec.ofNat 64 416) := rfl
    simp only [barTmpl, hId, hN, hp.block]
    rfl
  let hNext : Next kernel Assumptions.all l g (next u) (next u)
      (.bar 2 (next (next u)) (some 416) .sync) := ⟨.refl, hOut⟩
  obtain ⟨bar, w, hBar, hFire, hw⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, hNone⟩; cases hNone) hRunBar (suffixNonempty he hBarIndex)
  obtain ⟨rfl, hEq⟩ := hFire
  obtain rfl := Option.some.inj hEq
  have hBarrier : X.get (g, allocationBarrierPos l g) = some ⟨1910, .bar 2 (some 416) .sync⟩ :=
    by simpa only [hU.1] using hBar
  exact ⟨_, hU.next, hAlloc', (fun h => let ⟨col, hc, he, _⟩ := hStore h; ⟨col, hc, he⟩),
    hBarrier, beforeTarget he hBarrier hBarIndex (by dsimp; omega), hw⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem allocationReadSource {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hw : warpIndex l g = 12) (hLate : 1911 ≤ e.pc) :
    ∃ u o, At u 1911 (schedulerAbiFrame p l) ∧
      X.get (g, 6) = some ⟨1909, .tc (.resource .one (some (allocationSlot l g)) (.alloc 512))⟩ ∧
      (laneOf l g = 0 → ∃ col, col < 2 ^ 16 ∧
        X.get (g, 7) = some ⟨1909, .wr {loc := allocationSlot l g, size := 4} (b32 col).toBytes⟩) ∧
      X.get (g, allocationBarrierPos l g) = some ⟨1910, .bar 2 (some 416) .sync⟩ ∧
      (∃ inst, X.get (g, 5) = some ⟨1907,
        .setMaxReg (registerHintOf 12).1 (registerHintOf 12).2 inst⟩) ∧
      allocationBarrierPos l g + 1 ≤ index ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (allocationBarrierPos l g + 1)) o := by
  have hg := event_thread_lt hX he
  obtain ⟨t, o, hIndex, ht, hr⟩ := nonzeroCommonPrefixOfLateEvent hp hX hg
    (show 0 < warpIndex l g by rw [hw]; decide) he (by omega)
  have hAt : At t 174 (startupFacts p l) := by
    apply ht.mono
    refine ⟨hw ▸ ht.2.2.2.2.1, ht.2.2.2.2.2.1, ?_, ?_, ?_, ?_, trivial⟩
    all_goals exact holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts, abiFacts])
  obtain ⟨s, hLocal, hs⟩ := dispatchWarp12 hp hg hAt
  have hStop : out kernel Assumptions.all l g s = .ev (.setMaxReg false 80 (next s)) := by
    rw [startupOut_eq_nil (by rw [hs.1]; decide) (by rw [hs.1]; decide)]
    unfold out
    rw [hs.1, hs.2.2.2.1, Flow.code_1907]
    rfl
  let hn : Next kernel Assumptions.all l g t s (.setMaxReg false 80 (next s)) :=
    ⟨run_rtg hLocal, hStop⟩
  obtain ⟨_, _, hGet, ⟨inst, rfl, hAfter⟩, hRun⟩ :=
    hn.continuing_at_nonempty (by rintro _ ⟨_, _, h⟩; cases h)
      hr (suffixNonempty he hIndex)
  obtain rfl := Option.some.inj hAfter
  have hHint : X.get (g, 5) = some ⟨1907, .setMaxReg false 80 inst⟩ := hs.1 ▸ hGet
  have hKeep : At (next s) 1908 (schedulerAbiFrame p l) := by
    apply hs.next.mono
    refine ⟨?_, ?_, hs.2.2.2.2.1, ?_, trivial⟩
    all_goals exact holds_mem hs.2.2.2.2 (by simp [startupFacts])
  have h6 : 6 ≤ index := beforeTarget he hHint hIndex
    (show 1907 ≠ e.pc by omega)
  obtain ⟨u, hu, hAlloc, hStore, hBar, hPos, hRead⟩ :=
    allocationPrefixToRead hp he hLate h6 hKeep hRun
  exact ⟨u, _, hu, hAlloc, hStore, hBar, ⟨inst, hHint⟩, hPos, hRead⟩

/-- An observed later event forces the allocating warp to have issued its address load.
The continuation retains the actual returned bytes and needs no completed launch. -/
private theorem allocationReadBeforeEventWithFrame {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e) (hw : warpIndex l g = 12) (hLate : 1911 < e.pc) :
    ∃ t bytes o, At t 1911 (schedulerAbiFrame p l) ∧ bytes.length = 4 ∧
      X.get (g, allocationBarrierPos l g + 1) =
        some ⟨1911, .rd {loc := allocationSlot l g, size := 4} bytes⟩ ∧
      allocationBarrierPos l g + 2 ≤ index ∧
      ((X.tr g).take (allocationBarrierPos l g + 2)).countP Execution.isShfl = 3 ∧
      Run kernel Assumptions.all l g (afterLoad t [1179] bytes)
        ((X.tr g).drop (allocationBarrierPos l g + 2)) o := by
  have hg := event_thread_lt hX he
  obtain ⟨u, o, hu, hAlloc, hStore, hBar, hHint, hPos, hRead⟩ :=
    allocationReadSource hp hX he hw (by omega)
  obtain ⟨_, hHint⟩ := hHint
  have hReadTemplate := allocationReadTemplateFromBase (g := g) hp hu hu.2.2.2.2.2.1
  let hNext : Next kernel Assumptions.all l g u u
      (.read {loc := allocationSlot l g, size := 4} (afterLoad u [1179])) :=
    ⟨.refl, hReadTemplate⟩
  obtain ⟨load, w, hLoad, hFire, hw⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, _, _, hNone⟩; cases hNone) hRead (suffixNonempty he hPos)
  obtain ⟨bytes, hSize, rfl, hEq⟩ := hFire
  obtain rfl := Option.some.inj hEq
  have hRead' : X.get (g, allocationBarrierPos l g + 1) =
      some ⟨1911, .rd {loc := allocationSlot l g, size := 4} bytes⟩ :=
    by simpa only [hu.1] using hLoad
  have hLen : 4 < (X.tr g).length := by
    have h := (List.getElem?_eq_some_iff.mp he).1
    change index < (X.tr g).length at h
    unfold allocationBarrierPos at hPos
    split at hPos <;> omega
  have hCount := startupShuffleCount hp hX hg (by assumption) hLen
  have hCount' : ((X.tr g).take (allocationBarrierPos l g + 2)).countP Execution.isShfl = 3 := by
    rw [show allocationBarrierPos l g + 2 = (allocationBarrierPos l g + 1) + 1 by omega,
      shuffleCountAfter hRead', shuffleCountAfter hBar]
    by_cases hZero : laneOf l g = 0
    · obtain ⟨_, _, hs⟩ := hStore hZero
      simp only [allocationBarrierPos, hZero, ↓reduceIte]
      rw [shuffleCountAfter hs, shuffleCountAfter hAlloc, shuffleCountAfter hHint, hCount]
      rfl
    · simp only [allocationBarrierPos, hZero, ↓reduceIte]
      rw [shuffleCountAfter hAlloc, shuffleCountAfter hHint, hCount]
      rfl
  exact ⟨u, bytes, o, hu, hSize, hRead', beforeTarget he hRead' hPos (by dsimp; omega), hCount', hw⟩

/-- An observed later event forces the allocating warp to have issued its address load.
The continuation retains the actual returned bytes and needs no completed launch. -/
theorem allocationReadBeforeEvent {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hw : warpIndex l g = 12) (hLate : 1911 < e.pc) :
    ∃ t bytes o, At t 1911 [(1062, b32 12), (2535, b32 l.sharedBase)] ∧ bytes.length = 4 ∧
      X.get (g, allocationBarrierPos l g + 1) =
        some ⟨1911, .rd {loc := allocationSlot l g, size := 4} bytes⟩ ∧
      allocationBarrierPos l g + 2 ≤ index ∧
      ((X.tr g).take (allocationBarrierPos l g + 2)).countP Execution.isShfl = 3 ∧
      Run kernel Assumptions.all l g (afterLoad t [1179] bytes)
        ((X.tr g).drop (allocationBarrierPos l g + 2)) o := by
  obtain ⟨t, bytes, o, ht, hSize, hRead, hIndex, hCount, hTail⟩ :=
    allocationReadBeforeEventWithFrame hp hX he hw hLate
  exact ⟨t, bytes, o, ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩,
    hSize, hRead, hIndex, hCount, hTail⟩

omit hp hX in
private theorem onlyFaultRecord {l : Launch} {g i : Nat} {t : TState} {es : List Event}
    {o : Option TState} {e : Event} {fault : Fault} (hf : t.fault = some fault)
    (hRun : Run kernel Assumptions.all l g t es o) (he : es[i]? = some e) : e.kind = .ub fault := by
  have hOut : out kernel Assumptions.all l g t = .ev (.ub fault) := by simp [out, hf]
  have hUnique {u : TState} (hs : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) :
      u = t := by
    rcases Relation.ReflTransGen.cases_head hs with rfl | ⟨w, hStep, _⟩
    · rfl
    · rw [Tau, hOut] at hStep
      cases hStep
  cases hRun with
  | nil => simp at he
  | step ht hStep _ =>
    obtain rfl := hUnique ht
    obtain ⟨m, hm, hFire⟩ := hStep
    rw [hOut] at hm
    obtain rfl := Out.ev.inj hm
    cases hFire.2
  | last ht hStep =>
    obtain rfl := hUnique ht
    obtain ⟨m, hm, hFire⟩ := hStep
    rw [hOut] at hm
    obtain rfl := Out.ev.inj hm
    have hZero : i = 0 := by have := (List.getElem?_eq_some_iff.mp he).1; simp at this; omega
    subst i
    obtain rfl := Option.some.inj he.symm
    exact congrArg Event.kind hFire.1

/-- The actual shared read of the TMEM allocation result uses its four-byte startup slot. -/
theorem allocationReadFootprint {g index : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, index) = some ⟨1911, .rd a bs⟩) :
    a = {loc := allocationSlot l g, size := 4} := by
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < 1911 by decide)
    (show 1911 ∉ registerHintSites by decide)
  change roleBodyPc (warpIndex l g) 1911 at hRole
  have hWarp : warpIndex l g = 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨u, o, hu, _, _, _, _, hPos, hRead⟩ :=
    allocationReadSource hp hX he hWarp (Nat.le_refl 1911)
  let step : Next kernel Assumptions.all l g u u
      (.read {loc := allocationSlot l g, size := 4} (afterLoad u [1179])) :=
    ⟨.refl, allocationReadTemplateFromBase hp hu hu.2.2.2.2.2.1⟩
  obtain ⟨_, _, hLoad, ⟨bytes, _, rfl, hNext⟩, hRun⟩ :=
    step.continuing_at_nonempty (by rintro _ ⟨_, _, _, hNone⟩; cases hNone)
      hRead (suffixNonempty he hPos)
  obtain rfl := Option.some.inj hNext
  rcases Nat.eq_or_lt_of_le hPos with hEq | hLater
  · rw [hEq, he] at hLoad
    exact (Kind.rd.inj (congrArg Event.kind (Option.some.inj hLoad))).1
  · have hGet : ((X.tr g).drop (allocationBarrierPos l g + 2))[index -
        (allocationBarrierPos l g + 2)]? = some ⟨1911, .rd a bs⟩ := by
      rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
      exact he
    obtain ⟨s, _, hReach, hFire⟩ := hRun.before_event hGet
    cases hBytes : rebuild 3 bytes with
    | error fault =>
      have hFault : (afterLoad u [1179] bytes).fault = some fault := by
        simp [afterLoad, hBytes]
      cases onlyFaultRecord hFault hRun hGet
    | ok value =>
      have hStart : 1912 ≤ (afterLoad u [1179] bytes).pc := by
        simp [afterLoad, hBytes, hu.1, hu.2.1]
      have hFloor := Thread.resourceSuffixFloor .allocationRead hReach hStart
      change 1912 ≤ s.pc at hFloor
      have hPc : 1911 = s.pc := EventFrame.estep_source_pc hFire
      omega

/-- An actual event beyond allocation has a preceding descriptor send with the assembled
lane-zero operand. The descriptor's received value remains the value from the actual trace. -/
private theorem descriptorSendBeforeEventWithFrame {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e) (hw : warpIndex l g = 12) (hLate : 1911 < e.pc)
    (hKind : ∀ f, e.kind ≠ .ub f) :
    ∃ t recv ok o, descriptorShufflePos (laneOf l g) ≤ index ∧
      X.get (g, descriptorShufflePos (laneOf l g)) =
        some ⟨1916, .shfl .idx (b32 (startupQLow l)) 0 31 recv ok⟩ ∧
      X.ShflK (g, descriptorShufflePos (laneOf l g)) 3 ∧
      At (next (setReg t 2450 recv)) 1917
        ((2450, recv) :: schedulerAbiFrame p l) ∧
      Run kernel Assumptions.all l g (next (setReg t 2450 recv))
        ((X.tr g).drop (descriptorShufflePos (laneOf l g) + 1)) o := by
  obtain ⟨s, bytes, o, hs, _, _, hIndex, hCount, hr⟩ :=
    allocationReadBeforeEventWithFrame hp hX he hw hLate
  let pos := allocationBarrierPos l g + 2
  have hGet : ((X.tr g).drop pos)[index - pos]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  have hRecovery : ∃ t, t = afterLoad s [1179] bytes ∧ At t 1912 (schedulerAbiFrame p l) := by
    cases hRead : rebuild 3 bytes with
    | error f =>
      have hf : (afterLoad s [1179] bytes).fault = some f := by simp [afterLoad, hRead]
      exact (hKind f (onlyFaultRecord hf hr hGet)).elim
    | ok v =>
      have hNext : afterLoad s [1179] bytes = next (setReg s 1179 v) := by
        rw [afterLoad_ok hs.2.1 hs.2.2.1 hRead]
        simp [next, setReg, hs.2.1, hs.2.2.1]
      have hAt : At (next (setReg s 1179 v)) 1912 ((1179, v) :: schedulerAbiFrame p l) := hs.set (by
        intro pair hm
        simp only [schedulerAbiFrame, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl <;> simp)
      exact ⟨_, hNext.symm, hAt.mono hAt.2.2.2.2.2⟩
  obtain ⟨u, hEq, hu⟩ := hRecovery
  rw [← hEq] at hr
  have hBase : u.regs 2535 = some (b32 l.sharedBase) := hu.2.2.2.2.2.1
  obtain ⟨w, hLocal, hwAt⟩ := startupQWord hp g u (hu.mono ⟨hBase, trivial⟩)
  have hKeep (r : Nat) (h : r ∈ [1062, 2535, 7203, 7506]) : w.regs r = u.regs r :=
    schedulerLocalFrame (lo := 1912) (len := 4) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hLocal hu.1.ge (by rw [hu.1]) h
  have hW : At w 1916 ((2455, b32 (startupQLow l)) :: schedulerAbiFrame p l) := hwAt.mono
    ⟨hwAt.2.2.2.2.1, (hKeep 1062 (by decide)).trans hu.2.2.2.2.1,
      (hKeep 2535 (by decide)).trans hBase,
      (hKeep 7203 (by decide)).trans hu.2.2.2.2.2.2.1,
      (hKeep 7506 (by decide)).trans hu.2.2.2.2.2.2.2.1, trivial⟩
  have hActual := localRun (by decide) (by decide) hu.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hLocal
  let hNext : Next kernel Assumptions.all l g u w
      (.shfl .idx (b32 (startupQLow l)) 0 31 (fun v _ => next (setReg w 2450 v))) :=
    ⟨run_rtg hActual, startupQShuffle hp hwAt⟩
  obtain ⟨_, v, hShfl, hFire, hRun⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨recv, ok, he, hNone⟩; cases hNone) hr (suffixNonempty he hIndex)
  obtain ⟨recv, ok, rfl, hv⟩ := hFire
  obtain rfl := Option.some.inj hv
  have hPos : pos = descriptorShufflePos (laneOf l g) := by
    simp only [pos, allocationBarrierPos, descriptorShufflePos]
    split <;> decide
  have hAt : At (next (setReg w 2450 recv)) 1917 ((2450, recv) :: schedulerAbiFrame p l) :=
    (hW.mono hW.2.2.2.2.2).set (by
      intro pair hm
      simp only [schedulerAbiFrame, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> simp)
  change X.get (g, pos) = _ at hShfl
  have hEvent : X.get (g, descriptorShufflePos (laneOf l g)) =
      some ⟨1916, .shfl .idx (b32 (startupQLow l)) 0 31 recv ok⟩ :=
    by simpa only [hW.1, hPos] using hShfl
  change ((X.tr g).take pos).countP Execution.isShfl = 3 at hCount
  exact ⟨w, recv, ok, o, hPos ▸ hIndex, hEvent, ⟨⟨_, _, _, _, _, _, _, hEvent⟩, hPos ▸ hCount⟩,
    hAt, hPos ▸ hRun⟩

/-- An actual event beyond allocation has a preceding descriptor send with the assembled
lane-zero operand. The descriptor's received value remains the value from the actual trace. -/
theorem descriptorSendBeforeEvent {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hw : warpIndex l g = 12) (hLate : 1911 < e.pc) (hKind : ∀ f, e.kind ≠ .ub f) :
    ∃ t recv ok o, descriptorShufflePos (laneOf l g) ≤ index ∧
      X.get (g, descriptorShufflePos (laneOf l g)) =
        some ⟨1916, .shfl .idx (b32 (startupQLow l)) 0 31 recv ok⟩ ∧
      X.ShflK (g, descriptorShufflePos (laneOf l g)) 3 ∧
      At (next (setReg t 2450 recv)) 1917
        ((2450, recv) :: [(1062, b32 12), (2535, b32 l.sharedBase)]) ∧
      Run kernel Assumptions.all l g (next (setReg t 2450 recv))
        ((X.tr g).drop (descriptorShufflePos (laneOf l g) + 1)) o := by
  obtain ⟨t, recv, ok, o, hi, he, hk, ht, hr⟩ :=
    descriptorSendBeforeEventWithFrame hp hX he hw hLate hKind
  exact ⟨t, recv, ok, o, hi, he, hk,
    ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, trivial⟩, hr⟩

/-- The allocator warp's fourth shuffle follows the allocation result load. -/
theorem shuffleAfterAllocation {g index pc b c : Nat} {md : ShflMode} {a r : Value} {ok : Bool}
    (hw : warpIndex l g = 12) (he : X.get (g, index) = some ⟨pc, .shfl md a b c r ok⟩)
    (hK : X.ShflK (g, index) 3) : 1911 < pc := by
  have hg : g < l.threads := event_thread_lt hX he
  have hLength : index < (X.tr g).length := len_of_get he
  have hIndex : 3 ≤ index := hK.2.symm.le.trans (countP_take_le_length _ _ _)
  obtain ⟨hf, hb⟩ := startupFenceAndBar hp hX hg hw (by omega)
  have hAfter : 5 ≤ index := by
    by_contra! h
    interval_cases index
    · rw [hf] at he
      cases he
    · rw [hb (by omega)] at he
      cases he
  obtain ⟨s, _, hs, _, _, hRun⟩ := nonzeroCommonPrefix hp hX hg
    (show 0 < warpIndex l g by rw [hw]; decide) (by omega)
  have hAt : At s 174 (baseFrame l) := hs.mono
    ⟨hw ▸ hs.2.2.2.2.1, hs.2.2.2.2.2.1, trivial⟩
  obtain ⟨u, _, hHint, hu, hTail⟩ := firstRegisterHintFromCommon hp hg (12 : Fin 16)
    hAt hRun (suffixNonempty he hAfter)
  have hAfterHint : 6 ≤ index := by
    by_contra! h
    obtain rfl : index = 5 := by omega
    rw [hHint] at he
    cases he
  obtain ⟨visits, hWalk⟩ := walkFromRun hTail
  have hMem : (⟨pc, .shfl md a b c r ok⟩ : Event) ∈ (X.tr g).drop 6 := by
    apply List.mem_of_getElem? (i := index - 6)
    rwa [List.getElem?_drop, Nat.add_sub_of_le hAfterHint]
  have hRole := roleBodyEventPcs (12 : Fin 16) hu hWalk _ hMem
  have hLow : 1908 ≤ pc := by
    change pc = 9205 ∨ 1908 ≤ pc ∧ pc < 2768 at hRole
    omega
  obtain ⟨_, hFault⟩ | ⟨_, ins, _, _, hCode, hFire⟩ := get_source hX he
  · cases hFault
  have hShfl := fires_shfl_op hFire
    (show Execution.isShfl ⟨pc, .shfl md a b c r ok⟩ = true from rfl)
  by_contra! hHigh
  interval_cases pc <;>
    simp only [Flow.code_1908, Flow.code_1909, Flow.code_1910, Flow.code_1911,
      Option.some.injEq] at hCode <;> subst ins <;> cases hShfl

private theorem fourthShuffleWord {g index pc b c : Nat} {md : ShflMode} {a r : Value} {ok : Bool}
    (hw : warpIndex l g = 12) (he : X.get (g, index) = some ⟨pc, .shfl md a b c r ok⟩)
    (hK : X.ShflK (g, index) 3) : a = b32 (startupQLow l) := by
  have hLate := shuffleAfterAllocation hp hX hw he hK
  obtain ⟨_, _, _, _, _, hSend, hOrd, _, _⟩ := descriptorSendBeforeEvent hp hX he hw hLate
    (by intro f h; cases h)
  have hIndex := shfl_index_unique hK hOrd
  rw [hIndex] at he
  have hEq := Option.some.inj (he.symm.trans hSend)
  exact (Kind.shfl.inj (congrArg Event.kind hEq)).2.1

private theorem noExitBeforeDescriptor {g : Nat} (hw : warpIndex l g = 12)
    : ¬ ShflExited X g 3 := by
  rintro ⟨index, pc, he, hCount⟩
  obtain rfl := actualExitPc hX he
  obtain ⟨_, _, _, _, hIndex, hSend, hOrd, _, _⟩ := descriptorSendBeforeEvent hp hX he hw
    (show 1911 < 9205 by decide) (by intro f h; cases h)
  have hNext := beforeTarget he hSend hIndex (show 1916 ≠ 9205 by decide)
  have hMono := countP_take_mono Execution.isShfl (X.tr g) hNext
  rw [shuffleCountAfter hSend, hOrd.2] at hMono
  simp only [Execution.isShfl, ↓reduceIte] at hMono
  omega

/-- A surviving MMA warp's first Q descriptor comes from the matching lane-zero shuffle.
Actual events suffice to recover its return and the remaining run even in a suspended prefix. -/
private theorem initialQueryDescriptorBeforeEventWithFrame {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e) (hw : warpIndex l g = 12) (hLate : 1916 < e.pc)
    (hKind : ∀ f, e.kind ≠ .ub f) :
    ∃ t o, descriptorShufflePos (laneOf l g) + 1 ≤ index ∧
      At t 1917 ((2450, b32 (startupQLow l)) :: schedulerAbiFrame p l) ∧
      Run kernel Assumptions.all l g t
        ((X.tr g).drop (descriptorShufflePos (laneOf l g) + 1)) o := by
  obtain ⟨s, recv, ok, o, hIndex, hSend, hOrd, ht, hr⟩ :=
    descriptorSendBeforeEventWithFrame hp hX he hw (by omega) hKind
  obtain ⟨_, hSource⟩ := hX.shfl g _ 3 1916 .idx (b32 (startupQLow l)) 0 31 recv ok hSend hOrd
  have hSourceLane := shflSource_idx (laneOf l g) (show 0 < 32 by decide)
  rw [hSourceLane, Nat.add_zero] at hSource
  have hg : g < l.threads := event_thread_lt hX he
  obtain ⟨hSame, _⟩ := laneZero_sameWarp (show 0 < l.block by rw [hp.block]; decide) hg
  have hWarp : warpIndex l (g - laneOf l g) = 12 := hSame.2.symm.trans hw
  have hValue : recv = b32 (startupQLow l) := by
    rcases hSource with ⟨_, _, _, _, _, _, hPeer, hWord⟩ | hExit
    · exact fourthShuffleWord hp hX hWarp hWord hPeer
    · exact (noExitBeforeDescriptor hp hX hWarp hExit).elim
  subst recv
  exact ⟨_, o, beforeTarget he hSend hIndex (by dsimp; omega), ht, hr⟩

/-- A surviving MMA warp's first Q descriptor comes from the matching lane-zero shuffle.
Actual events suffice to recover its return and the remaining run even in a suspended prefix. -/
theorem initialQueryDescriptorBeforeEvent {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e) (hw : warpIndex l g = 12) (hLate : 1916 < e.pc)
    (hKind : ∀ f, e.kind ≠ .ub f) :
    ∃ t o, descriptorShufflePos (laneOf l g) + 1 ≤ index ∧
      At t 1917 [(2450, b32 (startupQLow l)), (1062, b32 12), (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g t
        ((X.tr g).drop (descriptorShufflePos (laneOf l g) + 1)) o := by
  obtain ⟨t, o, hi, ht, hr⟩ := initialQueryDescriptorBeforeEventWithFrame hp hX he hw hLate hKind
  exact ⟨t, o, hi, ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, trivial⟩, hr⟩

omit hp hX in
private theorem mmaSchedulerSuffix {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {o : Option TState}
    (hs : 1940 < s.pc) (hr : Run kernel Assumptions.all l g s events o) :
    ∀ e ∈ events, 1940 < e.pc := by
  obtain ⟨_, hWalk⟩ := walkFromRun hr
  exact Thread.eventTailEvents (floor := 1941) (by decide +kernel) (by decide +kernel) hWalk hs

/-- An observed MMA scheduler lane read uses its in-range launch CuQ word. -/
theorem firstCuQReadFootprint {g j : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, j) = some ⟨1940, .rd a bs⟩) :
    j = descriptorShufflePos (laneOf l g) + 1 ∧ laneOf l g ≤ p.batch ∧
      a = {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4} := by
  have hRole := roleBodyPcOfEvent hp hX he (by change 173 < 1940; decide)
    (by change 1940 ∉ registerHintSites; decide)
  have hw : warpIndex l g = 12 := by
    change roleBodyPc (warpIndex l g) 1940 at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · cases h
    · split_ifs at h <;> omega
  obtain ⟨t, o, hj, ht, hr⟩ := initialQueryDescriptorBeforeEventWithFrame hp hX he hw
    (by change 1916 < 1940; decide) (by intro f h; cases h)
  obtain ⟨u, hCore, hu⟩ := startupQRegistersCore hp g t (ht.mono ⟨ht.2.2.2.2.1, trivial⟩)
  have hLocal := localRun (by decide) (by decide) ht.1 (by decide +kernel) hCore
  have hFrame {r : Nat} (hm : r ∈ [7203, 7506]) : u.regs r = t.regs r :=
    schedulerLocalFrame (lo := 1917) (len := 18) (by decide +kernel) (by decide +kernel)
      hCore ht.1.ge (by rw [ht.1]) hm
  have hU : At u 1935 [(1180, b32 (laneOf l g)), (7203, b32 p.batch), (7506, b64 p.cuQBase)] :=
    hu.mono ⟨hu.2.2.2.2.1,
      (hFrame (by decide)).trans ht.2.2.2.2.2.2.2.1,
      (hFrame (by decide)).trans ht.2.2.2.2.2.2.2.2.1, trivial⟩
  have hMore := suffixNonempty he hj
  have hPrefix := hr.after_local_nonempty (run_rtg hLocal) hMore
  by_cases hLane : laneOf l g ≤ p.batch
  · obtain ⟨v, hv, _, hNext⟩ := firstSchedulerNextWithFrame hp hLane hU
    obtain ⟨hPos, hAcc⟩ := hNext.uniqueScalarReadAt hv.1 hPrefix hj he
      (fun _ _ => mmaSchedulerSuffix)
    exact ⟨hPos, hLane, hAcc⟩
  · obtain ⟨v, hv, _, hSkip⟩ := firstSchedulerSkipWithFrame hp (Nat.lt_of_not_ge hLane) hU
    have hAt : ((X.tr g).drop (descriptorShufflePos (laneOf l g) + 1))[
        j - (descriptorShufflePos (laneOf l g) + 1)]? = some ⟨1940, .rd a bs⟩ := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hj]
      exact he
    have hPast := mmaSchedulerSuffix (by rw [hv.1]; decide)
      (hPrefix.after_local_nonempty hSkip hMore) _ (List.mem_of_getElem? hAt)
    exact (Nat.lt_irrefl 1940 hPast).elim

/-- Any later real event of an MMA lane has a replay through its first assembled Q bank. -/
theorem initialQueryBankBeforeEvent {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hw : warpIndex l g = 12) (hLate : 1916 < e.pc) (hKind : ∀ f, e.kind ≠ .ub f) :
    ∃ t o, descriptorShufflePos (laneOf l g) + 1 ≤ index ∧
      At t 1935 ((1062, b32 12) :: (9632, b32 0x8200490) :: qDescriptorFacts l 1) ∧
      Run kernel Assumptions.all l g t
        ((X.tr g).drop (descriptorShufflePos (laneOf l g) + 1)) o := by
  obtain ⟨s, o, hIndex, hs, hRun⟩ := initialQueryDescriptorBeforeEvent hp hX he hw hLate hKind
  obtain ⟨t, hLocal, ht⟩ := startupQueryBankWithRole hp g s
    (hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, trivial⟩)
  exact ⟨t, o, hIndex, ht, hRun.after_local_nonempty (run_rtg hLocal) (suffixNonempty he hIndex)⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
