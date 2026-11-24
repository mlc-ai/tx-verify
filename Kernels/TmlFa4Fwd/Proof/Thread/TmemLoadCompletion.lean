-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierRelease
public import Kernels.TmlFa4Fwd.Proof.CorrectionTmemLoads
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.SoftmaxTmem
import Lemmas.Flow.Async
import Lemmas.Flow.ContinuingEvent
import Lemmas.Flow.EventCont
import Lemmas.Flow.MemTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame

/-- A load whose checked register-consumption rule inserts an implicit load wait. -/
@[no_expose] def DataflowLoad (X : Execution) (i : EvId) : Prop :=
  ∃ site address values shape, site ∈ Assumptions.tcLdDataflowSites ∧
    X.get i = some ⟨site, .tc (.ld address values shape)⟩

private def selectedLoad (i : Instr) : Bool :=
  i.guard.isNone && match i.op with
  | .tcLd _ _ .s32x32b none => true
  | _ => false

private theorem plainLoadCode {site : Nat} (h : kernel.code[site]?.map selectedLoad = some true) :
    ∃ ds addr, kernel.code[site]? = some ⟨none, .tcLd ds addr .s32x32b none⟩ := by
  obtain ⟨ins, hc, hSelected⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨guard, op⟩ := ins
  simp only [selectedLoad, Bool.and_eq_true, Option.isNone_iff_eq_none] at hSelected
  obtain ⟨rfl, hOp⟩ := hSelected
  cases op <;> try (cases hOp)
  case tcLd ds addr shape red =>
    cases shape <;> cases red <;> cases hOp
    exact ⟨ds, addr, hc⟩

private theorem selectedDataflowCode {site : Nat} (h : site ∈ Assumptions.tcLdDataflowSites) :
    ∃ ds addr, kernel.code[site]? = some ⟨none, .tcLd ds addr .s32x32b none⟩ := by
  have audit : ∀ pc ∈ Assumptions.tcLdDataflowSites,
      kernel.code[pc]?.map selectedLoad = some true := by decide +kernel
  exact plainLoadCode (audit site h)

private theorem dataflowHook {site : Nat} (h : site ∈ Assumptions.tcLdDataflowSites) :
    Assumptions.all.any (·.tcLdWait site) = true := by
  have decoded : Assumptions.tcLdDataflowSites = List.ofFn (Softmax.scorePc .unbiased) ++
      (List.finRange 2).flatMap (fun s => List.ofFn (TmlFa4Fwd.Correction.rescaleLoadPc s)) :=
    by decide
  rw [decoded] at h
  rcases List.mem_append.mp h with hScores | hRescale
  · obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hScores
    exact Softmax.scoreWaitHook .unbiased q
  · obtain ⟨stage, _, hChunk⟩ := List.mem_flatMap.mp hRescale
    obtain ⟨chunk, rfl⟩ := List.mem_ofFn.mp hChunk
    exact TmlFa4Fwd.Correction.rescaleWaitHook stage chunk

private theorem implicitLoadContinuation {l : Launch} {g : Nat} {s u : TState}
    {site address : Nat} {vals : List Value} {shape : TcShape}
    (hSite : site ∈ Assumptions.tcLdDataflowSites)
    (hStep : EStep kernel Assumptions.all l g s ⟨site, .tc (.ld address vals shape)⟩ (some u)) :
    u.pc = site ∧ u.sub = 1 ∧ u.fault = none := by
  obtain ⟨ds, addr, hSelected⟩ := selectedDataflowCode hSite
  have hs : s.pc = site := (estep_source_pc hStep).symm
  have hf : s.fault = none := by
    cases hAt : s.fault with
    | none => rfl
    | some bad =>
      obtain ⟨tm, hOut, hFire⟩ := hStep
      have hFault : out kernel Assumptions.all l g s = .ev (.ub bad) := by simp [out, hAt]
      obtain rfl := Out.ev.inj (hOut.symm.trans hFault)
      cases hFire.2
  obtain ⟨ins, hAt, _, hFire⟩ := estep_event_source hStep
  rw [hs, hSelected] at hAt
  obtain rfl := Option.some.inj hAt.symm
  have hWait := dataflowHook hSite
  rw [show eventTmpl Assumptions.all l g s (.tcLd ds addr .s32x32b none) =
    tcLdTmpl Assumptions.all l g s (.tcLd ds addr .s32x32b none) from rfl] at hFire
  simp only [tcLdTmpl, hs, hWait, ↓reduceIte] at hFire
  split at hFire
  · rw [tcTmpl_tcLd_none (by intro _ h; cases h)] at hFire
    cases hAddr : readBits l g s 32 (.reg addr) <;>
      simp only [ofExec, hAddr, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hFire
    all_goals split_ifs at hFire <;> simp only [Tmpl.thenWaitLd, Fires, reduceCtorEq] at hFire
    all_goals try (simp at hFire; done)
    obtain ⟨values, _, _, hAfter⟩ := hFire
    have hNext := Option.some.inj hAfter
    exact ⟨congrArg TState.pc hNext, congrArg TState.sub hNext,
      (congrArg TState.fault hNext).trans ((setRegs_skel (next s) ds values).2.2.2.trans hf)⟩
  · simp [Fires] at hFire

/-- The actual event after a selected load is its implicit load wait. -/
theorem dataflowLoadWait {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i : Nat}
    (hLoad : DataflowLoad X (g,i)) (hNext : i + 1 < (X.tr g).length) :
    ∃ site, X.get (g,i+1) = some ⟨site, .tc .waitLd⟩ := by
  obtain ⟨site, address, vals, shape, hSite, he⟩ := hLoad
  obtain ⟨_, hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨s, u, hStep, hTail⟩ := hr.after_event he hNext
  obtain ⟨hu, hSub, hFault⟩ := implicitLoadContinuation hSite hStep
  obtain ⟨ds, addr, hc⟩ := selectedDataflowCode hSite
  have hOut : out kernel Assumptions.all l g u = .ev (.tc .waitLd {next u with sub := 0}) := by
    rw [out_event hFault (hu.symm ▸ hc) rfl rfl]
    simp only [eventTmpl, tcLdTmpl, hu, dataflowHook hSite, hSub, Nat.one_ne_zero, ↓reduceIte]
  change Run kernel Assumptions.all l g u ((X.tr g).drop (i+1)) _ at hTail
  rw [List.drop_eq_getElem_cons hNext] at hTail
  obtain ⟨_, hFire, _⟩ := Next.continuing_event ⟨.refl, hOut⟩ (by
    intro h
    cases h.2) hTail
  refine ⟨site, ?_⟩
  change (X.tr g)[i+1]? = _
  rw [List.getElem?_eq_getElem hNext, hFire.1, hu]

theorem DataflowLoad.of_decoded {X : Execution} {i : EvId} {site address : Nat}
    {vals : List Value} {shape : TcShape} (hs : site ∈ Assumptions.tcLdDataflowSites)
    (he : X.get i = some ⟨site, .tc (.ld address vals shape)⟩) : DataflowLoad X i :=
  ⟨site, address, vals, shape, hs, he⟩

/-- A selected load has completed before any actual release attempt in its CTA. -/
theorem dataflowLoadCompletedBeforeRelease {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i d : EvId} (hScope : i.1 / l.block = d.1 / l.block)
    (hLoad : DataflowLoad X i) (hd : Deallocation X d) :
    TcMma.WaitBefore l X .waitLd i d := by
  obtain ⟨g, index⟩ := i
  have hData : TensorDataEvent X (g,index) := by
    obtain ⟨_, _, _, _, _, hRead⟩ := hLoad
    exact ⟨_, hRead, .inl rfl⟩
  have hNext := tensorDataResumedBeforeDeallocation hp hX hScope hData hd
  obtain ⟨site, hWait⟩ := dataflowLoadWait hX hLoad hNext
  refine ⟨(g,index+1), ⟨site, hWait⟩, rfl, by omega, .inl ?_⟩
  exact tensorDataBeforeDeallocation hp hX hScope ⟨_, hWait, .inl rfl⟩ hd

private def localMove (ins : Instr) : Bool :=
  ins.guard.isNone && ins.op.isLocal && match ins.op with
  | .move _ => true
  | _ => false

private def unguardedLoadWait : Instr → Bool
  | ⟨none, .tcWaitLd⟩ => true
  | _ => false

private def explicitWindow (site : Nat) : Bool :=
  (kernel.code[site]?.map selectedLoad == some true) &&
    !Assumptions.tcLdDataflowSites.contains site &&
    (List.finRange 4).all (fun offset =>
      !Assumptions.swExp2Sites.contains (site + 1 + offset.val) &&
      (kernel.code[site + 1 + offset.val]?.map localMove == some true)) &&
    (kernel.code[site+5]?.map unguardedLoadWait == some true)

/-- A load whose next event is a decoded wait after four local moves. -/
@[no_expose] def ExplicitWaitLoad (X : Execution) (i : EvId) : Prop :=
  ∃ site address vals shape, explicitWindow site = true ∧
    X.get i = some ⟨site, .tc (.ld address vals shape)⟩

private theorem firstExplicitWaits : (List.finRange 16).all
    (fun k => explicitWindow (TmlFa4Fwd.Correction.finalizeLoadPc 0 k)) = true := by kernel_rfl

private theorem secondExplicitWaits : (List.finRange 16).all
    (fun k => explicitWindow (TmlFa4Fwd.Correction.finalizeLoadPc 1 k)) = true := by kernel_rfl

theorem ExplicitWaitLoad.finalization {X : Execution} {i : EvId} {address : Nat}
    {vals : List Value} {shape : TcShape} (stage : Fin 2) (chunk : Fin 16)
    (he : X.get i = some
      ⟨TmlFa4Fwd.Correction.finalizeLoadPc stage chunk, .tc (.ld address vals shape)⟩) :
    ExplicitWaitLoad X i := by
  fin_cases stage
  · exact ⟨_, _, _, _, List.all_eq_true.mp firstExplicitWaits chunk (List.mem_finRange _), he⟩
  · exact ⟨_, _, _, _, List.all_eq_true.mp secondExplicitWaits chunk (List.mem_finRange _), he⟩

private theorem explicitMoveCode {site pc : Nat}
    (h : explicitWindow site = true) (hLo : site+1 ≤ pc) (hHi : pc < site+5) :
    ∃ mv, kernel.code[pc]? = some ⟨none, .move mv⟩ ∧
      (Op.move mv).isLocal = true ∧ pc ∉ Assumptions.swExp2Sites := by
  simp only [explicitWindow, Bool.and_eq_true] at h
  let offset : Fin 4 := ⟨pc - (site+1), by omega⟩
  have ht := List.all_eq_true.mp h.1.2 offset (List.mem_finRange _)
  have hAt : site+1+offset.val = pc := Nat.add_sub_of_le hLo
  rw [hAt] at ht
  obtain ⟨hSeg, hMove⟩ := Bool.and_eq_true_iff.mp ht
  have hNo : pc ∉ Assumptions.swExp2Sites := by simpa using hSeg
  obtain ⟨⟨guard, op⟩, hc, hm⟩ := Option.map_eq_some_iff.mp (beq_iff_eq.mp hMove)
  simp only [localMove, Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨⟨rfl, hl⟩, hp⟩ := hm
  cases op <;> try (cases hp)
  exact ⟨_, hc, hl, hNo⟩

private theorem explicitWaitCode {site : Nat} (h : explicitWindow site = true) :
    kernel.code[site+5]? = some ⟨none, .tcWaitLd⟩ := by
  obtain ⟨⟨guard, op⟩, hc, ht⟩ := Option.map_eq_some_iff.mp
    (beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2)
  cases guard <;> cases op <;> simp [unguardedLoadWait] at ht hc
  exact hc

private theorem explicitWindowTau {l : Launch} {g site : Nat} {t u : TState}
    (h : explicitWindow site = true) (hLo : site+1 ≤ t.pc) (hHi : t.pc ≤ site+5)
    (ht : Tau kernel Assumptions.all l g t u) : site+1 ≤ u.pc ∧ u.pc ≤ site+5 := by
  obtain ⟨ins, hc, _, hSource⟩ := Softmax.tauScoreSource ht
  by_cases hEnd : t.pc = site+5
  · rw [hEnd, explicitWaitCode h] at hc
    obtain rfl := Option.some.inj hc.symm
    rcases hSource with ⟨_, hg⟩ | ⟨_, hl, _⟩
    · cases hg
    · cases hl
  obtain ⟨mv, hCode, _, hNo⟩ := explicitMoveCode h hLo (by omega)
  obtain rfl := Option.some.inj (hc.symm.trans hCode)
  rcases hSource with ⟨_, hGuard⟩ | ⟨_, _, hExec⟩
  · cases hGuard
  rcases Softmax.scoreExecLocal hExec with hFrame | ⟨_, hs, _, _⟩
  · have hNext : u.pc = t.pc + 1 := by
      simpa only [nextPc, BrxTarget, or_false] using hFrame.pc
    omega
  · exact (hNo hs).elim

private theorem explicitWindowEvent {p : Params} {l : Launch} {m : Mem0} {g site : Nat}
    {s u : TState} {e : Event} (hp : Pre p l m) (h : explicitWindow site = true)
    (hLo : site+1 ≤ s.pc) (hHi : s.pc ≤ site+5)
    (he : EStep kernel Assumptions.all l g s e (some u)) : e.kind = .tc .waitLd := by
  obtain ⟨ins, hc, hNotLocal, hFire⟩ := estep_event_source he
  by_cases hMark : s.pc = site+5
  · rw [hMark, explicitWaitCode h] at hc
    obtain rfl := Option.some.inj hc.symm
    exact congrArg Event.kind (fires_tcWaitLd (by rw [hp.block]) hFire)
  obtain ⟨mv, hCode, hLocal, _⟩ := explicitMoveCode h hLo (by omega)
  obtain rfl := Option.some.inj (hc.symm.trans hCode)
  rw [hLocal] at hNotLocal
  cases hNotLocal

private theorem explicitWindowTrace {p : Params} {l : Launch} {m : Mem0} {g site : Nat}
    {s u : TState} {events : List Event} (hp : Pre p l m) (h : explicitWindow site = true)
    (hr : TraceReach kernel Assumptions.all l g s events u)
    (hStart : site+1 ≤ s.pc ∧ s.pc ≤ site+5) :
    (∃ e ∈ events, e.kind = .tc .waitLd) ∨ (site+1 ≤ u.pc ∧ u.pc ≤ site+5) := by
  induction hr with
  | refl => exact .inr hStart
  | tau ht _ ih => exact ih (explicitWindowTau h hStart.1 hStart.2 ht)
  | event he _ _ => exact .inl ⟨_, by simp, explicitWindowEvent hp h hStart.1 hStart.2 he⟩

private theorem explicitContinuation {l : Launch} {g site address : Nat} {s u : TState}
    {vals : List Value} {shape : TcShape} (h : explicitWindow site = true)
    (he : EStep kernel Assumptions.all l g s ⟨site, .tc (.ld address vals shape)⟩ (some u)) :
    u.pc = site+1 := by
  simp only [explicitWindow, Bool.and_eq_true] at h
  obtain ⟨ds, addr, hCode⟩ := plainLoadCode (beq_iff_eq.mp h.1.1.1)
  obtain ⟨ins, hc, _, hFire⟩ := estep_event_source he
  have hs : s.pc = site := (estep_source_pc he).symm
  rw [hs, hCode] at hc
  obtain rfl := Option.some.inj hc.symm
  have hNo : Assumptions.tcLdDataflowSites.contains site = false := by simpa using h.1.1.2
  have hOff : Assumptions.all.any (·.tcLdWait site) = false :=
    (Assumptions.all_tcLdWait site).trans
      (congrArg (· && Assumption.ldConsumedAt kernel site) hNo)
  have hHook : Assumptions.all.any (·.tcLdWait s.pc) = false := hs.symm ▸ hOff
  obtain ⟨_, ws, _, _, rfl⟩ := fires_tcLd (by intro _ hb; cases hb) hFire hHook
  exact (setRegs_pc (next s) ds ws).trans (by simp [next, hs])

/-- An explicit output load has completed before any actual release attempt in its CTA. -/
theorem explicitLoadCompletedBeforeRelease {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i d : EvId} (hScope : i.1 / l.block = d.1 / l.block)
    (hLoad : ExplicitWaitLoad X i) (hd : Deallocation X d) :
    TcMma.WaitBefore l X .waitLd i d := by
  obtain ⟨g, index⟩ := i
  obtain ⟨site, _, _, _, hWindow, he⟩ := hLoad
  have hData : TensorDataEvent X (g,index) := ⟨_, he, .inl rfl⟩
  obtain ⟨finish, mode, hAfter, hFinal⟩ :=
    (tensorDataFinalArrivalBeforeDeallocation hp hX hScope hData hd).1
  obtain ⟨source, _, hFinalGet⟩ := hFinal.decoded
  have hLength : finish < (X.tr g).length := PTX.len_of_get hFinalGet
  obtain ⟨_, hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨_, u, hStep, hTail⟩ := hr.after_event he (by omega)
  let stop := finish-(index+1)
  have hTerm : ((X.tr g).drop (index+1))[stop]? = some ⟨source, .bar 2 (some 416) mode⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le (by omega : index+1 ≤ finish)]
    exact hFinalGet
  obtain ⟨v, _, hReach, hExit⟩ := hTail.before_event hTerm
  have hu := explicitContinuation hWindow hStep
  rcases explicitWindowTrace hp hWindow hReach (by omega) with ⟨e, he, hk⟩ | ⟨hLo,hHi⟩
  · obtain ⟨k, hIndex⟩ := List.mem_iff_getElem?.mp he
    have hLt : k < stop := by
      have hLen := (List.getElem?_eq_some_iff.mp hIndex).1
      simp only [List.length_take, Nat.lt_min] at hLen
      omega
    rw [List.getElem?_take_of_lt hLt, List.getElem?_drop] at hIndex
    obtain ⟨waitSite, kind⟩ := e
    cases hk
    have hWait : X.get (g,index+1+k) = some ⟨waitSite, .tc .waitLd⟩ := hIndex
    exact ⟨_, ⟨waitSite, hWait⟩, rfl, by omega, .inl
      (tensorDataBeforeDeallocation hp hX hScope ⟨_, hWait, .inl rfl⟩ hd)⟩
  · have hv : source = v.pc := estep_source_pc hExit
    rcases get_source hX hFinalGet with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
    · cases hf
    have hBar := fires_bar_op hf rfl
    rw [hv] at hc
    by_cases hEq : v.pc = site+5
    · rw [hEq, explicitWaitCode hWindow] at hc
      obtain rfl := Option.some.inj hc.symm
      cases hBar
    · obtain ⟨mv, hCode, _, _⟩ := explicitMoveCode hWindow hLo (by omega)
      obtain rfl := Option.some.inj (hc.symm.trans hCode)
      cases hBar

end PTX.Kernels.TmlFa4Fwd.Thread
