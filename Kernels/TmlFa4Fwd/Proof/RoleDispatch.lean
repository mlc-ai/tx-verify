-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderExit
public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
public import Kernels.TmlFa4Fwd.Proof.LoaderRingFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Kernels.TmlFa4Fwd.Proof.MmaLoopRank
public import Kernels.TmlFa4Fwd.Proof.PrologueBroadcast
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueInitChain
public import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueRoles
public import Kernels.TmlFa4Fwd.Proof2.Startup.Abi
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopLocal
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Lemmas.Flow.Determinism
public import Lemmas.Register.RegisterFrame
public import Lemmas.Flow.Scalars
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.Regs
public import Lemmas.Kernel.ReadValue
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Flow.WarpScan
public import Lemmas.Flow.TauFrame
public import Lemmas.Step.Released
public import Lemmas.Step.ProtectedReadProgress
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Bits
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Lemmas.Step.WarpVote
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Lemmas.Flow.Local
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Lemmas.Step.WarpShfl
public import Lemmas.Flow.WriteSpace
public import Lemmas.Snoc.ControlEffect
public import Kernels.TmlFa4Fwd.Proof.CuQReadBytes
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.MmaRoleCut
public import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame
public import Kernels.TmlFa4Fwd.Proof.NoCancellation
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
public import Kernels.TmlFa4Fwd.Proof.OutputWritebackSpec
public import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
public import Kernels.TmlFa4Fwd.Proof.PrologueScheduler
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Proof.SchedulerBallot
public import Kernels.TmlFa4Fwd.Proof.SchedulerCoordinates
public import Kernels.TmlFa4Fwd.Proof.SchedulerCursor
public import Kernels.TmlFa4Fwd.Proof.SchedulerCuts
public import Kernels.TmlFa4Fwd.Proof.SchedulerDrainWords
public import Kernels.TmlFa4Fwd.Proof.SchedulerFrame
public import Kernels.TmlFa4Fwd.Proof.SchedulerGroupPrefix
public import Kernels.TmlFa4Fwd.Proof.SchedulerProtection
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanGuard
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanObservations
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionObservations
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionPath
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionReads
public import Kernels.TmlFa4Fwd.Proof.SchedulerStartWord
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerBallotProgress
public import Kernels.TmlFa4Fwd.Proof.WarpFollows
public import Kernels.TmlFa4Fwd.Proof.WarpOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Mma Prologue

noncomputable section

private def foreignPc (pc : Nat) : Prop :=
  1904 ≤ pc ∧ (pc < 2768 ∨ 3099 ≤ pc)

private instance foreignPcDec (pc : Nat) : Decidable (foreignPc pc) :=
  inferInstanceAs (Decidable (1904 ≤ pc ∧ (pc < 2768 ∨ 3099 ≤ pc)))

private def foreignCode (pc : Nat) (ins : Instr) : Bool :=
  !decide (foreignPc pc) || (
    (ins.guard.isNone || decide (foreignPc (pc + 1))) &&
    (ins.op.isLocal || (ordinaryEvent ins.op && decide (foreignPc (pc + 1)))) &&
    match ins.op with
    | .brx .. => false
    | _ => decide (foreignPc (nextPc ins.op pc)))

private theorem foreignCodeAt {pc : Nat} {i : Instr} (hp : foreignPc pc)
    (hc : kernel.code[pc]? = some i) : foreignCode pc i = true := by
  have hAll : ((kernel.code.drop 1904).zipIdx 1904).all
      (fun (ins, site) => foreignCode site ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hGet : ((kernel.code.drop 1904).zipIdx 1904)[pc - 1904]? = some (i, pc) := by
    rw [List.getElem?_zipIdx, List.getElem?_drop, Nat.add_sub_of_le hp.1, hc]
    rfl
  exact List.all_eq_true.mp hAll _ (List.mem_of_getElem? hGet)

private theorem foreignSegment {s u : TState} {se : SegMatch CuteSlot}
    (hSite : s.pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel s.pc = some se)
    (hu : Assumptions.execSwExp2 se s = .ok u) : foreignPc u.pc := by
  have hAll : Assumptions.swExp2Sites.all (fun pc => match cuteExp2.matchAt kernel pc with
      | none => false | some x => decide (foreignPc x.stop)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hCode := List.all_eq_true.mp hAll _ hSite
  rw [hm] at hCode
  have hp := (Softmax.scoreSegmentFrame hu).1
  exact hp.symm ▸ of_decide_eq_true hCode

private theorem foreignStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hp : foreignPc s.pc) (he : WStep kernel Assumptions.all l g s e u) :
    foreignPc u.pc := by
  rcases he with ⟨_, ht⟩ | ⟨ev, _, he⟩
  · obtain ⟨i, hc, _, hSource⟩ := Softmax.tauScoreSource ht
    have hCode := foreignCodeAt hp hc
    simp only [foreignCode, hp, decide_true, Bool.not_true, Bool.false_or,
      Bool.and_eq_true] at hCode
    rcases hSource with ⟨rfl, hGuard⟩ | ⟨_, _, hLocal⟩
    · have hSafe := hCode.1.1
      simp only [Bool.or_eq_true] at hSafe
      rcases hSafe with hNone | hAfter
      · rw [Option.isNone_iff_eq_none.mp hNone] at hGuard
        cases hGuard
      · exact of_decide_eq_true hAfter
    · rcases Softmax.scoreExecLocal hLocal with hCore | ⟨se, hSite, hm, hu⟩
      · have hNext := hCore.pc
        cases hi : i.op <;> simp only [hi, BrxTarget, or_false] at hNext hCode
        all_goals first
          | exact hNext.symm ▸ of_decide_eq_true hCode.2
          | exact Bool.noConfusion hCode.2
      · exact foreignSegment hSite hm hu
  · obtain ⟨i, hc, hl, hFire⟩ := estep_event_source he
    have hCode := foreignCodeAt hp hc
    simp only [foreignCode, hp, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq, hl] at hCode
    rcases callbackFrame_fires (ordinaryEventFrame hCode.1.2.1) hFire with h | h
    · exact h.symm ▸ hp
    · exact h.symm ▸ hCode.1.2.2

private theorem foreignWalk {l : Launch} {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} (hs : foreignPc s.pc)
    (hWalk : Walk kernel Assumptions.all l g s events visits) :
    ∀ e ∈ events, foreignPc e.pc := by
  induction hWalk with
  | stop => simp
  | tau ht hW ih => exact ih (foreignStep hs (.inl ⟨rfl, ht⟩))
  | ev he hW ih =>
    intro e hm
    rcases List.mem_cons.mp hm with rfl | hMem
    · exact (estep_source_pc he).symm ▸ hs
    · exact ih (foreignStep hs (.inr ⟨_, rfl, he⟩)) _ hMem
  | last he =>
    intro e hm
    obtain rfl := List.mem_singleton.mp hm
    exact (estep_source_pc he).symm ▸ hs

private theorem noForeignEpilogueFromCommon {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (hg : g < l.threads) (warp : Fin 16) (hLt : warp.val < 14)
    (hNe : warp.val ≠ 13) {s : TState}
    (hs : At s 174 [(1062, b32 warp.val), (2535, b32 l.sharedBase)])
    {es : List Event} {o : Option TState} (hr : Run kernel Assumptions.all l g s es o)
    {e : Event} (hm : e ∈ es) (hLo : 2768 ≤ e.pc) (hHi : e.pc < 3099) : False := by
  obtain ⟨u, hDispatch, hu⟩ := dispatchRunFromCommon hp warp hg hs
  have hPc : foreignPc u.pc := by
    rw [hu.1, dispatchParamPc, ite_eq_right (Nat.not_le_of_gt hLt), ite_eq_right hNe]
    by_cases hMma : warp.val = 12
    · rw [ite_eq_left hMma]; decide
    · rw [ite_eq_right hMma]
      by_cases hSoftmax : warp.val < 8
      · rw [ite_eq_left hSoftmax]; decide
      · rw [ite_eq_right hSoftmax]; decide
  obtain ⟨vs, hWalk⟩ := walkFromRun hr
  rcases advanceWalkLocals hDispatch hWalk with hNil | ⟨_, _, _, hRole⟩
  · rw [hNil] at hm
    cases hm
  · have hSafe := foreignWalk hPc hRole e hm
    simp only [foreignPc] at hSafe
    omega

/-- A thread with a recorded event beyond startup has the matching warp index and shared
base at the common dispatch, with the observed event in the remaining trace. -/
theorem commonDispatchOfLateEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g index : Nat}
    (hg : g < l.threads) {e : Event} (he : X.get (g, index) = some e) (hLate : 173 < e.pc) :
    ∃ n t o, n ≤ index ∧ At t 174 [(1062, b32 (warpIndex l g)), (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop n) o := by
  cases Nat.eq_zero_or_pos (warpIndex l g) with
  | inl hZero =>
    obtain ⟨n, t, o, hn, ht, hr⟩ := warp0CommonPrefixOfLateEvent hp hX hg hZero he hLate
    have hRegs := ht.2.2.2.2
    exact ⟨n, t, o, hn, ht.mono
      ⟨hZero.symm ▸ hRegs.1, holds_mem hRegs (by simp [initFacts, initAddresses]), trivial⟩, hr⟩
  | inr hNonzero =>
    obtain ⟨t, o, hn, ht, hr⟩ := nonzeroCommonPrefixOfLateEvent hp hX hg hNonzero he hLate
    exact ⟨5, t, o, hn, ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩, hr⟩

theorem epilogueWarpOfNonLoaderShared {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {e : Event}
    (hGet : X.get i = some e) (hLo : 2768 ≤ e.pc) (hHi : e.pc < 3099)
    (hNonLoader : warpIndex l i.1 < 14) : warpIndex l i.1 = 13 := by
  by_contra hNe
  have hg := Step.CtaBar.thread_lt_of_get hX hGet
  have hLate : 173 < e.pc := by omega
  obtain ⟨n, t, o, hn, ht, hr⟩ := commonDispatchOfLateEvent hp hX hg hGet hLate
  have hMem : e ∈ (X.tr i.1).drop n := by
    apply List.mem_of_getElem? (i := i.2 - n)
    rw [List.getElem?_drop, Nat.add_sub_of_le hn]
    exact hGet
  let warp : Fin 16 := ⟨warpIndex l i.1, warpIndex_lt hp i.1⟩
  exact noForeignEpilogueFromCommon hp hg warp hNonLoader hNe ht hr hMem hLo hHi

/-- A loader at its common egress has only the terminal return left in its walk. -/
theorem loaderTailEventPcs {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (warp : Fin 2)
    (hs : At s 1901 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (hw : Walk kernel Assumptions.all l g s es vs) :
    ∀ e ∈ es, e.pc = 9205 := by
  obtain ⟨u, hPc, hNext⟩ := Loader.loaderRoleExit (g := g) warp hs
  have hOut := hNext.stop
  have hStop : Stops kernel Assumptions.all l g u := ⟨_, hOut⟩
  suffices tail : ∀ (t : TState) (es : List Event) (vs : List Visit),
      Walk kernel Assumptions.all l g t es vs →
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u →
      ∀ e ∈ es, e.pc = 9205 from tail s es vs hw hNext.steps
  clear hs hNext
  intro t es vs hw ht
  induction hw with
  | stop => simp
  | tau hTau _ ih =>
    rcases Relation.ReflTransGen.cases_head ht with rfl | ⟨_, h, hRest⟩
    · exact (not_tau_of_stops hStop hTau).elim
    · obtain rfl := tau_det h hTau
      exact ih hRest
  | ev he _ =>
    obtain rfl := stop_unique .refl ht (stops_of_estep he) hStop
    obtain ⟨m, hm, hf⟩ := he
    rw [hOut] at hm
    obtain rfl := Out.ev.inj hm
    cases hf.2
  | last he =>
    obtain rfl := stop_unique .refl ht (stops_of_estep he) hStop
    intro e hm
    obtain rfl := List.mem_singleton.mp hm
    rw [estep_source_pc he, hPc]

/-- A closed loader region can only emit events inside that region and at its return. -/
theorem loaderWalkEventRange {l : Launch} {g lower : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (warp : Fin 2) (hLower : 174 ≤ lower)
    (ht : lower ≤ s.pc ∧ s.pc ≤ 1901) (hShape : Loader.RingShape s)
    (hRegs : Holds s.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (hCode : ∀ bound, ((kernel.code.drop lower).take (1901 - lower)).all
      (fun i => Loader.loaderPipelineCutOp lower 1901 bound [2535, 1062] i.op) = true)
    (hw : Walk kernel Assumptions.all l g s es vs) :
    ∀ e ∈ es, lower ≤ e.pc ∧ (e.pc ≤ 1901 ∨ e.pc = 9205) := by
  let F := [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]
  have advance {t u : TState} {e : Option Event} {es : List Event} {vs : List Visit}
      (ht : lower ≤ t.pc ∧ t.pc ≤ 1901) (hShape : Loader.RingShape t)
      (hRegs : Holds t.regs F) (hClean : t.fault = none)
      (hStep : WStep kernel Assumptions.all l g t e u)
      (hWalk : Walk kernel Assumptions.all l g t (e.toList ++ es)
        (visit kernel l g t e :: vs))
      (ih : (lower ≤ u.pc ∧ u.pc ≤ 1901) → Loader.RingShape u → Holds u.regs F →
        ∀ ev ∈ es, lower ≤ ev.pc ∧ (ev.pc ≤ 1901 ∨ ev.pc = 9205))
      (hEvent : ∀ ev ∈ e.toList, ev.pc = t.pc) :
      ∀ ev ∈ e.toList ++ es, lower ≤ ev.pc ∧ (ev.pc ≤ 1901 ∨ ev.pc = 9205) := by
    by_cases hTail : t.pc = 1901
    · intro ev hm
      have hPc := loaderTailEventPcs warp
        (Loader.pipelineAtCut hTail hShape hRegs hClean ⟨_, Flow.code_1901, rfl⟩) hWalk ev hm
      exact ⟨by omega, .inr hPc⟩
    · have hBefore : t.pc < 1901 := by omega
      obtain ⟨hLower, hUpper, hShape', hRegs'⟩ := Loader.pipelineCutStep
        hLower (by decide : 1901 ≤ 1901) ⟨ht.1, hBefore⟩
        (hCode u.pc) hStep hShape hRegs
      intro ev he
      rcases List.mem_append.mp he with hFirst | hRest
      · exact (hEvent ev hFirst).symm ▸ ⟨ht.1, .inl ht.2⟩
      · exact ih ⟨hLower, hUpper.resolve_right (Nat.lt_irrefl _)⟩ hShape' hRegs' ev hRest
  induction hw with
  | stop => simp
  | tau hTau hW ih =>
    obtain ⟨_, _, hCl, _⟩ := Softmax.tauScoreSource hTau
    exact advance ht hShape hRegs hCl (.inl ⟨rfl, hTau⟩) (.tau hTau hW) ih (by simp)
  | @ev t u e es vs he hW ih =>
    have hCl : t.fault = none := by
      obtain ⟨tm, ho, hf⟩ := he
      cases ha : t.fault with
      | none => rfl
      | some f =>
        simp only [out, ha, Out.ev.injEq] at ho
        subst tm
        cases hf.2
    exact advance ht hShape hRegs hCl (.inr ⟨_, rfl, he⟩) (.ev he hW) ih
      (by intro ev hm; obtain rfl := List.mem_singleton.mp hm; exact estep_source_pc he)
  | last he =>
    intro e hm
    obtain rfl := List.mem_singleton.mp hm
    exact (estep_source_pc he).symm ▸ ⟨ht.1, .inl ht.2⟩

/-- Loader events occur in their initial code region or at the terminal return. -/
theorem loaderWalkEventPcs {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (warp : Fin 2)
    (hs : At s 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (hw : Walk kernel Assumptions.all l g s es vs) :
    ∀ e ∈ es, e.pc ≤ 1901 ∨ e.pc = 9205 := by
  intro e he
  exact (loaderWalkEventRange (lower := 174) warp (by decide) (by rw [hs.1]; decide)
    (Loader.ringShapeOfAt hs) hs.2.2.2.2
    (by intro bound; set_option maxRecDepth 100000 in kernel_rfl) hw e he).2

/-- Only warp 13 can issue events inside the epilogue role. -/
theorem issuerWarpOfEpiloguePc {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {e : Event}
    (hGet : X.get i = some e) (hLo : 2768 ≤ e.pc) (hEnd : e.pc < 3099) :
    warpIndex l i.1 = 13 := by
  by_cases hNonLoader : warpIndex l i.1 < 14
  · exact epilogueWarpOfNonLoaderShared hp hX hGet hLo hEnd hNonLoader
  exfalso
  have hHi := warpIndex_lt hp i.1
  have hLow := Nat.le_of_not_gt hNonLoader
  let warp : Fin 2 := ⟨warpIndex l i.1 - 14, by omega⟩
  have hIndex : 14 + warp.val = warpIndex l i.1 := Nat.add_sub_of_le hLow
  have hg := Step.CtaBar.thread_lt_of_get hX hGet
  have hLate : 173 < e.pc := by omega
  obtain ⟨n, t, o, hn, ht, hr⟩ := commonDispatchOfLateEvent hp hX hg hGet hLate
  have hAt : At t 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] :=
    ht.mono ⟨ht.2.2.2.2.2.1, hIndex.symm ▸ ht.2.2.2.2.1, trivial⟩
  obtain ⟨_, hW⟩ := walkFromRun hr
  have hMem : e ∈ (X.tr i.1).drop n := by
    apply List.mem_of_getElem? (i := i.2 - n)
    rw [List.getElem?_drop, Nat.add_sub_of_le hn]
    exact hGet
  have hSafe := loaderWalkEventPcs warp hAt hW e hMem
  omega

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
