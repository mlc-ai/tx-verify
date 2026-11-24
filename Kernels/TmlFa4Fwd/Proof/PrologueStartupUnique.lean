-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Kernels.TmlFa4Fwd.Flow.Code.Part002
public import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Assumption PTX.Proof PTX.Flow PTX.EventFrame

private def staysPastStartup (op : Op) : Bool :=
  match op with
  | .bra dest _ => decide (174 ≤ dest)
  | .brx .. => false
  | _ => true

private theorem afterStartupCode :
    (kernel.code.drop 174).all (fun i => staysPastStartup i.op) = true := by
  decide +kernel

private theorem afterStartupSegments :
    Assumptions.swExp2Sites.all (fun pc => match cuteExp2.matchAt kernel pc with
      | none => false | some m => decide (174 ≤ m.stop)) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem returningEventCode :
    kernel.code.all (fun i => i.op.isLocal || Epilogue.ordinaryEvent i.op) = true := by
  decide +kernel

private theorem tauStaysPastStartup {l : Launch} {g : Nat} {s u : TState}
    (hs : 174 ≤ s.pc) (ht : Tau kernel Assumptions.all l g s u) : 174 ≤ u.pc := by
  obtain ⟨i, hc, _, hStep⟩ := Softmax.tauScoreSource ht
  have hAt : (kernel.code.drop 174)[s.pc-174]? = some i := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le hs]
  have hCode := List.all_eq_true.mp afterStartupCode _ (List.mem_of_getElem? hAt)
  rcases hStep with ⟨rfl, _⟩ | ⟨_, _, hExec⟩
  · change 174 ≤ s.pc+1
    omega
  · rcases Softmax.scoreExecLocal hExec with hLocal | ⟨m, hSite, hm, hRun⟩
    · have hNext := hLocal.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hNext
      all_goals try omega
      case bra target flag =>
        have hTarget : 174 ≤ target := by simpa only [ho, staysPastStartup, decide_eq_true_eq]
          using hCode
        omega
      case brx => simp [ho, staysPastStartup] at hCode
    · have hStop := List.all_eq_true.mp afterStartupSegments _ hSite
      rw [hm] at hStop
      rw [(Softmax.scoreSegmentFrame hRun).1]
      exact of_decide_eq_true hStop

private def startupForward (p : Instr × Nat) : Bool :=
  match p.1.op with
  | .bra dest _ => decide (p.2 < dest)
  | .brx .. => false
  | _ => true

private theorem startupForwardCode : (kernel.code.take 174).zipIdx.all startupForward = true := by
  decide +kernel

private theorem tauStaysAboveStartupPc {l : Launch} {g lower : Nat} {s u : TState}
    (hLower : lower ≤ 174) (hs : lower ≤ s.pc)
    (ht : Tau kernel Assumptions.all l g s u) : lower ≤ u.pc := by
  by_cases hLate : 174 ≤ s.pc
  · exact hLower.trans (tauStaysPastStartup hLate ht)
  have hEarly : s.pc < 174 := by omega
  obtain ⟨i, hc, _, hStep⟩ := Softmax.tauScoreSource ht
  have hc' : (kernel.code.take 174)[s.pc]? = some i := by
    rwa [List.getElem?_take_of_lt hEarly]
  have hCode := List.all_eq_true.mp startupForwardCode _
    (List.mk_mem_zipIdx_iff_getElem?.mpr hc')
  rcases hStep with ⟨rfl, _⟩ | ⟨_, _, hExec⟩
  · change lower ≤ s.pc+1
    omega
  · rcases Softmax.scoreExecLocal hExec with hLocal | ⟨m, hSite, hm, hRun⟩
    · have hNext := hLocal.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hNext
      all_goals try omega
      case bra target flag =>
        have hTarget : s.pc < target := by
          simpa only [startupForward, ho, decide_eq_true_eq] using hCode
        omega
      case brx => simp [startupForward, ho] at hCode
    · have hStop := List.all_eq_true.mp afterStartupSegments _ hSite
      rw [hm] at hStop
      rw [(Softmax.scoreSegmentFrame hRun).1]
      exact hLower.trans (of_decide_eq_true hStop)

private theorem returningPc {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc ∨ u.pc = s.pc+1 := by
  obtain ⟨i, hc, hLocal, hf⟩ := estep_event_source he
  have hOrd := List.all_eq_true.mp returningEventCode _ (List.mem_of_getElem? hc)
  exact callbackFrame_fires
    (Epilogue.ordinaryEventFrame (by simpa only [hLocal, Bool.false_or] using hOrd)) hf

/-- Once the startup cursor reaches an instruction, the trace cannot return to an earlier
startup instruction. Later role loops stay beyond the whole startup. -/
theorem runAtOrPastStartupPc {l : Launch} {g lower : Nat} {s : TState}
    {events : List Event} {o : Option TState} (hBound : lower ≤ 174) (hs : lower ≤ s.pc)
    (hr : Run kernel Assumptions.all l g s events o) : ∀ e ∈ events, lower ≤ e.pc := by
  have localPath {t u : TState} (ht : lower ≤ t.pc)
      (hp : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) : lower ≤ u.pc := by
    induction hp with
    | refl => exact ht
    | tail _ hStep ih => exact tauStaysAboveStartupPc hBound ih hStep
  induction hr with
  | nil => simp
  | step hl he _ ih =>
    have hLocal := localPath hs hl
    intro e hm
    rcases List.mem_cons.mp hm with rfl | hMem
    · rwa [estep_source_pc he]
    · apply ih _ e hMem
      rcases returningPc he with h | h <;> omega
  | last hl he =>
    intro e hm
    obtain rfl := List.mem_singleton.mp hm
    rw [estep_source_pc he]
    exact localPath hs hl

/-- Role execution stays beyond the common startup barrier. -/
theorem runPastStartup {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {o : Option TState} (hs : 174 ≤ s.pc)
    (hr : Run kernel Assumptions.all l g s events o) : ∀ e ∈ events, 174 ≤ e.pc :=
  runAtOrPastStartupPc (le_refl _) hs hr

/-- An event before or at a recorded startup instruction is also in the startup trace. -/
theorem earlierStartupEvent {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i j : Nat} {e f : Event}
    (he : X.get (g, i) = some e) (hf : X.get (g, j) = some f)
    (hIndex : i ≤ j) (hStart : f.pc < 174) : e.pc < 174 := by
  rcases hIndex.eq_or_lt with rfl | hBefore
  · rw [he] at hf
    exact (Option.some.inj hf).symm ▸ hStart
  by_contra! hLate
  have hg : g < l.threads := event_thread_lt hX hf
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hf).1
  obtain ⟨o, hRun⟩ := hX.thr g hg
  obtain ⟨state, nextState, hStep, hSuffix⟩ := hRun.after_event he (by omega)
  have hState := estep_source_pc hStep
  have hNext : 174 ≤ nextState.pc := by
    rcases returningPc hStep with h | h <;> omega
  have hGet : ((X.tr g).drop (i + 1))[j - (i + 1)]? = some f := by
    rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
    exact hf
  exact (Nat.not_lt_of_ge (runPastStartup hNext hSuffix f (List.mem_of_getElem? hGet))) hStart

private theorem afterCommonBar {l : Launch} {g : Nat} {s u : TState}
    (he : EStep kernel Assumptions.all l g s ⟨173, .bar 0 none .sync⟩ (some u)) :
    u.pc = 174 := by
  have hPc : s.pc = 173 := (estep_source_pc he).symm
  obtain ⟨i, hc, _, hf⟩ := estep_event_source he
  rw [hPc, Flow.code_173] at hc
  obtain rfl := Option.some.inj hc.symm
  change Fires s.pc (.bar 0 (next s) none .sync) ⟨173, .bar 0 none .sync⟩ (some u) at hf
  have hU := congrArg TState.pc (Option.some.inj hf.2)
  rw [hU]
  exact congrArg (·+1) hPc

private theorem commonBarOneIndex {l : Launch} {g : Nat} {s : TState} {events : List Event}
    {o : Option TState} (hr : Run kernel Assumptions.all l g s events o) :
    ∀ i j : Nat, i < j → events[i]? = some ⟨173, .bar 0 none .sync⟩ →
      events[j]? = some ⟨173, .bar 0 none .sync⟩ → False := by
  induction hr with
  | nil => simp
  | step _ he hRest ih =>
    intro i j hLt hi hj
    cases j with
    | zero => omega
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        rw [hi] at he
        have hAfter := afterCommonBar he
        have hBad := runPastStartup hAfter.ge hRest
          _ (List.mem_of_getElem? hj)
        change 174 ≤ 173 at hBad
        omega
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        exact ih i j (by omega) hi hj
  | last _ _ =>
    intro i j hLt hi hj
    have h := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_cons, List.length_nil] at h
    omega

/-- A lane's actual common startup barrier can occur at only one trace index. -/
theorem commonStartupUnique {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i j : Nat}
    (hg : g < l.threads)
    (hi : X.IsBarrier (g, i) 0 none 173) (hj : X.IsBarrier (g, j) 0 none 173) : i = j := by
  obtain ⟨_, hRun⟩ := hX.thr g hg
  rcases lt_trichotomy i j with h | h | h
  · exact (commonBarOneIndex hRun i j h hi hj).elim
  · exact h
  · exact (commonBarOneIndex hRun j i h hj hi).elim

end PTX.Kernels.TmlFa4Fwd.Prologue
