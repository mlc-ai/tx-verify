-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Kernels.TmlFa4Fwd.Proof.CorrectionLseFallback
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.CorrectionLseAfter
import Kernels.TmlFa4Fwd.Flow.Code.Part120
import Kernels.TmlFa4Fwd.Flow.Code.Part121

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption Epilogue Mma Prologue

noncomputable section

private def structuralEvent : Op → Bool
  | .tcAlloc .. | .tcDealloc .. | .tcRelinquish .. | .tcMma .. | .tcCommit .. |
      .cpTensorStore .. | .bulkWait .. | .bulkCommit => true
  | _ => false

private theorem structuralEventFrame {l : Launch} {g : Nat} {s : TState} {op : Op}
    (hSub : s.sub ≤ 3) (he : structuralEvent op = true) :
    CallbackFrame (fun u => u.sub ≤ 3 ∧ u.regs = s.regs)
      (eventTmpl Assumptions.all l g s op) := by
  have hZero : (0 : Nat) ≤ 3 := by decide
  have hOne : (1 : Nat) ≤ 3 := by decide
  cases op <;> try contradiction
  case tcMma m =>
    simp only [eventTmpl, tcTmpl, mmaTmpl]
    split
    · apply ofExec_frame
      repeat' first | exact ⟨hSub, rfl⟩ | trivial | (apply allOk_bind; intro v) | split
    · apply ofExec_frame
      repeat' first | exact ⟨hSub, rfl⟩ | trivial | (apply allOk_bind; intro v) | split
    · trivial
  case tcCommit =>
    simp only [eventTmpl, tcCommitTmpl]
    apply ofExec_frame
    repeat' first | exact ⟨hSub, rfl⟩ | trivial | (apply allOk_bind; intro v) | split
  case bulkCommit =>
    exact ⟨hSub, rfl⟩
  case bulkWait => exact ⟨hSub, rfl⟩
  case cpTensorStore =>
    simp only [eventTmpl, tensorStoreTmpl]
    apply ofExec_frame
    repeat' (apply allOk_bind; intro v)
    exact ⟨hSub, rfl⟩
  all_goals
    simp only [eventTmpl, tcTmpl]
    apply ofExec_frame
    repeat' first
      | exact ⟨hSub, rfl⟩
      | exact ⟨hZero, rfl⟩
      | exact ⟨hOne, rfl⟩
      | trivial
      | (apply allOk_bind; intro v)
      | split

private def beforeCorrectionInstruction (pc : Nat) (i : Instr) : Bool :=
  !(writesRegs i.op).contains 1062 && !(Softmax.scoreEventWrites i.op).contains 1062 &&
    (i.op.isLocal || Softmax.scoreEventOp i.op || structuralEvent i.op) &&
    match i.op with
    | .bra dst _ => 1904 ≤ dst && dst ≤ 7742
    | .brx .. => false
    | _ => pc < 7742

private theorem beforeCorrectionCodeAt {pc : Nat} {i : Instr} (hLo : 1904 ≤ pc) (hHi : pc < 7742)
    (hc : kernel.code[pc]? = some i) : beforeCorrectionInstruction pc i = true := by
  have hAll : (((kernel.code.drop 1904).take (7742 - 1904)).zipIdx 1904).all
      (fun (i, pc) => beforeCorrectionInstruction pc i) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, pc)
  apply List.mem_of_getElem? (i := pc - 1904)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem beforeCorrectionSegment {s u : TState} {sm : SegMatch CuteSlot}
    (hSite : s.pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel s.pc = some sm)
    (hu : Assumptions.execSwExp2 sm s = .ok u) :
    1904 ≤ u.pc ∧ u.pc ≤ 7742 ∧ u.sub ≤ 3 ∧ u.regs 1062 = s.regs 1062 := by
  have hAll : Assumptions.swExp2Sites.all (fun pc => match cuteExp2.matchAt kernel pc with
      | none => false
      | some x => (1904 ≤ x.stop && x.stop ≤ 7742) &&
          !(Softmax.scoreSegmentWrites x).contains 1062) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hc := List.all_eq_true.mp hAll _ hSite
  rw [hm] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at hc
  obtain ⟨hPc, hSub, _, hRegs⟩ := Softmax.scoreSegmentFrame hu
  exact ⟨hPc.symm ▸ hc.1.1, hPc.symm ▸ hc.1.2, hSub.symm ▸ (by decide), hRegs _ hc.2⟩

private theorem beforeCorrectionStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 1904 ≤ s.pc) (hHi : s.pc < 7742) (hSub : s.sub ≤ 3)
    (he : WStep kernel Assumptions.all l g s e u) :
    1904 ≤ u.pc ∧ u.pc ≤ 7742 ∧ u.sub ≤ 3 ∧ u.regs 1062 = s.regs 1062 := by
  rcases he with ⟨_, he⟩ | ⟨ev, _, he⟩
  · obtain ⟨i, hc, _, hSource⟩ := Softmax.tauScoreSource he
    have hCode := beforeCorrectionCodeAt hLo hHi hc
    simp only [beforeCorrectionInstruction, Bool.and_eq_true, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hCode
    rcases hSource with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · exact ⟨by change 1904 ≤ s.pc + 1; omega, by change s.pc + 1 ≤ 7742; omega,
        by change 0 ≤ 3; decide, rfl⟩
    · rcases Softmax.scoreExecLocal hLocal with hCore | ⟨sm, hSite, hm, hu⟩
      · have hNext := hCore.pc
        have hPc : 1904 ≤ u.pc ∧ u.pc ≤ 7742 := by
          cases hOp : i.op <;> simp only [hOp, nextPc, BrxTarget, or_false] at hNext
          case bra target _ =>
            have hTarget : 1904 ≤ target ∧ target ≤ 7742 := by simpa [hOp] using hCode.2
            rwa [hNext]
          case brx => simp [hOp] at hCode
          all_goals omega
        exact ⟨hPc.1, hPc.2, hCore.sub.symm ▸ hSub, hCore.regs _ hCode.1.1.1⟩
      · exact beforeCorrectionSegment hSite hm hu
  · obtain ⟨i, hc, hl, hFire⟩ := estep_event_source he
    have hCode := beforeCorrectionCodeAt hLo hHi hc
    simp only [beforeCorrectionInstruction, Bool.and_eq_true, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not, hl, Bool.false_or, Bool.or_eq_true] at hCode
    have hOrdinary : ordinaryEvent i.op = true := by
      rcases hCode.1.2 with hs | hs
      · cases hi : i.op <;> simp_all [Softmax.scoreEventOp, ordinaryEvent]
      · cases hi : i.op <;> simp_all [structuralEvent, ordinaryEvent]
    have hPc := callbackFrame_fires (ordinaryEventFrame hOrdinary) hFire
    have hP' : 1904 ≤ u.pc ∧ u.pc ≤ 7742 := by rcases hPc with h | h <;> omega
    suffices u.sub ≤ 3 ∧ u.regs 1062 = s.regs 1062 from ⟨hP'.1, hP'.2, this⟩
    rcases hCode.1.2 with hs | hs
    · obtain ⟨hEvent, hKeep⟩ := Softmax.scoreEventStep hc hs hSub hCode.1.1.2 he
      exact ⟨hEvent.sub, hKeep⟩
    · obtain ⟨hBound, hKeep⟩ := callbackFrame_fires (structuralEventFrame hSub hs) hFire
      exact ⟨hBound, congrFun hKeep 1062⟩

private theorem localRoleRun {l : Launch} {g : Nat} {s u : TState} {i : Instr}
    (hF : s.fault = none) (hc : kernel.code[s.pc]? = some i)
    (hl : i.op.isLocal = true) (hG : guardHolds s i.guard = .ok true)
    (hOff : s.pc ∉ Assumptions.swExp2Sites) (hCore : Assumptions.coreOp i.op = true)
    (hExec : execLocal l g s i.op = .ok u) :
    run kernel Assumptions.all l g 1 s = some u := by
  have hA : execLocalA Assumptions.all l g s i.op = .ok u := by
    rwa [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff hCore,
      execLocalA_nil]
  simp only [run, tauStep, out_tau hF hc hG hl hA]
  rfl

private theorem nonCorrectionExit {l : Launch} {g : Nat} (warp : Fin 16)
    (hWarp : warp.val < 8 ∨ 12 ≤ warp.val) {s : TState}
    (hs : s.pc = 7742) (hf : s.fault = none) (hr : s.regs 1062 = some (b32 warp.val)) :
    ∃ u, run kernel Assumptions.all l g 3 s = some u ∧
      u.pc = 9205 ∧ u.sub = s.sub ∧ out kernel Assumptions.all l g u = .ev .exit := by
  let v := next (setReg s 5867 (.bits 32 (BitVec.ofNat 64 (4 * (warp.val / 4)))))
  let w := next (setReg v 681 (.pred true))
  let u := {w with pc := 9205}
  have hv : run kernel Assumptions.all l g 1 s = some v := by
    refine localRoleRun hf (by rw [hs]; exact Flow.code_7742) rfl rfl (by rw [hs]; decide) rfl ?_
    rw [execLocal_int rfl]
    fin_cases warp <;> norm_num at hWarp
    all_goals simp only [execInt, DType.width, readBits, readReg, hr, bind,
      Except.bind, pure, Except.pure]; rfl
  have hPcV : v.pc = 7743 := by simp [v, next, setReg, hs]
  have hvR := show v.regs 5867 = some (.bits 32 (BitVec.ofNat 64 (4 * (warp.val / 4)))) from
    by simp [v, next, setReg]
  have hw : run kernel Assumptions.all l g 1 v = some w := by
    refine localRoleRun hf (by rw [hPcV]; exact Flow.code_7743) rfl rfl
      (by rw [hPcV]; decide) rfl ?_
    rw [execLocal_int rfl]
    fin_cases warp <;> norm_num at hWarp
    all_goals simp only [execInt, DType.width, readBits, readReg, hvR, bind,
      Except.bind, pure, Except.pure]; rfl
  have hPcW : w.pc = 7744 := by simp [w, next, setReg, hPcV]
  have hG : guardHolds w (some (681, false)) = .ok true := by
    have hr : w.regs 681 = some (.pred true) := by simp [w, next, setReg]
    simp [guardHolds, readReg, hr, bind, Except.bind, pure, Except.pure]
  have hu : run kernel Assumptions.all l g 1 w = some u :=
    localRoleRun hf (by rw [hPcW]; exact Flow.code_7744) rfl hG (by rw [hPcW]; decide) rfl rfl
  have he : out kernel Assumptions.all l g u = .ev .exit :=
    out_event (t := u) (show u.fault = none from hf) Flow.code_9205 rfl rfl
  exact ⟨u, run_comp (run_comp hv hw) hu, rfl, rfl, he⟩


private theorem nonCorrectionWalk {l : Launch} {g : Nat} (warp : Fin 16)
    (hWarp : warp.val < 8 ∨ 12 ≤ warp.val) {s : TState} {es : List Event} {vs : List Visit}
    (hLo : 1904 ≤ s.pc) (hHi : s.pc ≤ 7742) (hSub : s.sub ≤ 3)
    (hReg : s.regs 1062 = some (b32 warp.val))
    (hw : Walk kernel Assumptions.all l g s es vs) :
    ∀ pc a bs, pc ∈ lseStoreSites → (⟨pc, .wr a bs⟩ : Event) ∉ es := by
  induction hw with
  | stop => simp
  | @tau t u es vs ht hWalk ih =>
    by_cases hEnd : t.pc = 7742
    · intro pc a bs hSite hm
      have hClean := (Softmax.tauScoreSource ht).choose_spec.2.1
      obtain ⟨v, hr, hV, hSubV, _⟩ := nonCorrectionExit (l := l) (g := g)
        warp hWarp hEnd hClean hReg
      rcases advanceWalkLocals hr (.tau ht hWalk) with hEmpty | ⟨_, _, _, hTail⟩
      · rw [hEmpty] at hm
        cases hm
      · simp [lseStoreSites] at hSite
        exact noLseAfterTile (pc := pc) (a := a) (bs := bs)
          (by omega) (by omega) (by rw [hSubV]; exact hSub) hTail hm
    · obtain ⟨hL, hH, hS, hR⟩ :=
        beforeCorrectionStep hLo (by omega) hSub (.inl ⟨rfl, ht⟩)
      exact ih hL hH hS (hR.trans hReg)
  | @ev t u e es vs he hWalk ih =>
    intro pc a bs hSite hm
    rcases List.mem_cons.mp hm with hHere | hRest
    · have hP := estep_source_pc he
      rw [← hHere] at hP
      change pc = t.pc at hP
      simp [lseStoreSites] at hSite
      omega
    · by_cases hEnd : t.pc = 7742
      · obtain ⟨i, hc, hl, _⟩ := estep_event_source he
        rw [hEnd, Flow.code_7742] at hc
        obtain rfl := Option.some.inj hc
        cases hl
      · obtain ⟨hL, hH, hS, hR⟩ :=
          beforeCorrectionStep hLo (by omega) hSub (.inr ⟨_, rfl, he⟩)
        exact ih hL hH hS (hR.trans hReg) pc a bs hSite hRest
  | @last t e he =>
    intro pc a bs hSite hm
    have hEvent := List.mem_singleton.mp hm
    have hP := estep_source_pc he
    rw [← hEvent] at hP
    change pc = t.pc at hP
    simp [lseStoreSites] at hSite
    omega

/-- Every observed scalar LSE store is issued by one of the four correction warps. -/
theorem lseStoreWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {pc : Nat} {a : Acc} {bs : List Byte}
    (hGet : X.get i = some ⟨pc, .wr a bs⟩) (hSite : pc ∈ lseStoreSites) :
    8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12 := by
  by_contra hCorrection
  have hg := Step.CtaBar.thread_lt_of_get hX hGet
  have hLate : 173 < (⟨pc, .wr a bs⟩ : Event).pc := by
    simp [lseStoreSites] at hSite
    change 173 < pc
    omega
  obtain ⟨n, t, o, hn, ht, hr⟩ := commonDispatchOfLateEvent hp hX hg hGet hLate
  obtain ⟨visits, hw⟩ := walkFromRun hr
  have hm : (⟨pc, .wr a bs⟩ : Event) ∈ (X.tr i.1).drop n := by
    apply List.mem_of_getElem? (i := i.2 - n)
    rw [List.getElem?_drop, Nat.add_sub_of_le hn]
    exact hGet
  by_cases hLoader : 14 ≤ warpIndex l i.1
  · let warp : Fin 2 := ⟨warpIndex l i.1 - 14, by have := warpIndex_lt hp i.1; omega⟩
    have hIndex : 14 + warp.val = warpIndex l i.1 := Nat.add_sub_of_le hLoader
    have hAt : At t 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] :=
      ht.mono ⟨ht.2.2.2.2.2.1, hIndex.symm ▸ ht.2.2.2.2.1, trivial⟩
    have hSafe := loaderWalkEventPcs warp hAt hw _ hm
    simp [lseStoreSites] at hSite
    change pc ≤ 1901 ∨ pc = 9205 at hSafe
    omega
  · let warp : Fin 16 := ⟨warpIndex l i.1, warpIndex_lt hp i.1⟩
    have hNot : warp.val < 8 ∨ 12 ≤ warp.val := by
      change warpIndex l i.1 < 8 ∨ 12 ≤ warpIndex l i.1
      omega
    obtain ⟨u, hLocals, hu⟩ := dispatchRunFromCommon hp warp hg ht
    have hRange : 1904 ≤ u.pc ∧ u.pc ≤ 7742 := by
      have hLt : ¬ 14 ≤ warp.val := hLoader
      rw [hu.1, dispatchParamPc, ite_eq_right hLt]
      by_cases h13 : warp.val = 13
      · rw [ite_eq_left h13]
        decide
      · rw [ite_eq_right h13]
        by_cases h12 : warp.val = 12
        · rw [ite_eq_left h12]
          decide
        · rw [ite_eq_right h12]
          have hSoft : warp.val < 8 := by omega
          rw [ite_eq_left hSoft]
          decide
    rcases advanceWalkLocals hLocals hw with hNil | ⟨_, _, _, hRole⟩
    · rw [hNil] at hm
      cases hm
    · exact nonCorrectionWalk warp hNot hRange.1 hRange.2
        (by rw [hu.2.1]; decide) hu.2.2.2.2.1 hRole pc a bs hSite hm

/-- The observed correction lane writes the row of its actual work item. -/
theorem lseStoreAssignment {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {pc : Nat} {a : Acc} {bs : List Byte}
    (hSite : pc ∈ lseStoreSites) (hGet : X.get i = some ⟨pc, .wr a bs⟩) :
    AssignedLseFootprint p l (i.1 / l.block) i.1 a := by
  have hThread := Step.CtaBar.thread_lt_of_get hX hGet
  obtain ⟨hLoWarp, hHiWarp⟩ := lseStoreWarp hp hX hGet hSite
  have hLane : laneOf l i.1 < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l i.1 (laneOf l i.1) = i.1 :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hActual : X.get (warpLane l i.1 (laneOf l i.1), i.2) = some ⟨pc, .wr a bs⟩ := by
    rw [hSelf]
    exact hGet
  have hPc : pc = 9073 ∨ pc = 9082 := by simpa [lseStoreSites] using hSite
  simpa only [hSelf] using
    correctionWarpLseStoreSpec hp hX hThread hLoWarp hHiWarp hLane hPc hActual

/-- The query offsets that every read returns determine valid LSE store footprints for every
recorded write, including in incomplete consistent executions. -/
theorem lseStoreSpecs {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) : LseStoreSpecs p X :=
  fun _ _ _ _ hSite hGet => (lseStoreAssignment hp hX hSite hGet).toSpec hp

end
end PTX.Kernels.TmlFa4Fwd.Correction
