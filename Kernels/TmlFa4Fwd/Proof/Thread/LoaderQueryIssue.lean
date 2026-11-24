-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderActiveProgram
public import Kernels.TmlFa4Fwd.Proof.LoaderInputDescriptors
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Flow.Code.Part006
import Kernels.TmlFa4Fwd.Flow.Code.Part008
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Lemmas.Flow.Elect
import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

private def queryFrame (l : Launch) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1062, b32 14)]

private def queryExit : Event := ⟨9205, .exit⟩

private theorem qFrameCode (l : Launch) (branch : Nat) :
    ((kernel.code.drop 174).take (1901 - 174)).all
      (fun ins => loaderPipelineCutOp 174 1901 branch
        ((queryFrame l).map Prod.fst) ins.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem runOfExitWalk {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hx : queryExit ∈ es) : Run kernel Assumptions.all l g s es none := by
  induction hw with
  | stop => cases hx
  | tau ht _ ih =>
    cases ih hx with
    | step hloc he htail => exact .step (.head ht hloc) he htail
    | last hloc he => exact .last (.head ht hloc) he
  | ev he _ ih =>
    rcases List.mem_cons.mp hx with rfl | hTail
    · obtain ⟨_, _, hf⟩ := he
      cases fires_end_none hf (.inr rfl)
    · exact .step .refl he (ih hTail)
  | last he => exact .last .refl he

section
variable {l : Launch}

private theorem queryMarkContinuation {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) (hBounds : 174 ≤ s.pc ∧ s.pc ≤ 1901)
    (hs : RingShape s) (hFrame : Holds s.regs (queryFrame l)) {mark : Event} (hm : mark ∈ es)
    (hMark : mark.pc < 1901) (hContinues : ¬ Ends mark) :
    ∃ (t u : TState) (past tail : List Event) (visits : List Visit),
      es = past ++ mark :: tail ∧ (mark.pc ≤ u.pc ∧ u.pc ≤ mark.pc + 1) ∧
      EStep kernel Assumptions.all l g t mark (some u) ∧
      RingShape u ∧ Holds u.regs (queryFrame l) ∧
      Walk kernel Assumptions.all l g u tail visits := by
  have before {t : TState} {events : List Event} {visits : List Visit}
      (h : t.pc ≤ 1901) (hW : Walk kernel Assumptions.all l g t events visits)
      (hs : RingShape t) (hF : Holds t.regs (queryFrame l))
      (hm : mark ∈ events) : t.pc < 1901 := by
    by_contra! hn
    have hp : t.pc = 1901 := by omega
    have hc := loaderExitEventPcs (0 : Fin 2) hp hs hF hW _ hm
    rcases hc <;> omega
  have step {t u : TState} {ev : Option Event}
      (h : 174 ≤ t.pc ∧ t.pc < 1901) (hS : RingShape t)
      (hF : Holds t.regs (queryFrame l)) (he : WStep kernel Assumptions.all l g t ev u) :=
    pipelineCutStep (by decide) (by decide) h (qFrameCode l u.pc) he hS hF
  induction hw with
  | stop => cases hm
  | @tau t u es vs ht hWalk ih =>
    have hHi := before hBounds.2 (.tau ht hWalk) hs hFrame hm
    obtain ⟨hL, hH, hS, hF⟩ := step ⟨hBounds.1, hHi⟩ hs hFrame (.inl ⟨rfl, ht⟩)
    exact ih ⟨hL, hH.resolve_right (Nat.lt_irrefl _)⟩ hS hF hm
  | @ev t u e es vs he hWalk ih =>
    have hHi := before hBounds.2 (.ev he hWalk) hs hFrame hm
    obtain ⟨hL, hH, hS, hF⟩ := step ⟨hBounds.1, hHi⟩ hs hFrame (.inr ⟨e, rfl, he⟩)
    rcases List.mem_cons.mp hm with rfl | hNext
    · have hp := estep_source_pc he
      have hc : EStep kernel [] l g t mark (some u) := by
        obtain ⟨tm, hout, hFire⟩ := he
        exact ⟨tm, by rwa [← loaderOutCore hBounds.1 (by omega)], hFire⟩
      have hPc := (estep_return_pc hc (fun _ _ _ h => execLocal_frame h)).2
      have hAdvance : mark.pc ≤ u.pc ∧ u.pc ≤ mark.pc + 1 := by rcases hPc <;> omega
      exact ⟨t, u, [], es, vs, rfl, hAdvance, he, hS, hF, hWalk⟩
    · obtain ⟨t', u', past, tail, visits, hTail, hpc, hE, hS', hF', hW⟩ :=
        ih ⟨hL, hH.resolve_right (Nat.lt_irrefl _)⟩ hS hF hNext
      exact ⟨t', u', e :: past, tail, visits, by simp [hTail], hpc, hE, hS', hF', hW⟩
  | last he =>
    obtain rfl := (List.mem_singleton.mp hm).symm
    obtain ⟨_, _, hFire⟩ := he
    exact (hContinues (fires_none_ends hFire)).elim

private theorem queryAfterActualEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g index : Nat} (hg : g < l.threads) (hWarp : warpIndex l g = 14)
    {mark : Event} (he : X.get (g, index) = some mark)
    (hLate : 173 < mark.pc) (hMark : mark.pc < 1901) (hContinues : ¬ Ends mark) :
    ∃ t u pos visits, (mark.pc ≤ u.pc ∧ u.pc ≤ mark.pc + 1) ∧
      EStep kernel Assumptions.all l g t mark (some u) ∧
      RingShape u ∧ Holds u.regs (queryFrame l) ∧ queryExit ∈ (X.tr g).drop pos ∧
      Walk kernel Assumptions.all l g u ((X.tr g).drop pos) visits := by
  obtain ⟨s, _, hi, hs, hr⟩ :=
    nonzeroCommonPrefixOfLateEvent hp hX hg (by omega) he hLate
  have hStart : Holds s.regs (queryFrame l) :=
    ⟨hs.2.2.2.2.2.1, hWarp ▸ hs.2.2.2.2.1, trivial⟩
  obtain ⟨visits, hw⟩ := Mma.walkFromRun hr
  have hGet : ((X.tr g).drop 5)[index - 5]? = some mark := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le hi]
  obtain ⟨t, u, past, tail, rest, hTail, hu, hE, hShape, hFrame, hWalk⟩ :=
    queryMarkContinuation hw (by rw [hs.1]; decide) (ringShapeOfAt hs) hStart
      (List.mem_of_getElem? hGet) hMark hContinues
  obtain ⟨pc, hLast⟩ := (hComplete.1 g hg).resolve_left (noCanceled hX)
  have hLength : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hFinal : ((X.tr g).drop 5).getLast? = some queryExit := by
    have hPc := actualExitPc hX (i := (g, (X.tr g).length - 1))
      (by exact List.getLast?_eq_getElem?.symm.trans hLast)
    simp [List.getLast?_drop, not_le.mpr (by omega : 5 < (X.tr g).length), hLast, hPc, queryExit]
  have hTailExit : queryExit ∈ tail := by
    rw [hTail, List.getLast?_append] at hFinal
    cases tail with
    | nil =>
      simp at hFinal
      exact (hContinues (.inr (congrArg Event.kind hFinal))).elim
    | cons head tail =>
      have hSome : (head :: tail).getLast?.isSome = true := by simp
      cases hx : (head :: tail).getLast? with
      | none => simp [hx] at hSome
      | some e =>
        simp [List.getLast?_cons, hx] at hFinal
        exact List.mem_of_getLast? (hFinal ▸ hx)
  have hEq : past ++ mark :: tail = (past ++ [mark]) ++ tail := by
    rw [List.append_assoc]; rfl
  have hRest : (X.tr g).drop (5 + (past.length + 1)) = tail := by
    rw [← List.drop_drop, hTail, hEq, show past.length + 1 = (past ++ [mark]).length by simp,
      List.drop_append_length]
  exact ⟨t, u, _, rest, hu, hE, hShape, hFrame, hRest.symm ▸ hTailExit, hRest.symm ▸ hWalk⟩

private theorem requiredCut {g lo cut : Nat} {s : TState} {es : List Event} {vs : List Visit}
    {F : List (Nat × Value)} (hLo : 174 ≤ lo) (hCut : cut ≤ 1901)
    (hAudit : ∀ bound,
      ((kernel.code.drop lo).take (cut - lo)).all
        (fun ins => loaderPipelineCutOp lo cut bound (F.map Prod.fst) ins.op) = true)
    (hw : Walk kernel Assumptions.all l g s es vs) (hp : lo ≤ s.pc ∧ s.pc ≤ cut)
    (hShape : RingShape s) (hFrame : Holds s.regs F) (hExit : queryExit ∈ es) :
    ∃ t past tail visits, es = past ++ tail ∧ t.pc = cut ∧
      RingShape t ∧ Holds t.regs F ∧ queryExit ∈ tail ∧
      Walk kernel Assumptions.all l g t tail visits := by
  have keepExit {t : TState} {e : Event} {o : Option TState} (ht : t.pc ≤ cut)
      (he : EStep kernel Assumptions.all l g t e o) : e ≠ queryExit := by
    intro h
    have hSource := (estep_source_pc he).symm.trans (congrArg Event.pc h)
    change t.pc = 9205 at hSource
    omega
  induction hw with
  | stop => cases hExit
  | @tau t u events visits ht hw ih =>
    by_cases hc : t.pc = cut
    · exact ⟨t, [], events, _, rfl, hc, hShape, hFrame, hExit, .tau ht hw⟩
    obtain ⟨hL, hU, hS, hF⟩ := pipelineCutStep hLo hCut ⟨hp.1, by omega⟩
      (hAudit u.pc) (.inl ⟨rfl, ht⟩) hShape hFrame
    exact ih ⟨hL, hU.resolve_right (Nat.lt_irrefl _)⟩ hS hF hExit
  | @ev t u e events visits he hw ih =>
    by_cases hc : t.pc = cut
    · exact ⟨t, [], e :: events, _, rfl, hc, hShape, hFrame, hExit, .ev he hw⟩
    have hNext : queryExit ∈ events :=
      (List.mem_cons.mp hExit).resolve_left (Ne.symm (keepExit hp.2 he))
    obtain ⟨hL, hU, hS, hF⟩ := pipelineCutStep hLo hCut ⟨hp.1, by omega⟩
      (hAudit u.pc) (.inr ⟨e, rfl, he⟩) hShape hFrame
    obtain ⟨r, pre, tail, rest, heq, hPc, hs, hfr, hx, hWalk⟩ :=
      ih ⟨hL, hU.resolve_right (Nat.lt_irrefl _)⟩ hS hF hNext
    exact ⟨r, e :: pre, tail, rest, by rw [heq]; rfl, hPc, hs, hfr, hx, hWalk⟩
  | @last t e he =>
    exact (keepExit hp.2 he (List.mem_singleton.mp hExit).symm).elim

private theorem querySetupCode (l : Launch) (bound : Nat) :
    ((kernel.code.drop 385).take (538 - 385)).all
      (fun i => loaderPipelineCutOp 385 538 bound ((queryFrame l).map Prod.fst) i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem queryBranchCode (l : Launch) (bound : Nat) :
    ((kernel.code.drop 539).take (676 - 539)).all
      (fun i => loaderPipelineCutOp 539 676 bound
        (((123, .pred false) :: queryFrame l).map Prod.fst) i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem queryElectCode (l : Launch) (bound : Nat) :
    ((kernel.code.drop 677).take (687 - 677)).all
      (fun i => loaderPipelineCutOp 677 687 bound ((queryFrame l).map Prod.fst) i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem queryCoreStep {g : Nat} {s : TState} {es : List Event} {vs : List Visit} {pc : Nat}
    {F : List (Nat × Value)} {op : Op} {guard : Option (Nat × Bool)} (hp : s.pc = pc)
    (hLocal : op.isLocal = true) (hc : kernel.code[pc]? = some ⟨guard, op⟩) (hShape : RingShape s)
    (hFrame : Holds s.regs F) (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hExit : queryExit ∈ es) (hBound : pc < 9205) :
    At s pc F := by
  apply pipelineAtCut hp hShape hFrame _ ⟨_, hc, hLocal⟩
  by_contra hBad
  cases hf : s.fault with
  | none => exact hBad hf
  | some f =>
    cases hWalk with
    | stop => cases hExit
    | tau ht _ => simp [Tau, out, hf] at ht
    | ev he _ =>
      obtain ⟨tm, hout, hFire⟩ := he
      simp only [out, hf, Out.ev.injEq] at hout
      subst tm
      cases hFire.2
    | last he =>
      have hPc := (estep_source_pc he).symm.trans
        (congrArg Event.pc (List.mem_singleton.mp hExit).symm)
      change s.pc = 9205 at hPc
      omega

private theorem queryRolePred {g : Nat} :
    Seg kernel Assumptions.all l g 1 538 (queryFrame l) 539
      ((123, .pred false) :: queryFrame l) := by
  have core : Seg kernel [] l g 1 538 (queryFrame l) 539
      ((123, .pred false) :: queryFrame l) := by
    intro s hs
    simp only [queryFrame] at hs ⊢
    seg_fp hs using rfl
  intro s hs
  obtain ⟨u, hu, hU⟩ := core s hs
  exact ⟨u, (loaderLinear (regs := []) (by decide) (by decide) hs.1 (by simp) rfl hu).1, hU⟩

private theorem querySkipBranch {g : Nat} {t : TState}
    (ht : At t 676 ((123, .pred false) :: queryFrame l)) :
    Tau kernel Assumptions.all l g t (next t) := by
  unfold Tau
  rw [loaderOutCore (by have := ht.1; omega) (by have := ht.1; omega)]
  simp [out, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, Flow.code_676,
    guardHolds, readReg, skip, next, bind, Except.bind, pure, Except.pure]

private theorem queryElection {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : s.pc = 687) (hw : Walk kernel Assumptions.all l g s es vs) (hExit : queryExit ∈ es) :
    ∃ inst leader tail, es = ⟨687, .elect (2 ^ 32 - 1) inst leader⟩ :: tail := by
  cases hw with
  | stop => cases hExit
  | @tau _ u _ _ ht _ =>
    have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore (by omega) (by omega)]
    exact (tau_core_not_event (hs.symm ▸ Flow.code_687) (by decide) ht').elim
  | ev he _ =>
    obtain ⟨i, hc, _, hf⟩ := estep_event_source he
    rw [hs, Flow.code_687] at hc
    obtain rfl := Option.some.inj hc
    rcases fires_elect_mask (bits := BitVec.ofNat 64 (2 ^ 32 - 1)) rfl hf with
      ⟨inst, leader, rfl⟩ | ⟨_, hBad⟩
    · exact ⟨inst, leader, _, by rw [hs]; rfl⟩
    · rw [hBad] at hf
      exact (by cases fires_end_none hf (Or.inl ⟨_, rfl⟩))
  | last he =>
    have hPc := (estep_source_pc he).symm.trans
      (congrArg Event.pc (List.mem_singleton.mp hExit).symm)
    change s.pc = 9205 at hPc
    omega

private theorem queryElectionAfterMarker {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} (hw : Walk kernel Assumptions.all l g s events visits)
    (hPc : 385 ≤ s.pc ∧ s.pc ≤ 386) (hShape : RingShape s) (hFrame : Holds s.regs (queryFrame l))
    (hExit : queryExit ∈ events) :
    ∃ inst leader, (⟨687, .elect (2 ^ 32 - 1) inst leader⟩ : Event) ∈ events := by
  obtain ⟨t, pre, es, vs, hEs, ht, hTShape, hTRegs, hX, hW⟩ :=
    requiredCut (by decide) (by decide) (querySetupCode l) hw ⟨hPc.1, by omega⟩ hShape hFrame hExit
  have hAt : At t 538 (queryFrame l) :=
    queryCoreStep ht rfl Flow.code_538 hTShape hTRegs hW hX (by decide)
  obtain ⟨u, hu, hU⟩ := queryRolePred t hAt
  obtain ⟨nextVs, nextWalk⟩ := Mma.walkFromRun ((runOfExitWalk hW hX).after_local (run_rtg hu))
  obtain ⟨v, pre', tail, tailVs, hTail, hv, hShapeV, hFrameV, hExitV, hWalkV⟩ :=
    requiredCut (by decide) (by decide) (queryBranchCode l) nextWalk (by rw [hU.1]; decide)
      (ringShapeOfAt hU) hU.2.2.2.2 hX
  have hV : At v 676 ((123, .pred false) :: queryFrame l) :=
    queryCoreStep hv rfl Flow.code_676 hShapeV hFrameV hWalkV hExitV (by decide)
  have nextAt : At (next v) 677 (queryFrame l) := (hV.mono hFrameV.2).next
  obtain ⟨restVisits, hRest⟩ := Mma.walkFromRun
    ((runOfExitWalk hWalkV hExitV).after_local (.single (querySkipBranch hV)))
  obtain ⟨w, p, rem, wv, hRem, hwPc, _, _, hExitW, hWw⟩ :=
    requiredCut (by decide) (by decide) (queryElectCode l) hRest (by rw [nextAt.1]; decide)
      (ringShapeOfAt nextAt) nextAt.2.2.2.2 hExitV
  obtain ⟨inst, leader, tail', hE⟩ := queryElection hwPc hWw hExitW
  exact ⟨inst, leader, by rw [hEs, hTail, hRem, hE]; simp⟩
end

private theorem electedQueryPred {l : Launch} {g : Nat} :
    Seg kernel Assumptions.all l g 1 688 ((142, .pred true) :: queryFrame l) 689
      ((143, .pred false) :: queryFrame l) := by
  have core : Seg kernel [] l g 1 688 ((142, .pred true) :: queryFrame l) 689
      ((143, .pred false) :: queryFrame l) := by
    intro s hs
    simp only [queryFrame] at hs ⊢
    seg_fp hs using rfl
  intro s hs
  obtain ⟨u, hu, hU⟩ := core s hs
  exact ⟨u, (loaderLinear (regs := []) (by decide) (by decide) hs.1 (by simp) rfl hu).1, hU⟩

private theorem electedQueryBranch {l : Launch} {g : Nat} {s : TState}
    (hs : At s 689 ((143, .pred false) :: queryFrame l)) :
    Tau kernel Assumptions.all l g s (next s) := by
  unfold Tau
  rw [loaderOutCore (by have := hs.1; omega) (by have := hs.1; omega)]
  simp [out, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, Flow.code_689,
    guardHolds, readReg, skip, next, bind, Except.bind, pure, Except.pure]

private theorem electedQueryCode (l : Launch) (bound : Nat) :
    ((kernel.code.drop 690).take (693 - 690)).all
      (fun i => loaderPipelineCutOp 690 693 bound ((queryFrame l).map Prod.fst) i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem queryAtIssue {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : s.pc = 693) (hFrame : Holds s.regs (queryFrame l))
    (hw : Walk kernel Assumptions.all l g s es vs) (hExit : queryExit ∈ es) :
    ∃ addr spec tail, es = ⟨693, .tensorIssue addr spec⟩ :: tail ∧
      spec.sharedBase = ⟨.shared, g / l.block, l.sharedBase + 3072⟩ ∧
      spec.mbar = ⟨.shared, g / l.block, l.sharedBase⟩ := by
  cases hw with
  | stop => cases hExit
  | @tau _ u _ _ ht _ =>
    have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore (by omega) (by omega)]
    exact (tau_core_not_event (hs.symm ▸ Flow.code_693) (by decide) ht').elim
  | ev he _ =>
    obtain ⟨i, hc, _, hf⟩ := estep_event_source he
    rw [hs, Flow.code_693] at hc
    obtain rfl := Option.some.inj hc
    obtain ⟨addr, spec, rfl, _, hMbar⟩ := fires_cpTensor_issue hf
    have hCopy := fires_cpTensor_copy hf rfl
    have hDst := (tensorLoadCopy_box hCopy).1
    have hBound : l.sharedBase + 3072 < 2 ^ 32 := by have := hp.shared.2.1; omega
    have hBase : s.regs 2535 = some (b32 l.sharedBase) := hFrame.1
    have hDst' : sharedEffAddr l g s false 2535 3072 =
        .ok ⟨.shared, g / l.block, l.sharedBase + 3072⟩ := effAddr_b32_off hBase hBound
    have hMb' : mbarLoc l g s 2535 0 = .ok ⟨.shared, g / l.block, l.sharedBase⟩ := by
      simpa only [Nat.add_zero, Int.ofNat_zero] using
        decodedMbarOffset hp (g := g) (delta := 0) (off := 0)
          (by simpa only [Nat.add_zero] using hBase)
          (by unfold initializedMbarOffset; decide : initializedMbarOffset (0 + 0))
    exact ⟨addr, spec, _, by rw [hs], Except.ok.inj (hDst.symm.trans hDst'),
      Except.ok.inj (hMbar.symm.trans hMb')⟩
  | last he =>
    have hPc := (estep_source_pc he).symm.trans
      (congrArg Event.pc (List.mem_singleton.mp hExit).symm)
    change s.pc = 9205 at hPc
    omega

private theorem electedQueryIssues {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g index inst leader : Nat} (hg : g < l.threads) (hWarp : warpIndex l g = 14)
    (hLeader : laneOf l g = leader)
    (hElect : X.Elect (g, index) 687 (2 ^ 32 - 1) inst leader) :
    ∃ issue addr spec, FirstQueryIssue X (g, issue) addr spec ∧
      spec.sharedBase = ⟨.shared, g / l.block, l.sharedBase + 3072⟩ ∧
      spec.mbar = ⟨.shared, g / l.block, l.sharedBase⟩ := by
  obtain ⟨t, u, pos, visits, _, he, hShape, hFrame, hExit, hWalk⟩ :=
    queryAfterActualEvent hp hX hComplete hg hWarp hElect
      (by change 173 < 687; decide) (by change 687 < 1901; decide) (by simp [Ends])
  have ht : t.pc = 687 := (estep_source_pc he).symm
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  rw [ht, Flow.code_687] at hc
  obtain rfl := Option.some.inj hc
  obtain ⟨mask, label, lead, hEq, hu⟩ := fires_elect hf
  have heq := Kind.elect.inj (congrArg Event.kind hEq)
  obtain rfl := heq.2.2
  have hU : At u 688 ((142, .pred true) :: queryFrame l) := by
    have hPc : u.pc = 688 := by rw [hu]; simp [next, setReg, ht]
    have hReg : u.regs 142 = some (.pred true) := by rw [hu]; simp [next, setReg, hLeader]
    exact queryCoreStep hPc rfl Flow.code_688 hShape ⟨hReg, hFrame⟩ hWalk hExit (by decide)
  obtain ⟨v, hv, hV⟩ := electedQueryPred (g := g) u hU
  have hNext : At (next v) 690 (queryFrame l) := (hV.mono hV.2.2.2.2.2).next
  have hLoc := (run_rtg hv).trans (.single (electedQueryBranch hV))
  obtain ⟨vs, hw⟩ := Mma.walkFromRun ((runOfExitWalk hWalk hExit).after_local hLoc)
  obtain ⟨s, pre, tail, rest, hTrace, hs, _, hRegs, hTailExit, hTail⟩ :=
    requiredCut (by decide) (by decide) (electedQueryCode l) hw (by rw [hNext.1]; decide)
      (ringShapeOfAt hNext) hNext.2.2.2.2 hExit
  obtain ⟨addr, spec, _, hTrace', hDst, hMbar⟩ := queryAtIssue hp hs hRegs hTail hTailExit
  refine ⟨pos + pre.length, addr, spec, ?_, hDst, hMbar⟩
  change (X.tr g)[pos + pre.length]? = some ⟨693, .tensorIssue addr spec⟩
  rw [← List.getElem?_drop, hTrace, hTrace', List.getElem?_append_right (by omega)]
  simp

/-- A completed active CTA issues the first Q subbox in the warp-14 trace. -/
theorem firstQueryIssue {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {cta : Nat} (hCta : cta < l.grid) (hActive : cta < tilePrefix p p.batch * p.heads)
    (hFrame : OutputFootprint p X) :
    ∃ (input : EvId) (spec : TensorCopy.Spec),
      X.TensorIssue input p.qMapAddress spec ∧ FirstQueryIssue X input p.qMapAddress spec ∧
      input.1 / l.block = cta ∧
      spec.sharedBase = ⟨.shared, cta, l.sharedBase + 3072⟩ ∧
      spec.mbar = ⟨.shared, cta, l.sharedBase⟩ ∧
      (⟨spec.outer, spec.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
        ⟨2, p.qMap⟩ ∧ spec.rows = none ∧ spec.clusterAddress = false ∧ spec.group = .one := by
  let g := cta * l.block + 14 * 32
  have hg : g < l.threads := by
    change cta * l.block + 448 < l.grid * l.block
    rw [hp.block]
    omega
  have hOwner : g / l.block = cta := by dsimp [g]; rw [hp.block]; omega
  have hWarp : warpIndex l g = 14 := by dsimp [g, warpIndex]; rw [hp.block]; omega
  have hLane : laneOf l g = 0 := by dsimp [g, laneOf]; rw [hp.block]; omega
  have hWarpLane : warpLane l g 0 = g := by simp [warpLane, hLane]
  obtain ⟨batch, shuffles, _, _, _, cur, hTrace⟩ :=
    loaderActiveProgram hp hX hComplete hg (Nat.le_of_eq hWarp.symm)
      (by rwa [hOwner]) (by
        intro ref a data loc hWrite hCover hGlobal
        rcases hFrame ref a data loc hWrite hCover hGlobal with ho | ⟨q, hq, h, hh, k, hk, rfl⟩
        · exact .inl ho
        · exact .inr (lseByte_in hq hh hk))
  let acc : Acc := {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
  let bytes := (b32 (p.kLength batch)).toBytes.map some
  have hMark : X.get (g, cur.pos 0 - 3 + 2) = some ⟨385, .rd acc bytes⟩ := by
    have ht := hTrace 0 (by decide)
    rw [hWarpLane] at ht
    change (X.tr g)[cur.pos 0 - 3 + 2]? = _
    rw [← List.getElem?_drop, ht, List.getElem?_append_left (by change 2 < 3; decide)]
    rfl
  obtain ⟨_, u, pos, vs, hu, _, hShape, huFrame, hExit, hw⟩ :=
    queryAfterActualEvent hp hX hComplete hg hWarp hMark
      (by change 173 < 385; decide) (by change 385 < 1901; decide) (by simp [Ends])
  obtain ⟨inst, leader, hElect⟩ := queryElectionAfterMarker hw hu hShape huFrame hExit
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hElect
  have hFirst : X.Elect (g, pos + i) 687 (2 ^ 32 - 1) inst leader := by
    unfold Execution.Elect
    change (X.tr g)[pos + i]? = _
    rwa [← List.getElem?_drop]
  have hMask := (hX.elect.1 _ _ _ _ _ hFirst).2.2
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLeaderWarp := Step.sameWarp_lane hBlock hg hMask.1
  obtain ⟨j, pc, lead, hOther⟩ := hX.dependency.electParticipant hFirst hMask.1 hMask.2
  have hOtherElect : X.Elect (warpLane l g leader, j) pc (2 ^ 32 - 1) inst lead := hOther
  obtain ⟨rfl, _, rfl, _⟩ :=
    hX.elect.2.1 _ _ _ _ _ _ _ _ _ hFirst hOtherElect hLeaderWarp.1
  have hThread : warpLane l g leader < l.threads := hLeaderWarp.1.1.2.1
  have hCta' : warpLane l g leader / l.block = cta :=
    hLeaderWarp.1.1.2.2.symm.trans hOwner
  have hWarp' : warpIndex l (warpLane l g leader) = 14 :=
    hLeaderWarp.1.2.symm.trans hWarp
  obtain ⟨issue, addr, spec, hIssue, hDst, hMbar⟩ :=
    electedQueryIssues hp hX hComplete hThread hWarp' hLeaderWarp.2 hOtherElect
  obtain ⟨site, hAddr, hDesc, hRows, hDst', hCluster, hGroup⟩ :=
    actualInputBox hp hX hIssue.issue
  have hOff := congrArg Loc.addr (hDst.symm.trans hDst')
  have hSite : site = 0 := by
    change l.sharedBase + 3072 = l.sharedBase + (inputSite site).sharedOffset at hOff
    fin_cases site <;> first | rfl | (simp [inputSite] at hOff)
  subst site
  change addr = p.qMapAddress at hAddr
  subst addr
  exact ⟨_, spec, hIssue.issue, hIssue, hCta', by rwa [hCta'] at hDst,
    by rwa [hCta'] at hMbar, hDesc, hRows, hCluster, hGroup⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
