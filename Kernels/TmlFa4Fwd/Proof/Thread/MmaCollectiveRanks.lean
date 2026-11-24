-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal
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
import Kernels.TmlFa4Fwd.Proof.MmaLinearEvents
import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity
import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
import Lemmas.Flow.ElectMask
import Lemmas.Flow.NotShfl
import Lemmas.Flow.TauFrame
import Lemmas.Flow.MarkedCut
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCollectiveAnchor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma
open Prologue (warpIndex)
open PTX.Kernels.TmlFa4Fwd (roleBodyPc roleBodyEventPcs)

noncomputable section

-- Relative event counts start immediately before the first QK election.
private def prefixShuffles : List Nat := [2214]
private def prefixElections : List Nat := [2153,2205,2215,2267,2271]
private def steadyShuffles : List Nat := [2307,2308,2310,2361,2423,2425]
private def steadyElections : List Nat := [2311,2363,2415,2426,2459,2464,2516,2520]
private def tailShuffles : List Nat := [2558,2559,2561,2599,2601]
private def tailElections : List Nat := [2534,2538,2562,2602,2635,2639,2643]

private def beforeSite (pos : Nat) (xs : List Nat) : Nat :=
  xs.countP (fun site => site < pos)

private def shuffleOffset (pos : Nat) : Nat :=
  if pos < 2291 then beforeSite pos prefixShuffles
  else 1 + beforeSite pos (if pos < 2534 then steadyShuffles else tailShuffles)

private def electionOffset (pos : Nat) : Nat :=
  if pos < 2291 then beforeSite pos prefixElections
  else 5 + beforeSite pos (if pos < 2534 then steadyElections else tailElections)

private def loopEdge (pos dst : Nat) : Bool := pos == 2533 && (dst == 2291 || dst == 2534)

private def countedEdge (pos dst shfl elect : Nat) : Bool :=
  decide (2768 ≤ dst) ||
    (decide (2153 ≤ dst) &&
      (decide (2654 ≤ dst) ||
        (decide (pos < 2654) && decide (shuffleOffset dst + (if loopEdge pos dst then 6 else 0) =
          shuffleOffset pos + shfl))) &&
      decide (electionOffset dst + (if loopEdge pos dst then 8 else 0) =
        electionOffset pos + elect))

private def rankInstruction (pos : Nat) (ins : Instr) : Bool :=
  let s := if ins.op.isShfl then 1 else 0
  let e := if electOp ins.op then 1 else 0
  (!(ins.op.isShfl || electOp ins.op) ||
    (ins.guard.isNone && (match ins.op with
      | .warp w => linearWarpOp w
      | _ => false))) &&
  countedEdge pos (pos+1) s e &&
  match ins.op with
  | .bra dst _ => countedEdge pos dst 0 0
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem rankInstructionAudit :
    (((kernel.code.drop 2153).take (2768-2153)).zipIdx 2153).all
      (fun (ins,pos) => rankInstruction pos ins) = true := by kernel_rfl

private theorem rankCodeAt {pos : Nat} {ins : Instr} (hLo : 2153 ≤ pos) (hHi : pos < 2768)
    (hCode : kernel.code[pos]? = some ins) : rankInstruction pos ins = true := by
  let code := ((kernel.code.drop 2153).take (2768-2153)).zipIdx 2153
  have hMem : (ins,pos) ∈ code := by
    apply List.mem_of_getElem? (i := pos-2153)
    dsimp only [code]
    rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
      Nat.add_sub_of_le hLo,hCode]
    rfl
  exact List.all_eq_true.mp rankInstructionAudit (ins,pos) hMem

private theorem returningCollective {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {w : WarpInstr} (hOp : linearWarpOp w = true)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.warp w)) e (some u)) :
    Execution.isShfl e = (.warp w : Op).isShfl ∧ isElectEv e = electOp (.warp w) := by
  unfold linearWarpOp at hOp
  split at hOp
  · obtain ⟨_,_,_,_,_,rfl,_⟩ := fires_shfl (p := none) hf
    exact ⟨rfl,rfl⟩
  · obtain ⟨_,_,_,rfl,_⟩ := fires_elect hf
    exact ⟨rfl,rfl⟩
  · simp only [eventTmpl,warpTmpl_vote] at hf
    unfold voteTmpl at hf
    repeat' split at hf
    all_goals first | (obtain ⟨_,rfl,_⟩ := hf; exact ⟨rfl,rfl⟩) | simp_all [Fires]
  · cases hOp

private theorem returningMarks {l : Launch} {g : Nat} {s u : TState} {e : Event} {ins : Instr}
    (hCheck : rankInstruction s.pc ins = true)
    (hFire : Fires s.pc (eventTmpl Assumptions.all l g s ins.op) e (some u)) :
    Execution.isShfl e = ins.op.isShfl ∧ isElectEv e = electOp ins.op := by
  by_cases hm : ins.op.isShfl || electOp ins.op
  · have hW : (match ins.op with | .warp w => linearWarpOp w | _ => false) = true := by
      simp only [rankInstruction,hm,Bool.not_true,Bool.false_or,Bool.and_eq_true] at hCheck
      exact hCheck.1.1.2
    cases hop : ins.op <;> rw [hop] at hW <;> try cases hW
    rename_i w
    simpa only [hop] using returningCollective hW (hop ▸ hFire)
  · have hNoS : ins.op.isShfl = false := by
      cases hs : ins.op.isShfl <;> simp_all
    have hNoE : electOp ins.op = false := by
      simpa [hNoS] using hm
    have hs : Execution.isShfl e = false := by
      cases hh : Execution.isShfl e
      · rfl
      · exact (Bool.noConfusion ((fires_shfl_op hFire hh).symm.trans hNoS))
    have he : isElectEv e = false := by
      obtain ⟨pc,k⟩ := e
      cases k <;> try rfl
      exact (fires_notElect (eventTmpl_notElect hNoE) hFire _ _ _ rfl).elim
    exact ⟨hs.trans hNoS.symm, he.trans hNoE.symm⟩

private theorem rankStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 2153 ≤ s.pc) (hHi : s.pc < 2768)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    countedEdge s.pc u.pc (ev.toList.countP Execution.isShfl)
      (ev.toList.countP isElectEv) = true := by
  have hCore := out_eq_core (show 1904 ≤ s.pc by omega) hHi (l := l) (g := g) (t := s)
  rcases hStep with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · have hTau : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← hCore]
    obtain ⟨ins,hCode⟩ := tau_core_has_code hTau
    have hCheck := rankCodeAt hLo hHi hCode
    have hNeutral : ins.op.isShfl = false ∧ electOp ins.op = false := by
      cases hS : ins.op.isShfl <;> cases hE : electOp ins.op
      · exact ⟨rfl,rfl⟩
      all_goals
        have hg : ins.guard.isNone = true := by
          simp only [rankInstruction,hS,hE,Bool.or_false,Bool.or_true,Bool.false_or,
            Bool.not_true,Bool.and_eq_true] at hCheck
          exact hCheck.1.1.1
        have hOp : ins.op.isLocal = false := by
          cases h : ins.op <;> simp only [h,Op.isShfl,electOp,Bool.false_eq_true] at hS hE
          all_goals rfl
        have hPlain : kernel.code[s.pc]? = some ⟨none,ins.op⟩ := by
          obtain ⟨guard,op⟩ := ins
          cases guard
          · exact hCode
          · cases hg
        exact (tau_core_not_event hPlain hOp hTau).elim
    simp only [rankInstruction,hNeutral.1,hNeutral.2,Bool.or_self,Bool.not_false,
      Bool.true_or,Bool.true_and,Bool.false_eq_true,ite_false,Bool.and_eq_true] at hCheck
    simp only [Option.toList_none,List.countP_nil]
    rcases tau_core_frame hCode hTau with rfl | hFrame
    · exact hCheck.1
    have hPc := hFrame.pc
    cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
    case bra dst uni => simpa only [hOp,hPc] using hCheck.2
    case brx =>
      have hNo := hCheck.2
      simp only [hOp,Bool.false_eq_true] at hNo
    all_goals exact hPc.symm ▸ hCheck.1
  · obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
    have hCheck := rankCodeAt hLo hHi hCode
    obtain ⟨hS,hE⟩ := returningMarks hCheck hFire
    have heCore : EStep kernel [] l g s e (some u) := by
      obtain ⟨tm,hOut,hFire⟩ := he
      exact ⟨tm,hCore ▸ hOut,hFire⟩
    simp only [Option.toList_some,List.countP_singleton,hS,hE]
    rcases (estep_return_pc heCore (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · by_cases hm : ins.op.isShfl || electOp ins.op
      · have hW : (match ins.op with | .warp w => linearWarpOp w | _ => false) = true := by
          simp only [rankInstruction,hm,Bool.not_true,Bool.false_or,Bool.and_eq_true] at hCheck
          exact hCheck.1.1.2
        cases hop : ins.op <;> rw [hop] at hW <;> try cases hW
        rename_i w
        have hAdv := (linearWarpAdvances hW (hop ▸ hFire)).1
        omega
      · have hNoS : ins.op.isShfl = false := by cases hs : ins.op.isShfl <;> simp_all
        have hNoE : electOp ins.op = false := by simpa [hNoS] using hm
        have hNot : loopEdge s.pc s.pc = false := by
          simp only [loopEdge,Bool.and_eq_false_iff,Bool.or_eq_false_iff,beq_eq_false_iff_ne]
          omega
        by_cases hLate : 2654 ≤ s.pc
        · simp [countedEdge,h,hNoS,hNoE,hLo,hNot,hLate]
        · have hEarly : s.pc < 2654 := by omega
          simp [countedEdge,h,hNoS,hNoE,hLo,hNot,hEarly]
    · rw [h]
      exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hCheck).1).2

private def CounterFrame (pos shuffles elections : Nat) : Prop :=
  ∃ n, elections = electionOffset pos + 8*n ∧
    (pos < 2654 → shuffles = shuffleOffset pos + 6*n)

private theorem counterStep {pos dst shfl elect s e : Nat}
    (h : countedEdge pos dst shfl elect = true) (hs : CounterFrame pos s e)
    (hHi : dst < 2768) :
    2153 ≤ dst ∧ CounterFrame dst (s+shfl) (e+elect) := by
  simp only [countedEdge,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨hdst,hS⟩,hE⟩ := h.resolve_left (by omega)
  obtain ⟨n,he,hs⟩ := hs
  refine ⟨hdst, n + (if loopEdge pos dst then 1 else 0),?_,?_⟩
  · rw [he]
    cases hEdge : loopEdge pos dst <;>
      simp only [hEdge,Bool.false_eq_true,↓reduceIte] at hE ⊢ <;> omega
  · intro hDst
    obtain ⟨hTime,hCnt⟩ := hS.resolve_left (by omega)
    rw [hs hTime]
    cases hEdge : loopEdge pos dst <;>
      simp only [hEdge,Bool.false_eq_true,↓reduceIte] at hCnt ⊢ <;> omega

set_option maxRecDepth 100000 in
private theorem collectiveExitFloor :
    (kernel.code.drop 2768).all (fun i => staysPastEvent 2768 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem collectiveExitSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2768 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem countersInWalk {l : Launch} {g sCount eCount : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hs : 2153 ≤ s.pc)
    (hFrame : CounterFrame s.pc sCount eCount)
    (hWalk : Walk kernel Assumptions.all l g s es vs) {e : Event} {index : Nat}
    (hGet : es[index]? = some e) (hEarly : e.pc < 2768) :
    CounterFrame e.pc (sCount+(es.take index).countP Execution.isShfl)
      (eCount+(es.take index).countP isElectEv) := by
  induction hWalk generalizing index sCount eCount with
  | stop => simp at hGet
  | @tau s u es vs ht hw ih =>
    have hMem := List.mem_of_getElem? hGet
    have hS : s.pc < 2768 := by
      by_contra! hLate
      exact (Nat.not_le_of_lt hEarly (eventTailEvents collectiveExitFloor
        collectiveExitSegments (.tau ht hw) hLate e hMem)).elim
    have hU : u.pc < 2768 := by
      by_contra! hLate
      exact (Nat.not_le_of_lt hEarly (eventTailEvents collectiveExitFloor
        collectiveExitSegments hw hLate e hMem)).elim
    have hStep := rankStep hs hS (.inl ⟨rfl,ht⟩)
    obtain ⟨hu,hF⟩ := counterStep hStep hFrame hU
    simp only [Option.toList_none,List.countP_nil,Nat.add_zero] at hF
    exact ih hu hF hGet
  | @ev s u first es vs hFirst hTail ih =>
    cases index with
    | zero =>
      obtain rfl := Option.some.inj hGet
      simpa only [List.take_zero,List.countP_nil,Nat.add_zero,estep_source_pc hFirst]
        using hFrame
    | succ index =>
      have hMem := List.mem_of_getElem? (show es[index]? = some e from hGet)
      have hS : s.pc < 2768 := by
        by_contra! hLate
        exact (Nat.not_le_of_lt hEarly (eventTailEvents collectiveExitFloor
          collectiveExitSegments (.ev hFirst hTail) hLate e (List.mem_cons_of_mem _ hMem))).elim
      have hU : u.pc < 2768 := by
        by_contra! hLate
        exact (Nat.not_le_of_lt hEarly (eventTailEvents collectiveExitFloor
          collectiveExitSegments hTail hLate e hMem)).elim
      have hStep := rankStep hs hS (.inr ⟨first,rfl,hFirst⟩)
      obtain ⟨hu,hF⟩ := counterStep hStep hFrame hU
      convert ih hu hF hGet using 1 <;>
        simp only [Option.toList_some,List.take_succ_cons,List.countP_cons,List.countP_nil] <;>
        omega
  | last hLast =>
    obtain rfl := List.mem_singleton.mp (List.mem_of_getElem? hGet)
    cases index with
    | zero =>
      simpa only [List.take_zero,List.countP_nil,Nat.add_zero,estep_source_pc hLast]
        using hFrame
    | succ _ => simp at hGet

private def beforeFirstRegion (pos : Nat) := 1908 ≤ pos ∧ (pos ≤ 2153 ∨ pos = 2763)

private instance (pos : Nat) : Decidable (beforeFirstRegion pos) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def beforeElectOp (ins : Instr) : Bool :=
  !electOp ins.op && match ins.op with
  | .bra dst _ => decide (beforeFirstRegion dst)
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem preElectionCode :
    ((kernel.code.drop 1908).take (2153-1908)).all beforeElectOp = true := by kernel_rfl

private theorem preElectionAt {pos : Nat} {ins : Instr} (hLo : 1908 ≤ pos) (hHi : pos < 2153)
    (hGet : kernel.code[pos]? = some ins) : beforeElectOp ins = true := by
  let code := (kernel.code.drop 1908).take (2153-1908)
  have hMem : ins ∈ code := by
    apply List.mem_of_getElem? (i := pos-1908)
    dsimp only [code]
    rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo,hGet]
  exact List.all_eq_true.mp preElectionCode ins hMem

private theorem beforeElectStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hs : beforeFirstRegion s.pc) (hPre : s.pc < 2153)
    (hStep : WStep kernel Assumptions.all l g s ev u) : beforeFirstRegion u.pc := by
  have hCore := out_eq_core (show 1904 ≤ s.pc by have := hs.1; omega)
    (show s.pc < 2768 by omega) (l := l) (g := g) (t := s)
  have hSeq : beforeFirstRegion (s.pc+1) := ⟨by have := hs.1; omega,.inl (by omega)⟩
  rcases hStep with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · have hTau : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← hCore]
    obtain ⟨ins,hCode⟩ := tau_core_has_code hTau
    rcases tau_core_frame hCode hTau with rfl | hLocal
    · exact hSeq
    have hPc := hLocal.pc
    have hCheck := (Bool.and_eq_true_iff.mp (preElectionAt hs.1 hPre hCode)).2
    cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
    case bra dst uni =>
      rw [hPc]
      exact of_decide_eq_true (by simpa only [hOp] using hCheck)
    case brx => simp only [hOp,Bool.false_eq_true] at hCheck
    all_goals exact hPc.symm ▸ hSeq
  · have hEStep : EStep kernel [] l g s e (some u) := by
      obtain ⟨tm,hOut,hFire⟩ := he
      exact ⟨tm,hCore ▸ hOut,hFire⟩
    rcases (estep_return_pc hEStep (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h.symm ▸ hs
    · exact h.symm ▸ hSeq

private theorem beforeElectEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hs : beforeFirstRegion s.pc) (hPre : s.pc < 2153)
    (hEvent : EStep kernel Assumptions.all l g s e (some u)) : isElectEv e = false := by
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source hEvent
  have hNo := (Bool.and_eq_true_iff.mp (preElectionAt hs.1 hPre hCode)).1
  have hNot : electOp ins.op = false := by simpa using hNo
  obtain ⟨pc,k⟩ := e
  cases k <;> try rfl
  exact (fires_notElect (eventTmpl_notElect hNot) hFire _ _ _ rfl).elim

set_option maxRecDepth 100000 in
private theorem afterMmaFloor :
    (kernel.code.drop 2763).all (fun i => staysPastEvent 2763 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterMmaSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2763 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem firstElectionCut {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hs : s.pc = 1908)
    (hWalk : Walk kernel Assumptions.all l g s es vs)
    {e : Event} (he : e ∈ es) (hRange : 2153 ≤ e.pc ∧ e.pc < 2763) :
    ∃ t pre rest post, es = pre ++ rest ∧ t.pc = 2153 ∧ e ∈ rest ∧
      (∀ f ∈ pre, f.pc < 2153 ∧ isElectEv f = false) ∧
      Walk kernel Assumptions.all l g t rest post := by
  obtain ⟨t,pre,rest,post,hSplit,hRest,hReg,hCut,_,hNo,hTail⟩ :=
    hWalk.cut_marked_where (P := fun s => beforeFirstRegion s.pc)
      (cut := fun s => 2153 ≤ s.pc) (good := fun ev => ev.pc < 2153 ∧ isElectEv ev = false)
      (fun _ => 0) (fun _ => false) (fun _ _ _ => rfl)
      (fun {_ _ ev} hP hn hStep => ⟨beforeElectStep hP (by omega) hStep,by cases ev <;> rfl⟩)
      (fun hP hn hEvent => ⟨by rw [estep_source_pc hEvent]; omega,
        beforeElectEvent hP (by omega) hEvent⟩)
      (by rw [hs]; decide) he (fun t _ hn h => hn (h ▸ hRange.1))
  have hPc : t.pc = 2153 := by
    rcases hReg.2 with hLe | hExit
    · omega
    · exact (Nat.not_le_of_lt hRange.2
        (eventTailEvents afterMmaFloor afterMmaSegments hTail hExit.ge e hRest)).elim
  exact ⟨t,pre,rest,post,hSplit,hPc,hRest,hNo,hTail⟩

private theorem noElectionCount {events : List Event} (h : ∀ e ∈ events, isElectEv e = false) :
    events.countP isElectEv = 0 := by
  induction events with
  | nil => rfl
  | cons first rest ih =>
    rw [List.countP_cons,h first (by simp),ih (fun e he => h e (by simp [he]))]
    rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem startupWithoutElections (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hFence : X.get (g,3) = some ⟨172,.fenceMbarInit⟩)
    (hBar : X.get (g,4) = some ⟨173,.bar 0 none .sync⟩) {inst : Nat}
    (hHint : X.get (g,5) = some ⟨1907,.setMaxReg false 80 inst⟩) :
    elections X g 6 = 0 := by
  apply noElectionCount
  intro e hm
  obtain ⟨k,hk,hGet⟩ := List.mem_iff_getElem.mp hm
  have hBound : k < 6 := hk.trans_le (List.length_take_le _ _)
  have he : X.get (g,k) = some e := by
    change (X.tr g)[k]? = some e
    rw [← List.getElem?_take_of_lt hBound]
    exact (List.getElem?_eq_getElem hk).trans (congrArg some hGet)
  interval_cases k
  · rw [Prologue.firstSharedValue hp hX g hg he]
    rfl
  · rw [Prologue.secondWarpValue hp hX g hg he]
    rfl
  · rw [Prologue.thirdWarpValue hp hX g hg he]
    rfl
  · obtain rfl := Option.some.inj (he.symm.trans hFence)
    rfl
  · obtain rfl := Option.some.inj (he.symm.trans hBar)
    rfl
  · obtain rfl := Option.some.inj (he.symm.trans hHint)
    rfl

private theorem electionAtCut {l : Launch} {g : Nat} {s : TState} {events : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s events vs) (hPc : s.pc = 2153)
    {e : Event} (he : e ∈ events) (hLater : 2153 < e.pc) :
    ∃ mask inst lead, events[0]? = some ⟨2153,.elect mask inst lead⟩ := by
  have hCode : kernel.code[s.pc]? = some _ := hPc.symm ▸ Flow.code_2153
  cases hw with
  | stop => cases he
  | tau ht _ =>
    have hCore := out_eq_core (show 1904 ≤ s.pc by omega) (show s.pc < 2768 by omega)
      (l := l) (g := g) (t := s)
    rw [Tau,hCore] at ht
    exact (tau_core_not_event hCode rfl ht).elim
  | ev hEvent _ =>
    obtain ⟨ins,hIns,_,hFire⟩ := estep_event_source hEvent
    obtain rfl := Option.some.inj (hIns.symm.trans hCode)
    obtain ⟨mask,inst,lead,rfl,_⟩ := fires_elect hFire
    exact ⟨mask,inst,lead,by simp only [List.getElem?_cons_zero,hPc]⟩
  | last hEvent =>
    obtain rfl := List.mem_singleton.mp he
    have hStart := estep_source_pc hEvent
    omega

private theorem actualCollectiveRanks (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {e : Event}
    (he : X.get (g,index) = some e) (hWarp : warpIndex l g = 12) (hPc : 2153 < e.pc ∧ e.pc < 2763) :
    ∃ first inst lead n, X.Elect (g,first) 2153 (2^32-1) inst lead ∧
      first ≤ index ∧ elections X g first = 0 ∧ elections X g index = electionOffset e.pc + 8*n ∧
      (e.pc < 2654 → ((X.tr g).take index).countP Execution.isShfl =
        ((X.tr g).take first).countP Execution.isShfl + shuffleOffset e.pc + 6*n) := by
  let xs := X.tr g
  obtain ⟨s,vs,hIndex,hs,hWalk,hFence,hBar,regInst,hHint⟩ :=
    mmaRoleWalkOfDemand hp hX he hWarp (.inl (by omega))
  have hG := event_thread_lt hX he
  have hLookup : (xs.drop 6)[index-6]? = some e := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hIndex]
    exact he
  obtain ⟨t,pre,rest,post,hSplit,ht,hMem,hNo,hTail⟩ :=
    firstElectionCut hs.1 hWalk (List.mem_of_getElem? hLookup) ⟨hPc.1.le,hPc.2⟩
  let first := 6 + pre.length
  have hBase : first ≤ index := by
    by_contra! hLate
    rw [hSplit,List.getElem?_append_left (by dsimp only [first] at hLate; omega)] at hLookup
    have hh := (hNo e (List.mem_of_getElem? hLookup)).1
    omega
  have hSuffix : xs.drop first = rest := by
    rw [← List.drop_drop,hSplit,List.drop_append_length]
  have hElects : elections X g first = 0 := by
    have hE0 := startupWithoutElections hp hX hG hFence hBar hHint
    change (xs.take 6).countP isElectEv = 0 at hE0
    change (xs.take (6+pre.length)).countP isElectEv = 0
    rw [List.take_add,hSplit,List.take_append_length,List.countP_append,hE0,
      noElectionCount (fun ev h => (hNo ev h).2)]
  obtain ⟨mask,inst,lead,hFirst⟩ := electionAtCut hTail ht hMem hPc.1
  have hActual : X.Elect (g,first) 2153 mask inst lead := by
    change xs[first]? = _
    rwa [← Nat.add_zero first,← List.getElem?_drop,hSuffix]
  have hRest : rest[index-first]? = some e := by
    rw [← hSuffix,List.getElem?_drop,Nat.add_sub_of_le hBase]
    exact he
  have hInit : CounterFrame t.pc 0 0 := by rw [ht]; exact ⟨0, rfl, fun _ => rfl⟩
  obtain ⟨n,hE,hS⟩ := countersInWalk ht.ge hInit hTail hRest (by omega)
  have hTake : xs.take index = xs.take first ++ rest.take (index-first) := by
    conv_lhs => rw [← Nat.add_sub_of_le hBase,List.take_add,hSuffix]
  refine ⟨first,inst,lead,n,actualFullElectionMask hX hActual ▸ hActual,hBase,hElects,?_,?_⟩
  · change (xs.take index).countP isElectEv = _
    rw [hTake,List.countP_append,show (xs.take first).countP isElectEv = 0 from hElects]
    exact hE
  · intro h
    rw [hTake,List.countP_append]
    have hs := hS h
    change (xs.take first).countP Execution.isShfl +
      (rest.take (index-first)).countP Execution.isShfl =
        (xs.take first).countP Execution.isShfl + shuffleOffset e.pc + 6*n
    omega

/-- Any actual MMA role event in the compute body follows the first full-warp QK election. -/
theorem firstMmaElectionBeforeEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e) (hWarp : warpIndex l g = 12)
    (hPc : 2153 < e.pc ∧ e.pc < 2763) :
    ∃ first inst lead, first < index ∧ X.Elect (g,first) 2153 (2^32-1) inst lead := by
  obtain ⟨first,inst,lead,_,hElect,hle,_,_,_⟩ := actualCollectiveRanks hp hX he hWarp hPc
  refine ⟨first,inst,lead,?_ ,hElect⟩
  by_contra! h
  obtain rfl : first = index := by omega
  have hh := congrArg Event.pc (Option.some.inj (hElect.symm.trans he))
  change 2153 = e.pc at hh
  omega

set_option maxRecDepth 100000 in
private theorem afterFirstFloor :
    (kernel.code.drop 2153).all (fun i => staysPastEvent 2153 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterFirstSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2153 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterOpeningElectionFloor :
    (kernel.code.drop 2154).all (fun i => staysPastEvent 2154 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterOpeningElectionSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2154 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem followingFirstElection {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g first index inst leader : Nat} {e : Event}
    (hFirst : X.Elect (g, first) 2153 (2 ^ 32 - 1) inst leader)
    (he : X.get (g, index) = some e) (hLater : first < index) : 2153 < e.pc := by
  have hg := event_thread_lt hX he
  obtain ⟨_, hr⟩ := hX.thr g hg
  have hLen : index < (X.tr g).length := len_of_get he
  obtain ⟨s, u, hStep, hRun⟩ := hr.after_event hFirst (by omega)
  have hPc : s.pc = 2153 := (estep_source_pc hStep).symm
  obtain ⟨ins, hc, _, hFire⟩ := estep_event_source hStep
  rw [hPc, Flow.code_2153] at hc
  obtain rfl := Option.some.inj hc.symm
  obtain ⟨_, _, _, _, rfl⟩ := fires_elect hFire
  obtain ⟨visits, hw⟩ := walkFromRun hRun
  have hSeen : e ∈ (X.tr g).drop (first + 1) := by
    apply List.mem_of_getElem? (i := index - (first + 1))
    rwa [List.getElem?_drop, Nat.add_sub_of_le (show first + 1 ≤ index by omega)]
  apply Nat.lt_of_succ_le
  apply eventTailEvents afterOpeningElectionFloor afterOpeningElectionSegments hw _ _ hSeen
  change 2154 ≤ s.pc + 1
  omega

private def scoreOpeningElections : List Nat :=
  prefixElections ++ steadyElections ++ tailElections

set_option maxRecDepth 100000 in
private theorem scoreOpeningElectAudit :
    (((kernel.code.drop 2154).take (2763 - 2154)).zipIdx 2154).all
      (fun (ins, pos) => !electOp ins.op || scoreOpeningElections.contains pos) = true := by
  kernel_rfl

private theorem scoreOpeningElectionSite {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g index pos mask inst leader : Nat}
    (he : X.Elect (g, index) pos mask inst leader) (hLo : 2153 < pos) (hHi : pos < 2763) :
    pos ∈ scoreOpeningElections := by
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hBad
  have hElect : electOp ins.op = true := by
    cases hk : electOp ins.op
    · exact (fires_notElect (eventTmpl_notElect hk) hf _ _ _ rfl).elim
    · rfl
  have hMem : (ins, pos) ∈ ((kernel.code.drop 2154).take (2763 - 2154)).zipIdx 2154 := by
    apply List.mem_of_getElem? (i := pos - 2154)
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le (show 2154 ≤ pos by omega), hc]
    rfl
  have h := List.all_eq_true.mp scoreOpeningElectAudit _ hMem
  simpa only [hElect, Bool.not_true, Bool.false_or, List.contains_iff_mem] using h

/-- The two opening score elections occur before either recurring score election. -/
theorem openingScoreElectionBeforeRecurring (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g index pos inst leader : Nat}
    (he : X.Elect (g, index) pos (2 ^ 32 - 1) inst leader) (hSite : pos = 2415 ∨ pos = 2516)
    (hWarp : warpIndex l g = 12) :
    ∃ j < index, ∃ inst', X.Elect (g, j) (if stage = 0 then 2205 else 2267)
      (2 ^ 32 - 1) inst' leader := by
  obtain ⟨first, inst₀, lead₀, n, hFirst, hStart, hZero, hRank, _⟩ :=
    actualCollectiveRanks hp hX he hWarp (show 2153 < pos ∧ pos < 2763 by omega)
  change elections X g index = electionOffset pos + 8 * n at hRank
  let target := if stage = 0 then 1 else 3
  have hSmall : target ≤ 3 := by fin_cases stage <;> decide
  have hOffsetBound : 3 < electionOffset pos := by rcases hSite with rfl | rfl <;> decide
  have hLimit : target < elections X g index := by omega
  obtain ⟨j, hj, event, hEvent, hMark, hCount⟩ :=
    Flow.exists_nth isElectEv (X.tr g) (n := target) (k := index) hLimit
  change elections X g j = target at hCount
  have hAfter : first < j := by
    by_contra! hBefore
    have hMono := countP_take_mono isElectEv (X.tr g) hBefore
    change elections X g j ≤ elections X g first at hMono
    rw [hZero, hCount] at hMono
    have hPositive : 0 < target := by fin_cases stage <;> decide
    omega
  have hLo := followingFirstElection hX hFirst hEvent hAfter
  have hHi : event.pc < 2763 := by
    by_contra! hLate
    have hContra := traceOrderOfPcFloor hX afterMmaFloor afterMmaSegments he
      (show X.get (g, j) = some event from hEvent) (show pos < 2763 by omega) hLate
    omega
  obtain ⟨tag, kind⟩ := event
  cases kind <;> simp [isElectEv] at hMark
  case elect mask inst' leader' =>
    have hRaw : X.Elect (g, j) tag mask inst' leader' := hEvent
    have hMask := actualFullElectionMask hX hRaw
    subst mask
    have hSites := scoreOpeningElectionSite hX hRaw hLo hHi
    obtain ⟨_, _, _, k, _, _, _, hOffset, _⟩ :=
      actualCollectiveRanks hp hX hRaw hWarp ⟨hLo, hHi⟩
    rw [hCount] at hOffset
    change target = electionOffset tag + 8 * k at hOffset
    have hTag : tag = if stage = 0 then 2205 else 2267 := by
      have hAudit : ∀ stage : Fin 2, ∀ tag ∈ scoreOpeningElections, 2153 < tag →
          electionOffset tag = (if stage = 0 then 1 else 3) →
          tag = (if stage = 0 then 2205 else 2267) := by decide +revert
      have hZero : k = 0 := by omega
      have hRank : electionOffset tag = target := by omega
      exact hAudit stage tag hSites hLo hRank
    have hg := event_thread_lt hX he
    have hLead := sameLeader hX (show SameWarp l g g from ⟨⟨hg, hg, rfl⟩, rfl⟩) hRaw he
    exact ⟨j, hj, inst', hTag ▸ hLead ▸ hRaw⟩

private theorem notTailShuffle (pos : Nat) (hpos : 2763 ≤ pos)
    {ins : Instr} (hGet : kernel.code[pos]? = some ins)
    (hEnd : pos < 2768 ∨ pos = 9205) : ins.op.isShfl = false := by
  rcases hEnd with h | rfl
  · have hCheck : ((kernel.code.drop 2763).take 5).all
        (fun i => !i.op.isShfl) = true := by set_option maxRecDepth 100000 in kernel_rfl
    have hMem : ins ∈ (kernel.code.drop 2763).take 5 := by
      apply List.mem_of_getElem? (i := pos-2763)
      rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,
        Nat.add_sub_of_le hpos,hGet]
    simpa using List.all_eq_true.mp hCheck _ hMem
  · rw [Flow.code_9205] at hGet
    obtain rfl := Option.some.inj hGet
    rfl

private theorem liveShuffleWithElection (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {event : Event}
    (he : X.get (g,j) = some event) (hWarp : warpIndex l g = 12) (hJ : 3 ≤ j)
    (hShfl : Execution.isShfl event = true) (hPositive : 0 < elections X g j) :
    2153 < event.pc ∧ event.pc < 2763 := by
  obtain ⟨s,vs,hJ6,hs,hWalk,hFence,hBar,inst,hHint⟩ :=
    mmaRoleWalkOfDemand hp hX he hWarp (.inr ⟨hJ,hShfl⟩)
  have hBefore : ∀ {index event}, 6 ≤ index → X.get (g,index) = some event →
      event.pc = 9205 ∨ 1908 ≤ event.pc ∧ event.pc < 2768 := by
    intro position ev hPos hGet
    have hMem : ev ∈ (X.tr g).drop 6 := by
      apply List.mem_of_getElem? (i := position-6)
      rwa [List.getElem?_drop,Nat.add_sub_of_le hPos]
    simpa only [roleBodyPc,show ¬ 14 ≤ (12 : Nat) by decide,show (12 : Nat) ≠ 13 by decide,
      ↓reduceIte] using roleBodyEventPcs (⟨12,by decide⟩ : Fin 16) hs hWalk ev hMem
  obtain ⟨k,hK,ev,hGet,hElect,_⟩ :=
    Flow.exists_nth isElectEv (X.tr g) (n := 0) (k := j) hPositive
  change X.get (g,k) = some ev at hGet
  have hK6 : 6 ≤ k := by
    by_contra! hEarly
    have hCount := startupWithoutElections hp hX (event_thread_lt hX he) hFence hBar hHint
    have hP := countP_take_succ (X := X) (g := g) (j := k) hGet hElect
    have hMono := countP_take_mono isElectEv (X.tr g) (show k+1 ≤ 6 by omega)
    unfold elections at hCount
    rw [hCount,hP] at hMono
    omega
  have hElectPc : 2153 ≤ ev.pc := by
    rcases hBefore hK6 hGet with h | ⟨hLo,_⟩
    · omega
    · by_contra! hHi
      rcases get_source hX hGet with ⟨_,hFault⟩ | ⟨t,ins,o,_,hCode,hFire⟩
      · obtain ⟨p,kind⟩ := ev
        change kind = _ at hFault
        subst kind
        cases hElect
      · have hNone := (Bool.and_eq_true_iff.mp (preElectionAt hLo hHi hCode)).1
        have hNot : electOp ins.op = false := by simpa using hNone
        obtain ⟨pc,kind⟩ := ev
        cases kind <;> try cases hElect
        exact (fires_notElect (eventTmpl_notElect hNot) hFire _ _ _ rfl).elim
  have hAfter : 2153 ≤ event.pc := by
    by_contra! hEarly
    have hOrder := traceOrderOfPcFloor hX afterFirstFloor afterFirstSegments he hGet
      hEarly hElectPc
    omega
  have hBound : event.pc < 2763 := by
    by_contra! hLate
    have hP : event.pc < 2768 ∨ event.pc = 9205 := by
      rcases hBefore hJ6 he with h | ⟨_,h⟩
      · exact .inr h
      · exact .inl h
    rcases get_source hX he with ⟨_,hFault⟩ | ⟨t,ins,o,_,hCode,hFire⟩
    · obtain ⟨p,kind⟩ := event
      change kind = _ at hFault
      subst kind
      cases hShfl
    · exact Bool.noConfusion ((notTailShuffle _ hLate hCode hP).symm.trans
        (fires_shfl_op hFire hShfl))
  have hNot : event.pc ≠ 2153 := by
    intro hPc
    rcases get_source hX he with ⟨_,hFault⟩ | ⟨t,ins,o,_,hCode,hFire⟩
    · obtain ⟨p,kind⟩ := event
      change kind = _ at hFault
      subst kind
      cases hShfl
    · rw [hPc,Flow.code_2153] at hCode
      obtain rfl := Option.some.inj hCode
      cases (fires_shfl_op hFire hShfl)
  exact ⟨by omega,hBound⟩

def descriptorShuffleSite : Fin 3 → Nat
  | 0 => 2308
  | 1 => 2559
  | _ => 2361

/-- The output-column broadcast at the start of a steady PV block. -/
def steadyOutputShuffleSite : Fin 2 → Nat
  | 0 => 2310
  | _ => 2425

private def operandBroadcastSite : Fin 7 → Nat
  | 0 => 2308
  | 1 => 2559
  | 2 => 2361
  | 3 => 2310
  | 4 => 2425
  | 5 => 2558
  | _ => 2599

private def arithmeticShuffleSites : List Nat := prefixShuffles ++ steadyShuffles ++ tailShuffles

set_option maxRecDepth 100000 in
private theorem arithmeticShufflesCode :
    (((kernel.code.drop 2154).take (2654-2154)).zipIdx 2154).all
      (fun (ins,pos) => !ins.op.isShfl || arithmeticShuffleSites.contains pos) = true := by
  kernel_rfl

private theorem beforeTailShuffleSite {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {e : Event}
    (he : X.get (g,j) = some e) (hShfl : Execution.isShfl e = true)
    (hLo : 2153 < e.pc) (hHi : e.pc < 2654) : e.pc ∈ arithmeticShuffleSites := by
  rcases get_source hX he with ⟨_,hFault⟩ | ⟨t,ins,o,_,hCode,hFire⟩
  · obtain ⟨p,kind⟩ := e
    change kind = _ at hFault
    subst kind
    cases hShfl
  · let code := ((kernel.code.drop 2154).take (2654-2154)).zipIdx 2154
    have hMem : (ins,e.pc) ∈ code := by
      apply List.mem_of_getElem? (i := e.pc-2154)
      dsimp only [code]
      rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
        Nat.add_sub_of_le (show 2154 ≤ e.pc by omega),hCode]
      rfl
    have h := List.all_eq_true.mp arithmeticShufflesCode (ins,e.pc) hMem
    simpa only [fires_shfl_op hFire hShfl,Bool.not_true,Bool.false_or,
      List.contains_iff_mem] using h

private theorem descriptorOffsetUnique (slot : Fin 7) {pos n k : Nat}
    (hPc : pos ∈ arithmeticShuffleSites)
    (hE : electionOffset (operandBroadcastSite slot)+8*n = electionOffset pos+8*k)
    (hS : shuffleOffset (operandBroadcastSite slot)+6*n = shuffleOffset pos+6*k) :
    pos = operandBroadcastSite slot := by
  simp only [arithmeticShuffleSites,prefixShuffles,steadyShuffles,tailShuffles,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hPc
  rcases hPc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases slot <;> first | rfl |
      (simp [operandBroadcastSite,electionOffset,shuffleOffset,beforeSite,
        prefixShuffles,prefixElections,steadyShuffles,steadyElections,tailShuffles,
        tailElections] at hE hS; omega)

private theorem laterElectionOffset {pos : Nat} (h : 2654 ≤ pos) : electionOffset pos = 12 := by
  have h2534 : ¬ pos < 2534 := by omega
  have h2291 : ¬ pos < 2291 := by omega
  have h2534' : 2534 < pos := by omega
  have h2538 : 2538 < pos := by omega
  have h2562 : 2562 < pos := by omega
  have h2602 : 2602 < pos := by omega
  have h2635 : 2635 < pos := by omega
  have h2639 : 2639 < pos := by omega
  have h2643 : 2643 < pos := by omega
  simp [electionOffset,beforeSite,tailElections,h2534,h2291,
    h2534',h2538,h2562,h2602,h2635,h2639,h2643]

private theorem firstThreeShuffles (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (h : 3 ≤ (X.tr g).length) :
    ((X.tr g).take 3).countP Execution.isShfl = 3 := by
  let xs := X.tr g
  have h0 : 0 < xs.length := by dsimp only [xs]; omega
  have h1 : 1 < xs.length := by dsimp only [xs]; omega
  have h2 : 2 < xs.length := by dsimp only [xs]; omega
  have hF := Prologue.firstSharedValue hp hX g hg (List.getElem?_eq_getElem h0)
  have hM := Prologue.secondWarpValue hp hX g hg (List.getElem?_eq_getElem h1)
  have hL := Prologue.thirdWarpValue hp hX g hg (List.getElem?_eq_getElem h2)
  change (xs.take 3).countP Execution.isShfl = 3
  rw [List.take_succ_eq_append_getElem h2,List.take_succ_eq_append_getElem h1,
    List.take_succ_eq_append_getElem h0,hF,hM,hL]
  rfl

private theorem operandBroadcastSource (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (station : Fin 7) {g index ordinal : Nat}
    {sent recv : Value} {ok : Bool} (hWarp : warpIndex l g = 12)
    (he : X.get (g,index) = some ⟨operandBroadcastSite station,.shfl .idx sent 0 31 recv ok⟩)
    (hOrdinal : X.ShflK (g,index) ordinal) :
    ∃ j a b reply valid, X.ShflK (g-laneOf l g,j) ordinal ∧
      X.get (g-laneOf l g,j) =
        some ⟨operandBroadcastSite station,.shfl .idx recv a b reply valid⟩ := by
  let target := operandBroadcastSite station
  let peer := g-laneOf l g
  have ht : 2153 < target ∧ target < 2654 := by fin_cases station <;> decide
  have hWidth : target < 2763 := by omega
  obtain ⟨j,site,b,c,reply,valid,hOrd,hGet⟩ :=
    mmaLaneZeroShuffleSource hp hX hWarp he hOrdinal hWidth
  have hg := event_thread_lt hX he
  have hw : SameWarp l g peer := (laneZero_sameWarp (by rw [hp.block]; decide) hg).1
  have hW' : warpIndex l peer = 12 := hw.2.symm.trans hWarp
  have hElect := electionCountAtMatchedShuffle hX hw he hOrdinal hGet hOrd
  obtain ⟨anchor,inst,lead,n,hAnchor,_,hE0,hE,hS⟩ :=
    actualCollectiveRanks hp hX he hWarp ⟨ht.1,hWidth⟩
  obtain ⟨_,_,hi,_,_,_,_,_⟩ := mmaRoleWalkOfDemand hp hX he hWarp
    (.inl (show 1907 < target by omega))
  have hLen : index < (X.tr g).length := hOrdinal.lt
  have hCount3 := firstThreeShuffles hp hX (g := g) hg (show 3 ≤ (X.tr g).length by omega)
  have hOrdinal3 : 3 ≤ ordinal := by
    have hLe := countP_take_mono Execution.isShfl (X.tr g) (show 3 ≤ index by omega)
    rw [hCount3,hOrdinal.2] at hLe
    exact hLe
  have hj : 3 ≤ j := hOrdinal3.trans
    (hOrd.2 ▸ countP_take_le_length Execution.isShfl (X.tr peer) j)
  have hPos : 0 < elections X peer j := by
    rw [← hElect,hE]
    change 0 < electionOffset target+8*n
    fin_cases station <;> first | (change 0 < 5+8*n; omega) |
      (change 0 < 7+8*n; omega) | (change 0 < 6+8*n; omega) | (change 0 < 8+8*n; omega)
  have hPeerPc := liveShuffleWithElection hp hX hGet hW' hj rfl hPos
  obtain ⟨anchor',inst',lead',k,hAnchor',_,hE0',hE',hS'⟩ :=
    actualCollectiveRanks hp hX hGet hW' hPeerPc
  have countE : electionOffset target+8*n = electionOffset site+8*k :=
    hE.symm.trans (hElect.trans hE')
  have hPeerBefore : site < 2654 := by
    by_contra! hLater
    rw [laterElectionOffset hLater] at countE
    fin_cases station <;>
      first | (change 5+8*n = 12+8*k at countE; omega) |
        (change 7+8*n = 12+8*k at countE; omega) |
        (change 6+8*n = 12+8*k at countE; omega) |
        (change 8+8*n = 12+8*k at countE; omega)
  obtain ⟨j',hPartner⟩ := ElectOrd.partner hX hw hAnchor (by
    have hLane : laneOf l peer < 32 := Nat.mod_lt _ (by decide)
    refine ⟨hLane,?_⟩
    rw [Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
    exact hLane)
  have hPair : ElectOrd.Partner X (g,anchor) (peer,anchor') := by
    obtain ⟨p₀,p₁,m₀,m₁,inst₂,l₀,l₁,hP₀,hP₁⟩ := hPartner
    have hMut : ElectMutual l X := ElectMutual.of_full (actualFullElectionMask hX)
    have hBefore := electOrdinal hX hMut hw hP₀ hP₁
    have hBefore' : elections X peer j' = 0 := hBefore.symm.trans hE0
    have hOnce := Flow.eq_of_count_eq isElectEv (X.tr peer) hP₁ rfl hAnchor' rfl
      (hBefore'.trans hE0'.symm)
    change j' = anchor' at hOnce
    subst j'
    exact ⟨p₀,p₁,m₀,m₁,inst₂,l₀,l₁,hP₀,hP₁⟩
  have hAnchorCount := shuffleCountAtMatchedElection hX hw hPair
  have hCountS := hOrdinal.2.trans hOrd.2.symm
  have hs := hS ht.2
  have hs' := hS' hPeerBefore
  change ((X.tr g).take index).countP Execution.isShfl =
    ((X.tr g).take anchor).countP Execution.isShfl + shuffleOffset target + 6*n at hs
  change ((X.tr peer).take j).countP Execution.isShfl =
    ((X.tr peer).take anchor').countP Execution.isShfl + shuffleOffset site + 6*k at hs'
  have countS : shuffleOffset target+6*n = shuffleOffset site+6*k := by
    change ((X.tr g).take index).countP Execution.isShfl =
      ((X.tr peer).take j).countP Execution.isShfl at hCountS
    omega
  have hEqual := descriptorOffsetUnique station (beforeTailShuffleSite hX hGet rfl
    hPeerPc.1 hPeerBefore) countE countS
  exact ⟨j,b,c,reply,valid,hOrd,hEqual ▸ hGet⟩

/-- A key or value descriptor broadcast has a live lane-zero sender at the same station. -/
theorem cacheDescriptorShuffleSource (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (station : Fin 3) {g index ordinal : Nat} {sent recv : Value} {ok : Bool}
    (hWarp : warpIndex l g = 12)
    (he : X.get (g,index) = some ⟨descriptorShuffleSite station,.shfl .idx sent 0 31 recv ok⟩)
    (hOrdinal : X.ShflK (g,index) ordinal) :
    ∃ j a b reply valid, X.ShflK (g-laneOf l g,j) ordinal ∧
      X.get (g-laneOf l g,j) =
        some ⟨descriptorShuffleSite station,.shfl .idx recv a b reply valid⟩ := by
  let q : Fin 7 := ⟨station.val,station.isLt.trans (by decide)⟩
  have hs : operandBroadcastSite q = descriptorShuffleSite station := by fin_cases station <;> rfl
  simpa only [hs] using operandBroadcastSource hp hX q hWarp (hs.symm ▸ he) hOrdinal

/-- A steady output-column broadcast has a live lane-zero sender at the same station. -/
theorem steadyOutputShuffleSource (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g index ordinal : Nat} {sent recv : Value} {ok : Bool}
    (hWarp : warpIndex l g = 12)
    (he : X.get (g,index) = some ⟨steadyOutputShuffleSite stage,.shfl .idx sent 0 31 recv ok⟩)
    (hOrdinal : X.ShflK (g,index) ordinal) :
    ∃ j a b reply valid, X.ShflK (g-laneOf l g,j) ordinal ∧
      X.get (g-laneOf l g,j) =
        some ⟨steadyOutputShuffleSite stage,.shfl .idx recv a b reply valid⟩ := by
  let q : Fin 7 := ⟨3+stage.val,by have := stage.isLt; omega⟩
  have hs : operandBroadcastSite q = steadyOutputShuffleSite stage := by fin_cases stage <;> rfl
  simpa only [hs] using operandBroadcastSource hp hX q hWarp (hs.symm ▸ he) hOrdinal

/-- The two probability-column broadcasts of the final PV groups. -/
def tailProbabilityColumnShuffleSite : Fin 2 → Nat
  | 0 => 2558
  | _ => 2599

/-- A tail probability broadcast receives its value from the same station of lane zero. -/
theorem tailProbabilityColumnShuffleSource (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g index ordinal : Nat}
    {sent recv : Value} {ok : Bool} (hWarp : warpIndex l g = 12)
    (he : X.get (g,index) = some ⟨tailProbabilityColumnShuffleSite stage,
      .shfl .idx sent 0 31 recv ok⟩) (hOrdinal : X.ShflK (g,index) ordinal) :
    ∃ j a b reply valid, X.ShflK (g-laneOf l g,j) ordinal ∧
      X.get (g-laneOf l g,j) = some ⟨tailProbabilityColumnShuffleSite stage,
        .shfl .idx recv a b reply valid⟩ := by
  let q : Fin 7 := ⟨5+stage.val,by have := stage.isLt; omega⟩
  have hs : operandBroadcastSite q = tailProbabilityColumnShuffleSite stage := by
    fin_cases stage <;> rfl
  simpa only [hs] using operandBroadcastSource hp hX q hWarp (hs.symm ▸ he) hOrdinal

end
end PTX.Kernels.TmlFa4Fwd.Thread
