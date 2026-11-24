-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasLeader
import Kernels.TmlFa4Fwd.Proof.LoaderDrainPoll
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
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Lemmas.Flow.ContinuingEvent
import Lemmas.Flow.Tc
import Kernels.TmlFa4Fwd.Flow.Code.Part039
import Kernels.TmlFa4Fwd.Flow.Code.Part040
import Kernels.TmlFa4Fwd.Flow.Code.Part041
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Lemmas.Flow.CountTake
public import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasRead
import Kernels.TmlFa4Fwd.Flow.Code.Part068
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part054
import Kernels.TmlFa4Fwd.Flow.Code.Part055
import Kernels.TmlFa4Fwd.Flow.Code.Part055
import Kernels.TmlFa4Fwd.Flow.Code.Part056
import Kernels.TmlFa4Fwd.Flow.Code.Part080
import Kernels.TmlFa4Fwd.Flow.Code.Part081
import Kernels.TmlFa4Fwd.Flow.Code.Part082
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part076
import Kernels.TmlFa4Fwd.Flow.Code.Part079
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Loader (DrainWaitSite LoaderWaitCode)

private def biasWindowWait : Fin 22 → DrainWaitSite
  | 0 | 15 | 20 => ⟨3498, 9752, 2771, 2770⟩
  | 1 | 21 => ⟨5181, 9755, 3965, 7250⟩
  | 2 | 3 | 8 | 17 => ⟨3425, 9751, 2769, 2770⟩
  | 4 | 5 | 9 | 18 => ⟨5109, 9754, 3964, 7253⟩
  | 6 | 7 | 10 | 19 => ⟨6676, 9821, 5126, 7253⟩
  | 11 => ⟨2548, 9726, 2610, 7205⟩
  | 12 => ⟨2595, 9737, 2615, 7205⟩
  | 13 => ⟨8473, 9888, 6495, 6496⟩
  | 14 => ⟨8769, 9890, 6499, 6496⟩
  | _ => ⟨5181, 9755, 3965, 7250⟩

private def biasWindowEnd : Fin 22 → Nat
  | 0 => 3590
  | 1 => 5278
  | 2 => 4847
  | 3 => 4867
  | 4 => 6532
  | 5 => 6552
  | 6 => 7437
  | 7 => 7457
  | 8 => 4397
  | 9 => 5683
  | 10 => 6891
  | 11 => 2642
  | 12 => 2646
  | 13 => 8759
  | 14 => 9055
  | 15 => 4397
  | 16 => 5683
  | 17 => 4858
  | 18 => 6543
  | 19 => 7448
  | 20 => 3583
  | _ => 5271

private theorem biasWindowCode (i : Fin 22) : LoaderWaitCode (biasWindowWait i) := by
  fin_cases i
  · exact ⟨Flow.code_3498, Flow.code_3499, Flow.code_3500⟩
  · exact ⟨Flow.code_5181, Flow.code_5182, Flow.code_5183⟩
  · exact ⟨Flow.code_3425, Flow.code_3426, Flow.code_3427⟩
  · exact ⟨Flow.code_3425, Flow.code_3426, Flow.code_3427⟩
  · exact ⟨Flow.code_5109, Flow.code_5110, Flow.code_5111⟩
  · exact ⟨Flow.code_5109, Flow.code_5110, Flow.code_5111⟩
  · exact ⟨Flow.code_6676, Flow.code_6677, Flow.code_6678⟩
  · exact ⟨Flow.code_6676, Flow.code_6677, Flow.code_6678⟩
  · exact ⟨Flow.code_3425, Flow.code_3426, Flow.code_3427⟩
  · exact ⟨Flow.code_5109, Flow.code_5110, Flow.code_5111⟩
  · exact ⟨Flow.code_6676, Flow.code_6677, Flow.code_6678⟩
  · exact ⟨Flow.code_2548, Flow.code_2549, Flow.code_2550⟩
  · exact ⟨Flow.code_2595, Flow.code_2596, Flow.code_2597⟩
  · exact ⟨Flow.code_8473, Flow.code_8474, Flow.code_8475⟩
  · exact ⟨Flow.code_8769, Flow.code_8770, Flow.code_8771⟩
  · exact ⟨Flow.code_3498, Flow.code_3499, Flow.code_3500⟩
  · exact ⟨Flow.code_5181, Flow.code_5182, Flow.code_5183⟩
  · exact ⟨Flow.code_3425, Flow.code_3426, Flow.code_3427⟩
  · exact ⟨Flow.code_5109, Flow.code_5110, Flow.code_5111⟩
  · exact ⟨Flow.code_6676, Flow.code_6677, Flow.code_6678⟩
  · exact ⟨Flow.code_3498, Flow.code_3499, Flow.code_3500⟩
  · exact ⟨Flow.code_5181, Flow.code_5182, Flow.code_5183⟩

private def insideBiasBody (window : Fin 22) (pc : Nat) : Prop :=
  (biasWindowWait window).pc + 3 ≤ pc ∧ pc ≤ biasWindowEnd window

private instance (window : Fin 22) (pc : Nat) : Decidable (insideBiasBody window pc) :=
  inferInstanceAs (Decidable ((biasWindowWait window).pc + 3 ≤ pc ∧ pc ≤ biasWindowEnd window))

private noncomputable def biasBodyDebt (window : Fin 22) (s : TState) : Nat :=
  if s.pc = (biasWindowWait window).pc + 1 then
    if s.regs (biasWindowWait window).result = some (.pred true) then 1 else 0
  else if insideBiasBody window s.pc then 1 else 0

private def biasAcquireMark (window : Fin 22) (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true _ _ => e.pc == (biasWindowWait window).pc
  | _ => false

/-- Marks successful waits for a Bias-ready stage. -/
def readSuccess (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true _ _ => e.pc == 3498 || e.pc == 5181
  | _ => false

private def biasReturnMark (window : Fin 22) (e : Event) : Bool :=
  e.pc == biasWindowEnd window

private def biasWindowEdge (window : Fin 22) (src dst : Nat) : Bool :=
  decide (dst ≠ (biasWindowWait window).pc + 1 ∧
    (insideBiasBody window dst → insideBiasBody window src))

private def biasWindowBranch (window : Fin 22) (src : Nat) (op : Op) : Bool :=
  match op with
  | .bra dst _ => (src == (biasWindowWait window).pc + 1) || biasWindowEdge window src dst
  | .brx .. => false
  | _ => true

private def biasWindowBranches (window : Fin 22) : Bool :=
  (kernel.code.zipIdx 0).all (fun (ins,site) => biasWindowBranch window site ins.op)

private theorem earlyBiasWindowBranches (window : Fin 15) :
    biasWindowBranches ⟨window.val, window.isLt.trans (by decide)⟩ = true := by
  fin_cases window <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem firstBiasStatisticsBranches : biasWindowBranches 15 = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem repeatedBiasStatisticsBranches : biasWindowBranches 16 = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem tailWarpBranches (window : Fin 5) :
    biasWindowBranches ⟨17+window.val, by have := window.isLt; omega⟩ = true := by
  fin_cases window <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem biasWindowBranchAt (window : Fin 22) {pc : Nat} {ins : Instr}
    (hc : kernel.code[pc]? = some ins) : biasWindowBranch window pc ins.op = true := by
  have hAll : biasWindowBranches window = true := by
    by_cases h : window.val < 15
    · exact earlyBiasWindowBranches ⟨window.val,h⟩
    by_cases h15 : window.val = 15
    · obtain rfl : window = 15 := Fin.ext h15
      exact firstBiasStatisticsBranches
    by_cases h16 : window.val = 16
    · obtain rfl : window = 16 := Fin.ext h16
      exact repeatedBiasStatisticsBranches
    let tail : Fin 5 := ⟨window.val-17,by have := window.isLt; omega⟩
    have he : (⟨17+tail.val,by have := tail.isLt; omega⟩ : Fin 22) = window := by
      apply Fin.ext
      dsimp only [tail]
      omega
    exact he ▸ tailWarpBranches tail
  exact List.all_eq_true.mp hAll (ins,pc) (List.mem_zipIdx_iff_getElem?.mpr hc)

private noncomputable def windowsKeepSegment (start : Nat) : Bool :=
  match cuteExp2.matchAt kernel start with
  | some block => (List.finRange 22).all (fun window => biasWindowEdge window start block.stop)
  | none => false

set_option maxRecDepth 100000 in
private theorem biasWindowSegmentAudit :
    Assumptions.swExp2Sites.all windowsKeepSegment = true := by kernel_rfl

private theorem biasWindowSegment (window : Fin 22) {pc : Nat} {seg : SegMatch CuteSlot}
    (hSite : pc ∈ Assumptions.swExp2Sites) (hSeg : cuteExp2.matchAt kernel pc = some seg) :
    biasWindowEdge window pc seg.stop = true := by
  have h := List.all_eq_true.mp biasWindowSegmentAudit _ hSite
  unfold windowsKeepSegment at h
  rw [hSeg] at h
  exact List.all_eq_true.mp h _ (List.mem_finRange window)

private theorem biasWindowReleaseCode (window : Fin 22) :
    (∃ ins, kernel.code[biasWindowEnd window]? = some ins ∧ barOp ins.op = true) ∨
    (∃ base off, kernel.code[biasWindowEnd window]? =
      some ⟨none, .tcCommit .one base off none⟩) ∨
    (∃ (base : Nat) (off : Int) (count out : Nat),
      kernel.code[biasWindowEnd window]? = some
        ⟨none, .mbarArrive base off (.imm 0) (.reg count) false true .cta (some out)⟩) ∨
    kernel.code[biasWindowEnd window]? = some
      ⟨none,.warp ⟨.barWarp,none,[],[],some (.imm (-1))⟩⟩ := by
  fin_cases window
  · exact .inr (.inr (.inl ⟨_, _, _, _, Flow.code_3590⟩))
  · exact .inr (.inr (.inl ⟨_, _, _, _, Flow.code_5278⟩))
  · exact .inr (.inr (.inl ⟨_, _, _, _, Flow.code_4847⟩))
  · exact .inr (.inr (.inl ⟨_, _, _, _, Flow.code_4867⟩))
  · exact .inr (.inr (.inl ⟨_, _, _, _, Flow.code_6532⟩))
  · exact .inr (.inr (.inl ⟨_, _, _, _, Flow.code_6552⟩))
  · exact .inr (.inr (.inl ⟨_, _, _, _, Flow.code_7437⟩))
  · exact .inr (.inr (.inl ⟨_, _, _, _, Flow.code_7457⟩))
  · exact .inl ⟨_, Flow.code_4397, rfl⟩
  · exact .inl ⟨_, Flow.code_5683, rfl⟩
  · exact .inl ⟨_, Flow.code_6891, rfl⟩
  · exact .inr (.inl ⟨_, _, Flow.code_2642⟩)
  · exact .inr (.inl ⟨_, _, Flow.code_2646⟩)
  · exact .inr (.inr (.inl ⟨_, _, _, _, Flow.code_8759⟩))
  · exact .inr (.inr (.inl ⟨_, _, _, _, Flow.code_9055⟩))
  · exact .inl ⟨_, Flow.code_4397, rfl⟩
  · exact .inl ⟨_, Flow.code_5683, rfl⟩
  · exact .inr (.inr (.inr Flow.code_4858))
  · exact .inr (.inr (.inr Flow.code_6543))
  · exact .inr (.inr (.inr Flow.code_7448))
  · exact .inl ⟨_, Flow.code_3583, rfl⟩
  · exact .inl ⟨_, Flow.code_5271, rfl⟩

private theorem releaseAdvances {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (window : Fin 22) (hS : s.pc = biasWindowEnd window)
    (he : EStep kernel Assumptions.all l g s e (some u)) : u.pc = s.pc + 1 := by
  rcases biasWindowReleaseCode window with ⟨ins, hc, hMarked⟩ | ⟨base,off,hc⟩ |
    ⟨base, off, count, word, hc⟩ | hc
  · exact followsMarkedBarrier hS hc hMarked he
  · obtain ⟨ins, hCode, _, hFire⟩ := estep_event_source he
    rw [hS,hc] at hCode
    obtain rfl := Option.some.inj hCode
    obtain rfl := fires_tcCommit hFire
    rfl
  · obtain ⟨ins, hRead, _, hFire⟩ := estep_event_source he
    rw [hS, hc] at hRead
    obtain rfl := Option.some.inj hRead
    have hWide : (Assumptions.all.any (·.clusterScopeMbar s.pc)) = false := rfl
    have hZero : readBits l g s 32 (.imm 0) = .ok 0#64 := rfl
    simp only [eventTmpl, hWide, widenMbarScope, tmaTmpl, hZero,
      bind, Except.bind, pure, Except.pure] at hFire
    cases ha : mbarLoc l g s base off
    · simp [ha, ofExec, Fires] at hFire
    · cases hb : readBits l g s 32 (.reg count)
      · simp [ha, hb, ofExec, Fires] at hFire
      · simp only [ha, hb, ofExec, Fires] at hFire
        obtain ⟨_, hU⟩ := hFire
        obtain rfl := Option.some.inj hU
        rfl
  · obtain ⟨_,hCode,_,hFire⟩ := estep_event_source he
    rw [hS,hc] at hCode
    obtain rfl := Option.some.inj hCode
    change Fires s.pc (warpBarTmpl l g s (.imm (-1))) e (some u) at hFire
    have hMask : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2^32-1 := by decide
    by_cases hMember : electMember (2^32-1) (laneOf l g)
    · simp only [warpBarTmpl,readBits,pure,Except.pure,hMask,hMember,↓reduceIte,Fires] at hFire
      obtain ⟨_,_,hAfter⟩ := hFire
      obtain rfl := Option.some.inj hAfter
      rfl
    · simp only [warpBarTmpl,readBits,pure,Except.pure,hMask,ite_eq_right hMember,Fires,
        reduceCtorEq, and_false] at hFire

private theorem biasBodyDebtEdge {s u : TState} (window : Fin 22)
    (hEdge : biasWindowEdge window s.pc u.pc = true) : biasBodyDebt window u ≤
      biasBodyDebt window s := by
  obtain ⟨hDst, hLive⟩ := of_decide_eq_true hEdge
  unfold biasBodyDebt
  rw [ite_eq_right hDst]
  by_cases hu : insideBiasBody window u.pc
  · have hs := hLive hu
    have hNo : s.pc ≠ (biasWindowWait window).pc + 1 := by
      unfold insideBiasBody at hs
      omega
    simp [hu, hs, hNo]
  · simp [hu]

private theorem biasBodyDebtNext {s u : TState} (window : Fin 22)
    (hn : u.pc = s.pc + 1) (hW : s.pc ≠ (biasWindowWait window).pc)
    (hG : s.pc ≠ (biasWindowWait window).pc + 2) : biasBodyDebt window u ≤
      biasBodyDebt window s := by
  apply biasBodyDebtEdge window
  apply decide_eq_true
  constructor
  · omega
  · unfold insideBiasBody
    omega

private theorem biasWindowGuardReg {s : TState} {reg : Nat}
    (h : guardHolds s (some (reg,false)) = .ok true) : s.regs reg = some (.pred true) := by
  cases hb : s.regs reg
  · simp [guardHolds, readReg, hb, bind, Except.bind, pure, Except.pure] at h
  · rename_i x
    cases x <;> simp [guardHolds, readReg, hb, bind, Except.bind, pure, Except.pure] at h
    rename_i b
    subst b
    rfl

private theorem biasReadOrderStep {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (window : Fin 22) (hStep : WStep kernel Assumptions.all l g s ev u) :
    ev.toList.countP (biasReturnMark window) + biasBodyDebt window u ≤
      ev.toList.countP (biasAcquireMark window) + biasBodyDebt window s := by
  have hBounds : (biasWindowWait window).pc + 3 ≤ biasWindowEnd window := by
    fin_cases window <;> decide
  have hCode := biasWindowCode window
  by_cases hW : s.pc = (biasWindowWait window).pc
  · obtain ⟨addr, q, ok, scope, rfl, rfl⟩ := wstep_poll hStep (hW.symm ▸ hCode.1)
    have hEnd : s.pc ≠ biasWindowEnd window := by omega
    have hU : (next (setReg s (biasWindowWait window).result (.pred ok))).pc =
        (biasWindowWait window).pc + 1 := by
      simp [next, setReg, hW]
    have hR : (next (setReg s (biasWindowWait window).result (.pred ok))).regs
        (biasWindowWait window).result = some (.pred ok) := by
      simp [next, setReg]
    have hS : ¬ insideBiasBody window s.pc := by unfold insideBiasBody; omega
    have hNe : (biasWindowWait window).pc ≠ biasWindowEnd window := by omega
    have hS' : ¬ insideBiasBody window (biasWindowWait window).pc := hW ▸ hS
    cases ok <;> simp [biasBodyDebt, biasAcquireMark, biasReturnMark, hW, hNe, hS', hU, hR]
  have hElse (hpc : u.pc = s.pc ∨ u.pc = s.pc + 1)
      (hC : s.pc ≠ (biasWindowWait window).pc + 1)
      (hR : s.pc ≠ (biasWindowWait window).pc + 2) :
      biasBodyDebt window u ≤ biasBodyDebt window s := by
    rcases hpc with hp | hp
    · apply biasBodyDebtEdge window
      rw [hp]
      simp only [biasWindowEdge, decide_eq_true_eq]
      exact ⟨hC, id⟩
    · exact biasBodyDebtNext window hp hW hR
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · simp only [Option.toList_none, List.countP_nil, Nat.zero_add]
    obtain ⟨ins, hc, _, hExec⟩ := tauScoreSource ht
    by_cases hC : s.pc = (biasWindowWait window).pc + 1
    · rw [hC, hCode.2.1] at hc
      obtain rfl := Option.some.inj hc.symm
      rcases hExec with ⟨rfl, _⟩ | ⟨hGuard, _, hExec⟩
      · have hDst : (skip s).pc = (biasWindowWait window).pc + 2 := by simp [skip, hC]
        have hNo : ¬ insideBiasBody window (skip s).pc := by unfold insideBiasBody; omega
        have hNE : (skip s).pc ≠ (biasWindowWait window).pc + 1 := by omega
        unfold biasBodyDebt
        rw [ite_eq_right hNE, ite_eq_right hNo]
        exact Nat.zero_le _
      · have hr := biasWindowGuardReg hGuard
        have hInv : biasBodyDebt window s = 1 := by simp [biasBodyDebt, hC, hr]
        rw [hInv]
        unfold biasBodyDebt
        split <;> split <;> decide
    by_cases hR : s.pc = (biasWindowWait window).pc + 2
    · rw [hR, hCode.2.2] at hc
      obtain rfl := Option.some.inj hc.symm
      rcases hExec with ⟨_, hSkip⟩ | ⟨_, _, he⟩
      · cases hSkip
      · have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hR]; fin_cases window <;> decide
        rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl,
          execLocalA_nil] at he
        have hDst : u.pc = (biasWindowWait window).pc := by
          have hEq : Except.ok { s with pc := (biasWindowWait window).pc } =
              Except.ok u := he
          exact congrArg TState.pc (Except.ok.inj hEq).symm
        apply biasBodyDebtEdge window
        apply decide_eq_true
        rw [hDst]
        constructor
        · omega
        · unfold insideBiasBody; omega
    rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hExec⟩
    · exact hElse (.inr rfl) hC hR
    · rcases scoreExecLocal hExec with hF | ⟨seg, hs, hm, hr⟩
      · have hPc := hF.pc
        have hBranch := biasWindowBranchAt window hc
        cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
        case bra dest aligned =>
          apply biasBodyDebtEdge window
          rw [hPc]
          simpa [biasWindowBranch, ho, hC] using hBranch
        case brx => simp [biasWindowBranch, ho] at hBranch
        all_goals exact hElse (.inr hPc) hC hR
      · have hEdge := biasWindowSegment window hs hm
        rw [← (scoreSegmentFrame hr).1] at hEdge
        exact biasBodyDebtEdge window hEdge
  · have hPc := estep_source_pc he
    have hMark : biasAcquireMark window e = false := by
      cases hc : e.kind <;> simp [biasAcquireMark, hc, hPc]
      rename_i _ _ ok _ _
      cases ok <;> simp_all
    have hCont {r} (hr : s.pc = (biasWindowWait window).pc + r) (hN : r = 1 ∨ r = 2) : False := by
      obtain ⟨ins, hc, hl, _⟩ := estep_event_source he
      rcases hN with rfl | rfl
      · rw [hr, hCode.2.1] at hc
        obtain rfl := Option.some.inj hc
        cases hl
      · rw [hr, hCode.2.2] at hc
        obtain rfl := Option.some.inj hc
        cases hl
    simp only [Option.toList_some, List.countP_cons, List.countP_nil, hMark, Bool.false_eq_true,
      ↓reduceIte, Nat.zero_add]
    by_cases hEnd : s.pc = biasWindowEnd window
    · have hNext := releaseAdvances window hEnd he
      have hS : insideBiasBody window s.pc := by unfold insideBiasBody; omega
      have hU : ¬ insideBiasBody window u.pc := by unfold insideBiasBody; omega
      have hS' : s.pc ≠ (biasWindowWait window).pc + 1 := by omega
      have hU' : u.pc ≠ (biasWindowWait window).pc + 1 := by omega
      have hStart : biasBodyDebt window s = 1 := by simp [biasBodyDebt, hS', hS]
      have hStop : biasBodyDebt window u = 0 := by simp [biasBodyDebt, hU', hU]
      simp [biasReturnMark, hPc, hEnd, hStart, hStop]
    · have hFalse : biasReturnMark window e = false := by simp [biasReturnMark, hPc, hEnd]
      simp only [hFalse, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      obtain ⟨ins, hc, hl, hFire⟩ := estep_event_source he
      have hAll : kernel.code.all (fun ins => ins.op.isLocal || Epilogue.ordinaryEvent ins.op) =
          true := by decide +kernel
      have hOp := List.all_eq_true.mp hAll _ (List.mem_of_getElem? hc)
      have hF := Epilogue.ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g) (s := s)
        (by simpa only [hl, Bool.false_or] using hOp)
      exact hElse (callbackFrame_fires hF hFire) (fun hs => hCont hs (.inl rfl))
        (fun hs => hCont hs (.inr rfl))

private theorem biasReadOrderPath {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (window : Fin 22) (h : TraceReach kernel Assumptions.all l g s events u) :
    events.countP (biasReturnMark window) + biasBodyDebt window u ≤
      events.countP (biasAcquireMark window) + biasBodyDebt window s := by
  induction h with
  | refl => simp
  | tau ht _ ih =>
    have hOne := biasReadOrderStep window (.inl ⟨rfl, ht⟩)
    simpa using ih.trans (Nat.add_le_add_left (by simpa using hOne) _)
  | @event s t u events e he _ ih =>
    have hOne := biasReadOrderStep window (.inr ⟨e, rfl, he⟩)
    simp only [Option.toList_some, List.countP_cons, List.countP_nil] at hOne ⊢
    omega

private theorem windowDebtMatched {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    (windows : Finset (Fin 22)) {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hLive : ∃ i ∈ windows, insideBiasBody i e.pc) :
    let before := (X.tr g).take j
    (∑ i ∈ windows, before.countP (biasReturnMark i)) + 1 ≤
      ∑ i ∈ windows, before.countP (biasAcquireMark i) := by
  obtain ⟨i,hI,hi⟩ := hLive
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t,_,hPath,hStep⟩ := hr.before_event he
  let before := (X.tr g).take j
  change TraceReach kernel Assumptions.all l g {} before t at hPath
  have hBound (b : Fin 22) (_hb : b ∈ windows) :
      before.countP (biasReturnMark b) + biasBodyDebt b t ≤
      before.countP (biasAcquireMark b) := by
    have hZ : biasBodyDebt b ({} : TState) = 0 := by fin_cases b <;> rfl
    have hB := biasReadOrderPath b hPath
    rw [hZ, Nat.add_zero] at hB
    exact hB
  have hDebt : biasBodyDebt i t = 1 := by
    have ht : insideBiasBody i t.pc := estep_source_pc hStep ▸ hi
    have hTick : t.pc ≠ (biasWindowWait i).pc+1 := by
      have := ht.1
      omega
    simp [biasBodyDebt, hTick, ht]
  have hTotal := Finset.sum_le_sum hBound
  rw [Finset.sum_add_distrib] at hTotal
  have hOne : 1 ≤ ∑ b ∈ windows, biasBodyDebt b t := by
    rw [← hDebt]
    exact Finset.single_le_sum (f := fun b => biasBodyDebt b t) (fun _ _ => Nat.zero_le _) hI
  exact (Nat.add_le_add_left hOne _).trans hTotal

private theorem windowCreditsMatched {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (_hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (windows : Finset (Fin 22)) {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hMark : ∃ i ∈ windows, biasReturnMark i e = true) :
    let before := (X.tr g).take j
    (∑ i ∈ windows, before.countP (biasReturnMark i)) + 1 ≤
      ∑ i ∈ windows, before.countP (biasAcquireMark i) := by
  obtain ⟨i,hi,hMark⟩ := hMark
  have hePc : e.pc = biasWindowEnd i := beq_iff_eq.mp hMark
  have hBody (i : Fin 22) : insideBiasBody i (biasWindowEnd i) := by
    fin_cases i <;> decide
  exact windowDebtMatched hX windows he ⟨i,hi,hePc.symm ▸ hBody i⟩

/-- A Bias return of any actual prefix has a corresponding successful Bias-ready wait. -/
theorem actualBiasReadBudget {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hMark : e.pc ∈ [3590, 5278]) :
    let before := (X.tr g).take j
    (before.countP fun e => e.pc == 3590) + (before.countP fun e => e.pc == 5278) + 1 ≤
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 3498
        | _ => false) +
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 5181
        | _ => false) := by
  have h : e.pc = 3590 ∨ e.pc = 5278 := by simpa using hMark
  have hActive : ∃ i ∈ ({0,1} : Finset (Fin 22)), biasReturnMark i e = true := by
    rcases h with h | h
    · exact ⟨0, by simp, beq_iff_eq.mpr h⟩
    · exact ⟨1, by simp, beq_iff_eq.mpr h⟩
  have hBudget := windowCreditsMatched hp hX {0,1} he hActive
  simp [Finset.sum_insert] at hBudget
  exact hBudget

/-- Before any actual Bias vector read, the lane has passed one more successful
Bias-ready wait than its completed stage rendezvous count. -/
theorem biasReadRendezvousBudget {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (repeated : Bool) (v : Fin 16) {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g,j) = some ⟨biasReadPc repeated v,.rd a bytes⟩) :
    let before := (X.tr g).take j
    (before.countP fun e => e.pc == 3583) + (before.countP fun e => e.pc == 5271) + 1 ≤
      before.countP readSuccess := by
  have hActive : ∃ i ∈ ({20,21} : Finset (Fin 22)), insideBiasBody i (biasReadPc repeated v) := by
    cases repeated
    · refine ⟨20,by simp,?_⟩
      fin_cases v <;> decide
    · refine ⟨21,by simp,?_⟩
      fin_cases v <;> decide
  have hBudget := windowDebtMatched hX {20,21} he hActive
  have hMarks (e : Event) :
      readSuccess e = (biasAcquireMark 20 e || biasAcquireMark 21 e) := by
    obtain ⟨pc,kind⟩ := e
    cases kind <;> try rfl
    case wait _ _ ok _ _ => cases ok <;> rfl
  have hDistinct (e : Event) : ¬ (biasAcquireMark 20 e = true ∧ biasAcquireMark 21 e = true) := by
    obtain ⟨pc,kind⟩ := e
    cases kind
    case wait target parity ok acq scope =>
      cases ok
      · simp [biasAcquireMark]
      · change ¬ ((pc == 3498) = true ∧ (pc == 5181) = true)
        simp only [beq_iff_eq]
        omega
    all_goals simp [biasAcquireMark]
  have hCounts (events : List Event) : events.countP readSuccess =
      events.countP (biasAcquireMark 20) + events.countP (biasAcquireMark 21) := by
    induction events with
    | nil => rfl
    | cons e events ih =>
      rw [List.countP_cons,hMarks,ih,List.countP_cons,List.countP_cons]
      cases a : biasAcquireMark 20 e <;> cases b : biasAcquireMark 21 e <;>
        simp_all <;> omega
  change _ ≤ ((X.tr g).take j).countP readSuccess
  rw [hCounts]
  have hNot : (20 : Fin 22) ∉ ({21} : Finset (Fin 22)) := by decide
  dsimp only at hBudget
  rw [Finset.sum_insert hNot,Finset.sum_insert hNot,
    Finset.sum_singleton,Finset.sum_singleton] at hBudget
  exact hBudget

/-- Any recorded Bias rendezvous has a preceding successful Bias-ready wait. -/
theorem biasRendezvousHasReadySuccess {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {event : Event} (he : X.get (g,j) = some event)
    (hSite : event.pc = 3583 ∨ event.pc = 5271) :
    0 < ((X.tr g).take j).countP readSuccess := by
  let past := (X.tr g).take j
  have oneWindow (window : Fin 22) (hBody : insideBiasBody window event.pc)
      (hImplies : ∀ e, biasAcquireMark window e = true → readSuccess e = true) :
      0 < past.countP readSuccess := by
    have hBudget := windowDebtMatched hX {window} he ⟨window,Finset.mem_singleton_self _,hBody⟩
    simp only [Finset.sum_singleton] at hBudget
    change past.countP (biasReturnMark window) + 1 ≤ past.countP (biasAcquireMark window) at hBudget
    have hBound : past.countP (biasAcquireMark window) ≤ past.countP readSuccess :=
      List.countP_mono_left (fun e _ hm => hImplies e hm)
    omega
  rcases hSite with h | h
  · apply oneWindow 20 (h.symm ▸ (by decide : insideBiasBody 20 3583))
    intro e hMark
    obtain ⟨pc,kind⟩ := e
    cases kind <;> simp [biasAcquireMark] at hMark
    rename_i loc parity ok acq scope
    cases ok <;> simp [biasWindowWait] at hMark
    simp [readSuccess,hMark]
  · apply oneWindow 21 (h.symm ▸ (by decide : insideBiasBody 21 5271))
    intro e hMark
    obtain ⟨pc,kind⟩ := e
    cases kind <;> simp [biasAcquireMark] at hMark
    rename_i loc parity ok acq scope
    cases ok <;> simp [biasWindowWait] at hMark
    simp [readSuccess,hMark]

private def biasRendezvousSite (repeated : Bool) : Nat := if repeated then 5271 else 3583

private def biasCorridorStart (repeated returnEdge : Bool) : Nat :=
  if returnEdge then biasRendezvousSite repeated else biasRendezvousSite repeated - 2

private def biasCorridorEnd (repeated returnEdge : Bool) : Nat :=
  if returnEdge then biasRendezvousSite repeated + 7 else biasRendezvousSite repeated

private def biasCorridor (repeated returnEdge : Bool) (pc : Nat) : Prop :=
  biasCorridorStart repeated returnEdge < pc ∧ pc ≤ biasCorridorEnd repeated returnEdge

private instance (repeated returnEdge : Bool) (pc : Nat) :
    Decidable (biasCorridor repeated returnEdge pc) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem corridorOpenCode (repeated returnEdge : Bool) :
    ∃ ins, kernel.code[biasCorridorStart repeated returnEdge]? = some ins ∧
      ins.op.isLocal = false ∧ ins.guard = none := by
  cases repeated <;> cases returnEdge
  · exact ⟨_,Flow.code_3581,rfl,rfl⟩
  · exact ⟨_,Flow.code_3583,rfl,rfl⟩
  · exact ⟨_,Flow.code_5269,rfl,rfl⟩
  · exact ⟨_,Flow.code_5271,rfl,rfl⟩

private def branchAroundCorridor (repeated returnEdge : Bool) (ins : Instr) : Bool :=
  match ins.op with
  | .bra dst _ => !decide (biasCorridor repeated returnEdge dst)
  | .brx .. => false
  | _ => true

private theorem branchAroundCorridorAll (repeated returnEdge : Bool) :
    kernel.code.all (branchAroundCorridor repeated returnEdge) = true := by
  cases repeated <;> cases returnEdge <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem segmentAroundCorridor (repeated returnEdge : Bool) {site : Nat}
    {seg : SegMatch CuteSlot} (hSite : site ∈ Assumptions.swExp2Sites)
    (hSeg : cuteExp2.matchAt kernel site = some seg) :
    ¬ biasCorridor repeated returnEdge seg.stop := by
  have hAudit : Assumptions.swExp2Sites.all (fun start =>
      match cuteExp2.matchAt kernel start with
      | some t => !decide (biasCorridor repeated returnEdge t.stop)
      | none => false) = true := by
    cases repeated <;> cases returnEdge <;> set_option maxRecDepth 100000 in kernel_rfl
  simpa [hSeg] using List.all_eq_true.mp hAudit site hSite

private theorem corridorEntryTau {l : Launch} {g : Nat} {s u : TState}
    (repeated returnEdge : Bool) (ht : Tau kernel Assumptions.all l g s u)
    (hu : biasCorridor repeated returnEdge u.pc) : biasCorridor repeated returnEdge s.pc := by
  obtain ⟨ins,hCode,_,hExec⟩ := tauScoreSource ht
  have hNext : u.pc = s.pc+1 := by
    rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hLocal⟩
    · rfl
    rcases scoreExecLocal hLocal with hFrame | ⟨seg,hSite,hMatch,hRun⟩
    · have hd := List.all_eq_true.mp (branchAroundCorridorAll repeated returnEdge) ins
        (List.mem_of_getElem? hCode)
      have hp := hFrame.pc
      cases ho : ins.op <;> simp only [ho,nextPc,BrxTarget,or_false] at hp
      case bra dst uni =>
        rw [hp] at hu
        simp [branchAroundCorridor,ho,hu] at hd
      case brx => simp [branchAroundCorridor,ho] at hd
      all_goals exact hp
    · exact (segmentAroundCorridor repeated returnEdge hSite hMatch
        ((scoreSegmentFrame hRun).1 ▸ hu)).elim
  have hNe : s.pc ≠ biasCorridorStart repeated returnEdge := by
    intro hPc
    obtain ⟨head,hHead,hLocal,hGuard⟩ := corridorOpenCode repeated returnEdge
    rw [hPc,hHead] at hCode
    obtain rfl := Option.some.inj hCode
    rcases hExec with ⟨_,hOff⟩ | ⟨_,hOp,_⟩
    · rw [hGuard] at hOff
      cases hOff
    · rw [hLocal] at hOp
      cases hOp
  unfold biasCorridor at hu ⊢
  omega

private theorem corridorLocal {pc : Nat} {ins : Instr} (repeated returnEdge : Bool)
    (hPc : biasCorridor repeated returnEdge pc)
    (hEnd : pc ≠ biasCorridorEnd repeated returnEdge) (hCode : kernel.code[pc]? = some ins) :
    ins.op.isLocal = true := by
  let lo := biasCorridorStart repeated returnEdge + 1
  let hi := biasCorridorEnd repeated returnEdge
  have hAudit : ((kernel.code.drop lo).take (hi-lo)).all (fun i => i.op.isLocal) = true := by
    cases repeated <;> cases returnEdge <;> kernel_rfl
  apply List.all_eq_true.mp hAudit ins
  apply List.mem_of_getElem? (i := pc-lo)
  unfold biasCorridor at hPc
  have hLo : lo ≤ pc := by dsimp only [lo]; omega
  have hHi : pc < hi := by dsimp only [hi]; omega
  rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]

private theorem corridorEndAdvances {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (repeated returnEdge : Bool) (hSite : s.pc = biasCorridorEnd repeated returnEdge)
    (he : EStep kernel Assumptions.all l g s e (some u)) : u.pc = s.pc+1 := by
  cases repeated <;> cases returnEdge
  · exact releaseAdvances 20 hSite he
  · exact releaseAdvances 0 hSite he
  · exact releaseAdvances 21 hSite he
  · exact releaseAdvances 1 hSite he

private theorem corridorEntryEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (repeated returnEdge : Bool) (he : EStep kernel Assumptions.all l g s e (some u))
    (hu : biasCorridor repeated returnEdge u.pc) :
    e.pc = biasCorridorStart repeated returnEdge := by
  obtain ⟨ins,hCode,hLocal,hFire⟩ := estep_event_source he
  by_cases hs : biasCorridor repeated returnEdge s.pc
  · by_cases hEnd : s.pc = biasCorridorEnd repeated returnEdge
    · have hNext := corridorEndAdvances repeated returnEdge hEnd he
      unfold biasCorridor at hu
      omega
    · rw [corridorLocal repeated returnEdge hs hEnd hCode] at hLocal
      cases hLocal
  have audit : kernel.code.all (fun i => i.op.isLocal || Epilogue.ordinaryEvent i.op) = true :=
    by decide +kernel
  have hOp := List.all_eq_true.mp audit ins (List.mem_of_getElem? hCode)
  have hFrame := Epilogue.ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g) (s := s)
    (by simpa only [hLocal,Bool.false_or] using hOp)
  have hPc := estep_source_pc he
  rcases callbackFrame_fires hFrame hFire with hSame | hNext
  · exact (hs (hSame ▸ hu)).elim
  · unfold biasCorridor at hs hu
    omega

private theorem biasCorridorLastEvent {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    (repeated returnEdge : Bool) (hReach : TraceReach kernel Assumptions.all l g s es u)
    {prior : List Event}
    (hStart : biasCorridor repeated returnEdge s.pc →
      ∃ xs e, prior = xs ++ [e] ∧ e.pc = biasCorridorStart repeated returnEdge)
    (hEnd : biasCorridor repeated returnEdge u.pc) :
    ∃ xs e, prior ++ es = xs ++ [e] ∧ e.pc = biasCorridorStart repeated returnEdge := by
  induction hReach generalizing prior with
  | refl => simpa using hStart hEnd
  | tau ht _ ih => exact ih (fun h => hStart (corridorEntryTau repeated returnEdge ht h)) hEnd
  | @event s t u es e ht _ ih =>
    rw [← List.singleton_append,← List.append_assoc]
    exact ih (fun h => ⟨prior,e,rfl,corridorEntryEvent repeated returnEdge ht h⟩) hEnd

variable {l : Launch} {m : Mem0} {X : Execution}

/-- A Bias rendezvous immediately follows its proxy fence. An elected return
credit immediately follows that same rendezvous in the credit issuer's trace. -/
theorem biasCorridorPrecedingEvent (hX : Consistent l kernel Assumptions.all m X)
    (repeated returnEdge : Bool) {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hSite : e.pc = (if repeated then 5271 else 3583) + (if returnEdge then 7 else 0)) :
    ∃ k prior, k+1 = j ∧ X.get (g,k) = some prior ∧
      prior.pc = (if repeated then 5271 else 3583) - (if returnEdge then 0 else 2) := by
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨s,_,hReach,hStep⟩ := hRun.before_event he
  have hS : s.pc = biasCorridorEnd repeated returnEdge := by
    rw [← estep_source_pc hStep,hSite]
    cases repeated <;> cases returnEdge <;> rfl
  have hEnd : biasCorridor repeated returnEdge s.pc := by
    rw [hS]
    cases repeated <;> cases returnEdge <;> decide
  obtain ⟨xs,prior,hSplit,hPrior⟩ := biasCorridorLastEvent repeated returnEdge hReach
    (prior := []) (fun h => by cases repeated <;> cases returnEdge <;> cases h.1) hEnd
  simp only [List.nil_append] at hSplit
  have hLen := congrArg List.length hSplit
  simp only [List.length_take,List.length_append,List.length_singleton,
    Nat.min_eq_left (len_of_get he).le] at hLen
  refine ⟨xs.length,prior,hLen.symm,?_,?_⟩
  · change (X.tr g)[xs.length]? = _
    rw [← List.getElem?_take_of_lt (show xs.length < j by omega),hSplit,
      List.getElem?_append_right le_rfl,Nat.sub_self]
    rfl
  · exact hPrior.trans (by cases repeated <;> cases returnEdge <;> rfl)

private def biasLoadStart (repeated : Bool) : Nat := biasReadPc repeated 0

private def biasReadWindowCode (ins : Instr) : Bool :=
  match ins.op with
  | .bra .. | .brx .. => false
  | op => op.isLocal || Epilogue.ordinaryEvent op

private theorem biasReadWindowCodeAt {pc : Nat} {ins : Instr} (repeated : Bool)
    (hLo : biasLoadStart repeated ≤ pc) (hHi : pc ≤ biasRendezvousSite repeated)
    (hc : kernel.code[pc]? = some ins) : biasReadWindowCode ins = true := by
  let lo := biasLoadStart repeated
  let hi := biasRendezvousSite repeated
  have hAudit : ((kernel.code.drop lo).take (hi+1-lo)).all biasReadWindowCode = true := by
    cases repeated <;> kernel_rfl
  apply List.all_eq_true.mp hAudit ins
  apply List.mem_of_getElem? (i := pc-lo)
  change lo ≤ pc at hLo
  change pc ≤ hi at hHi
  rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]

private theorem biasReadWindowTau {l : Launch} {g : Nat} {s u : TState}
    (repeated : Bool) (hLo : biasLoadStart repeated ≤ s.pc)
    (hHi : s.pc ≤ biasRendezvousSite repeated)
    (ht : Tau kernel Assumptions.all l g s u) :
    biasLoadStart repeated ≤ u.pc ∧ u.pc ≤ biasRendezvousSite repeated := by
  obtain ⟨ins,hc,_,hExec⟩ := tauScoreSource ht
  have hStrict : s.pc < biasRendezvousSite repeated := by
    by_contra! hAt
    have hPc : s.pc = biasCorridorStart repeated true := by
      change s.pc = biasRendezvousSite repeated
      omega
    obtain ⟨opening,hOpen,hLocal,hGuard⟩ := corridorOpenCode repeated true
    rw [hPc,hOpen] at hc
    obtain rfl := Option.some.inj hc
    rcases hExec with ⟨_,hSkip⟩ | ⟨_,hOp,_⟩
    · rw [hGuard] at hSkip
      cases hSkip
    · rw [hLocal] at hOp
      cases hOp
  rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hLocal⟩
  · change _ ≤ s.pc+1 ∧ s.pc+1 ≤ _
    omega
  rcases scoreExecLocal hLocal with hFrame | ⟨seg,hSite,hMatch,hRun⟩
  · have hCode := biasReadWindowCodeAt repeated hLo hHi hc
    have hNext := hFrame.pc
    cases ho : ins.op <;> simp only [ho,nextPc,BrxTarget,or_false] at hNext
    case bra | brx => simp [biasReadWindowCode,ho] at hCode
    all_goals omega
  · have audit : Assumptions.swExp2Sites.all (fun pc =>
        !decide (biasLoadStart repeated ≤ pc ∧ pc ≤ biasRendezvousSite repeated)) = true := by
      cases repeated <;> set_option maxRecDepth 100000 in kernel_rfl
    have h := List.all_eq_true.mp audit _ hSite
    simp [hLo,hHi] at h

private theorem biasReadWindowEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (repeated : Bool) (hLo : biasLoadStart repeated ≤ s.pc)
    (hHi : s.pc < biasRendezvousSite repeated)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    biasLoadStart repeated ≤ u.pc ∧ u.pc ≤ biasRendezvousSite repeated := by
  obtain ⟨ins,hc,hLocal,hFire⟩ := estep_event_source he
  have hCode := biasReadWindowCodeAt repeated hLo hHi.le hc
  have hOrd : Epilogue.ordinaryEvent ins.op = true := by
    cases ho : ins.op <;> simp_all [biasReadWindowCode]
  have hFrame := Epilogue.ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g) (s := s) hOrd
  rcases callbackFrame_fires hFrame hFire with hSame | hNext <;> omega

private theorem biasReadWindowTrace {l : Launch} {g : Nat} {s u : TState}
    {events : List Event} (repeated : Bool)
    (hr : TraceReach kernel Assumptions.all l g s events u)
    (hLo : biasLoadStart repeated ≤ s.pc) (hHi : s.pc ≤ biasRendezvousSite repeated) :
    (∃ prior e after, events = prior ++ e :: after ∧ e.pc = biasRendezvousSite repeated ∧
      ∀ earlier ∈ prior, biasLoadStart repeated ≤ earlier.pc ∧
        earlier.pc < biasRendezvousSite repeated) ∨
    (biasLoadStart repeated ≤ u.pc ∧ u.pc ≤ biasRendezvousSite repeated) := by
  induction hr with
  | refl => exact .inr ⟨hLo,hHi⟩
  | tau ht _ ih =>
    obtain ⟨hl,hh⟩ := biasReadWindowTau repeated hLo hHi ht
    exact ih hl hh
  | @event s t u es e he _ ih =>
    by_cases hEnd : s.pc = biasRendezvousSite repeated
    · exact .inl ⟨[],e,es,rfl,(estep_source_pc he).trans hEnd,by simp⟩
    have hStrict : s.pc < biasRendezvousSite repeated := by omega
    obtain ⟨hl,hh⟩ := biasReadWindowEvent repeated hLo hStrict he
    rcases ih hl hh with ⟨prior,bar,after,hEvents,hPc,hBefore⟩ | hBounds
    · refine .inl ⟨e::prior,bar,after,congrArg (e :: ·) hEvents,hPc,?_⟩
      intro before hb
      rcases List.mem_cons.mp hb with rfl | hm
      · rw [estep_source_pc he]
        exact ⟨hLo,hStrict⟩
      · exact hBefore _ hm
    · exact .inr hBounds

/-- A Bias read reaches its own rendezvous before leaving the straight-line
Bias load region, with no Bias rendezvous between the read and that arrival. -/
theorem biasReadRendezvousBefore (hX : Consistent l kernel Assumptions.all m X) (repeated : Bool)
    (v : Fin 16) {g read finish : Nat} {a : Acc} {bytes : List (Option Byte)} {later : Event}
    (he : X.get (g,read) = some ⟨biasReadPc repeated v,.rd a bytes⟩)
    (hLater : X.get (g,finish) = some later) (hAfter : read < finish)
    (hOutside : ¬ (biasReadPc repeated 0 ≤ later.pc ∧ later.pc ≤ (if repeated then 5271 else 3583)))
    :
    ∃ bar e, read < bar ∧ bar < finish ∧ X.get (g,bar) = some e ∧
      e.pc = (if repeated then 5271 else 3583) ∧
      ∀ j before, read ≤ j → j < bar → X.get (g,j) = some before →
        before.pc ≠ 3583 ∧ before.pc ≠ 5271 := by
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX he)
  have hLen : finish < (X.tr g).length := len_of_get hLater
  obtain ⟨s,u,hStep,hTail⟩ := hRun.after_event he (by omega)
  have hs : s.pc = biasReadPc repeated v := (estep_source_pc hStep).symm
  have hV := v.isLt
  have hRange : biasLoadStart repeated ≤ biasReadPc repeated v ∧
      biasReadPc repeated v < biasRendezvousSite repeated := by
    cases repeated <;> simp [biasLoadStart,biasReadPc,biasRendezvousSite] <;> omega
  obtain ⟨hl,hh⟩ := biasReadWindowEvent repeated (hs ▸ hRange.1) (hs ▸ hRange.2) hStep
  let stop := finish-(read+1)
  have hTarget : ((X.tr g).drop (read+1))[stop]? = some later := by
    rw [List.getElem?_drop,Nat.add_sub_of_le (show read+1 ≤ finish by omega)]
    exact hLater
  obtain ⟨t,_,hReach,hNext⟩ := hTail.before_event hTarget
  rcases biasReadWindowTrace repeated hReach hl hh with
    ⟨prior,e,after,hSplit,hSite,hBefore⟩ | hBounds
  · have hSize := congrArg List.length hSplit
    simp only [List.length_take,List.length_append,List.length_cons] at hSize
    let bar := read+1+prior.length
    have hBar : prior.length < stop := by omega
    have hReadDiff : biasReadPc repeated v ≠ 3583 ∧ biasReadPc repeated v ≠ 5271 := by
      cases repeated <;> simp [biasReadPc] <;> omega
    refine ⟨bar,e,by dsimp [bar]; omega,by dsimp [bar,stop] at *; omega,?_,hSite,?_⟩
    · change (X.tr g)[bar]? = _
      rw [show bar = read+1+prior.length by rfl, ← List.getElem?_drop,
        ← List.getElem?_take_of_lt hBar,hSplit,List.getElem?_append_right le_rfl,Nat.sub_self]
      rfl
    · intro j before hLow hHigh hGet
      by_cases hRead : j = read
      · subst j
        have h := Option.some.inj (hGet.symm.trans he)
        exact h ▸ hReadDiff
      let k := j-(read+1)
      have hk : k < prior.length := by dsimp [k,bar] at *; omega
      have hPoint : ((X.tr g).drop (read+1))[k]? = some before := by
        rw [List.getElem?_drop,Nat.add_sub_of_le (show read+1 ≤ j by omega)]
        exact hGet
      rw [← List.getElem?_take_of_lt (hk.trans hBar),hSplit,
        List.getElem?_append_left hk] at hPoint
      have hPC := hBefore _ (List.mem_of_getElem? hPoint)
      cases repeated <;> simp [biasLoadStart,biasReadPc,biasRendezvousSite] at hPC ⊢ <;> omega
  · exact (hOutside ((estep_source_pc hNext).symm ▸ hBounds)).elim

private def probabilityWindows (packet : Fin 2) : Finset (Fin 22) :=
  if packet = 0 then {2,4,6} else {3,5,7}

/-- A probability credit in any round has a corresponding successful score-ready wait. -/
theorem actualProbabilityScoreBudget {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (packet : Fin 2)
    {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hSite : if packet.val = 0 then e.pc ∈ [4847, 6532, 7437] else e.pc ∈ [4867, 6552, 7457]) :
    let before := (X.tr g).take j
    (before.countP fun e => e.pc == (if packet.val = 0 then 4847 else 4867)) +
      (before.countP fun e => e.pc == (if packet.val = 0 then 6532 else 6552)) +
      (before.countP fun e => e.pc == (if packet.val = 0 then 7437 else 7457)) + 1 ≤
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 3425
        | _ => false) +
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 5109
        | _ => false) +
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 6676
        | _ => false) := by
  have hActive : ∃ i ∈ probabilityWindows packet, biasReturnMark i e = true := by
    fin_cases packet
    · have h : e.pc = 4847 ∨ e.pc = 6532 ∨ e.pc = 7437 := by simpa using hSite
      rcases h with h | h | h
      · exact ⟨2, by simp [probabilityWindows], beq_iff_eq.mpr h⟩
      · exact ⟨4, by simp [probabilityWindows], beq_iff_eq.mpr h⟩
      · exact ⟨6, by simp [probabilityWindows], beq_iff_eq.mpr h⟩
    · have h : e.pc = 4867 ∨ e.pc = 6552 ∨ e.pc = 7457 := by simpa using hSite
      rcases h with h | h | h
      · exact ⟨3, by simp [probabilityWindows], beq_iff_eq.mpr h⟩
      · exact ⟨5, by simp [probabilityWindows], beq_iff_eq.mpr h⟩
      · exact ⟨7, by simp [probabilityWindows], beq_iff_eq.mpr h⟩
  have h := windowCreditsMatched hp hX (probabilityWindows packet) he hActive
  fin_cases packet <;>
    simp [probabilityWindows, Finset.sum_insert, Nat.add_assoc] at h ⊢ <;>
    exact h

private def probabilityStoreWindow (round : Round) (last : Bool) : Fin 22 :=
  match round with
  | .first => if last then 3 else 2
  | .biased => if last then 5 else 4
  | .unbiased => if last then 7 else 6

private theorem actualProbabilityWindowScoreBudget (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (round : Round) (last : Bool) {e : Event} (he : X.get (g,j) = some e)
    (hLive : insideBiasBody (probabilityStoreWindow round last) e.pc) :
    let packet := (if last then 1 else 0 : Fin 2)
    let before := (X.tr g).take j
    (before.countP fun e => e.pc == (if packet.val = 0 then 4847 else 4867)) +
      (before.countP fun e => e.pc == (if packet.val = 0 then 6532 else 6552)) +
      (before.countP fun e => e.pc == (if packet.val = 0 then 7437 else 7457)) + 1 ≤
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 3425
        | _ => false) +
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 5109
        | _ => false) +
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 6676
        | _ => false) := by
  let packet := (if last then 1 else 0 : Fin 2)
  let window := probabilityStoreWindow round last
  have hMember : window ∈ probabilityWindows packet := by
    cases round <;> cases last <;> decide
  have h := windowDebtMatched hX (probabilityWindows packet) he ⟨_,hMember,hLive⟩
  change (∑ i ∈ probabilityWindows packet, ((X.tr g).take j).countP (biasReturnMark i)) + 1 ≤
    ∑ i ∈ probabilityWindows packet, ((X.tr g).take j).countP (biasAcquireMark i) at h
  change _ + _ + _ + 1 ≤ _
  let before := (X.tr g).take j
  cases hLast : last
  · simp [packet, hLast, probabilityWindows, Finset.sum_insert, Nat.add_assoc] at h
    change before.countP (biasReturnMark 2) + before.countP (biasReturnMark 4) +
      before.countP (biasReturnMark 6) + 1 ≤ before.countP (biasAcquireMark 2) +
        before.countP (biasAcquireMark 4) + before.countP (biasAcquireMark 6)
    simpa only [Nat.add_assoc] using h

  · simp [packet, hLast, probabilityWindows, Finset.sum_insert, Nat.add_assoc] at h
    change before.countP (biasReturnMark 3) + before.countP (biasReturnMark 5) +
      before.countP (biasReturnMark 7) + 1 ≤ before.countP (biasAcquireMark 3) +
        before.countP (biasAcquireMark 5) + before.countP (biasAcquireMark 7)
    simpa only [Nat.add_assoc] using h

/-- An actual P store has a successful score wait beyond its prior packet publications. -/
theorem actualProbabilityStoreScoreBudget (hX : Consistent l kernel Assumptions.all m X)
    {g j addr : Nat} {vals : List Value} {shape : TcShape} (round : Round) (quarter : Fin 4)
    (he : X.get (g,j) = some ⟨probabilityPc round quarter,.tc (.st addr vals shape)⟩) :
    let packet := (if quarter = 3 then 1 else 0 : Fin 2)
    let before := (X.tr g).take j
    (before.countP fun e => e.pc == (if packet.val = 0 then 4847 else 4867)) +
      (before.countP fun e => e.pc == (if packet.val = 0 then 6532 else 6552)) +
      (before.countP fun e => e.pc == (if packet.val = 0 then 7437 else 7457)) + 1 ≤
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 3425
        | _ => false) +
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 5109
        | _ => false) +
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 6676
        | _ => false) := by
  have hBody : insideBiasBody (probabilityStoreWindow round (decide (quarter = 3)))
      (probabilityPc round quarter) := by
    cases round <;> fin_cases quarter <;> decide
  have h := actualProbabilityWindowScoreBudget hX round (decide (quarter = 3)) he hBody
  let before := (X.tr g).take j
  by_cases hQ : quarter = 3
  · simp only [hQ,ite_true,decide_true] at h ⊢
    change before.countP (biasReturnMark 3) + before.countP (biasReturnMark 5) +
      before.countP (biasReturnMark 7) + 1 ≤ before.countP (biasAcquireMark 3) +
        before.countP (biasAcquireMark 5) + before.countP (biasAcquireMark 7) at h ⊢
    exact h
  · simp only [hQ,ite_false,decide_false] at h ⊢
    change before.countP (biasReturnMark 2) + before.countP (biasReturnMark 4) +
      before.countP (biasReturnMark 6) + 1 ≤ before.countP (biasAcquireMark 2) +
        before.countP (biasAcquireMark 4) + before.countP (biasAcquireMark 6) at h ⊢
    exact h

/-- Each actual score load already has a successful wait for the relevant round. -/
theorem actualScoreLoadScoreBudget (hX : Consistent l kernel Assumptions.all m X) {g j addr : Nat}
    {vals : List Value} {shape : TcShape} (round : Round) (quarter : Fin 4)
    (he : X.get (g,j) = some ⟨scorePc round quarter,.tc (.ld addr vals shape)⟩) :
    let before := (X.tr g).take j
    (before.countP fun e => e.pc == 4847) +
      (before.countP fun e => e.pc == 6532) +
      (before.countP fun e => e.pc == 7437) + 1 ≤
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 3425
        | _ => false) +
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 5109
        | _ => false) +
      (before.countP fun e => match e.kind with
        | .wait _ _ true _ _ => e.pc == 6676
        | _ => false) := by
  apply actualProbabilityWindowScoreBudget hX round false he
  change insideBiasBody (probabilityStoreWindow round false) (scorePc round quarter)
  cases round <;> fin_cases quarter <;> decide

private def statsWindows : Finset (Fin 22) := {8,9,10}

/-- Count the three score-ready waits to which a nonterminal statistics publication can belong. -/
def scoreAcquireMark (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true _ _ => ([3425,5109,6676] : List Nat).contains e.pc
  | _ => false

/-- Count statistics publications driven by a new score fragment. -/
def scoredStatisticsMark (e : Event) : Bool :=
  ([4397,5683,6891] : List Nat).contains e.pc

private theorem sumDistinctMarks (xs : List Event) (a b c : Nat) (ha : a ≠ b) (hb : a ≠ c)
    (hc : b ≠ c) (selected : Event → Bool) :
    (xs.countP fun e => selected e && ([a,b,c] : List Nat).contains e.pc) =
      (xs.countP fun e => selected e && e.pc == a) +
      (xs.countP fun e => selected e && e.pc == b) +
      (xs.countP fun e => selected e && e.pc == c) := by
  let mark (p : Nat) (e : Event) : Bool := selected e && e.pc == p
  have hMark : (fun e => selected e && ([a,b,c] : List Nat).contains e.pc) =
      (fun e => mark a e || mark b e || mark c e) := by
    funext e
    apply Bool.eq_iff_iff.mpr
    simp only [mark, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto
  rw [hMark]
  have h₁ : ∀ e ∈ xs, ¬(mark a e = true ∧ mark b e = true) := by
    intro e _ h
    simp only [mark, Bool.and_eq_true, beq_iff_eq] at h
    exact ha (h.1.2.symm.trans h.2.2)
  have h₂ : ∀ e ∈ xs, ¬((mark a e || mark b e) = true ∧ mark c e = true) := by
    intro e _ h
    simp only [mark, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    exact h.1.elim (fun hA => hb (hA.2.symm.trans h.2.2))
      (fun hB => hc (hB.2.symm.trans h.2.2))
  rw [countP_or_disj h₂, countP_or_disj h₁]

private theorem statsMarkerSum (xs : List Event) :
    (∑ i ∈ statsWindows, xs.countP (biasReturnMark i)) = xs.countP scoredStatisticsMark := by
  have h := sumDistinctMarks xs 4397 5683 6891 (by decide) (by decide) (by decide) (fun _ => true)
  simp only [Bool.true_and] at h
  simp [statsWindows, Finset.sum_insert]
  rw [← Nat.add_assoc]
  exact h.symm

private def earlyWindow : Fin 3 → Fin 22
  | 0 => 2
  | 1 => 4
  | 2 => 6

private theorem insideWindowDebt {s : TState} {w : Fin 22}
    (h : insideBiasBody w s.pc) : biasBodyDebt w s = 1 := by
  have hGate : s.pc ≠ (biasWindowWait w).pc+1 := by have := h.1; omega
  simp [biasBodyDebt,hGate,h]

private def earlyWindowBranch (w : Fin 22) (pc : Nat) (op : Op) : Bool :=
  if insideBiasBody w pc then
    match op with
    | .bra dst _ => decide (insideBiasBody w dst)
    | .brx .. => false
    | _ => true
  else true

private theorem earlyWindowBranchAt (i : Fin 3) {site : Nat} {ins : Instr}
    (hc : kernel.code[site]? = some ins) :
    earlyWindowBranch (earlyWindow i) site ins.op = true := by
  have h : (kernel.code.zipIdx 0).all (fun (ins,pc) =>
      earlyWindowBranch (earlyWindow i) pc ins.op) = true := by
    fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp h (ins,site)
  apply List.mem_of_getElem? (i := site)
  simp only [List.getElem?_zipIdx,hc,Option.map_some,Nat.zero_add]

private theorem earlyWindowSegment (i : Fin 3) {site : Nat} {seg : SegMatch CuteSlot}
    (hSite : site ∈ Assumptions.swExp2Sites) (hc : cuteExp2.matchAt kernel site = some seg)
    (hInside : insideBiasBody (earlyWindow i) site) : insideBiasBody (earlyWindow i) seg.stop := by
  have h : Assumptions.swExp2Sites.all (fun site =>
      if insideBiasBody (earlyWindow i) site then
        match cuteExp2.matchAt kernel site with
        | some match' => decide (insideBiasBody (earlyWindow i) match'.stop)
        | none => false
      else true) = true := by
    fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  have hh := List.all_eq_true.mp h site hSite
  rw [ite_eq_left hInside,hc] at hh
  exact of_decide_eq_true hh

private theorem earlyUnconditionalRelease (i : Fin 3) :
    ∃ op, kernel.code[biasWindowEnd (earlyWindow i)]? = some ⟨none,op⟩ ∧ op.isLocal = false := by
  fin_cases i
  · exact ⟨_,Flow.code_4847,rfl⟩
  · exact ⟨_,Flow.code_6532,rfl⟩
  · exact ⟨_,Flow.code_7437,rfl⟩

private theorem earlyBodyStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (i : Fin 3) (hInside : insideBiasBody (earlyWindow i) s.pc)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    ev.toList.countP (biasReturnMark (earlyWindow i)) + biasBodyDebt (earlyWindow i) u ≥ 1 := by
  let w := earlyWindow i
  have advancing (hBefore : s.pc < biasWindowEnd w) (hNext : u.pc = s.pc + 1) :
      biasBodyDebt w u = 1 := by
    have hFrom : (biasWindowWait w).pc+3 ≤ s.pc := hInside.1
    exact insideWindowDebt ⟨by omega,by omega⟩
  rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
  · obtain ⟨ins,hc,_,hExec⟩ := tauScoreSource hTau
    have hBefore : s.pc < biasWindowEnd w := by
      rcases lt_or_eq_of_le hInside.2 with h | heq
      · exact h
      · obtain ⟨op,hCode,hLocal⟩ := earlyUnconditionalRelease i
        rw [heq,hCode] at hc
        obtain rfl := Option.some.inj hc
        rcases hExec with ⟨_,hSkip⟩ | ⟨_,hL,_⟩
        · cases hSkip
        · rw [hLocal] at hL
          cases hL
    have hKept : biasBodyDebt w u = 1 := by
      rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hExec⟩
      · exact advancing hBefore rfl
      · rcases scoreExecLocal hExec with hFrame | ⟨seg,hs,hm,hRun⟩
        · have hPc := hFrame.pc
          have hAudit := earlyWindowBranchAt i hc
          have hHere : insideBiasBody (earlyWindow i) s.pc := hInside
          cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
          case bra dst uni =>
            have hh : insideBiasBody (earlyWindow i) dst := by
              simpa only [earlyWindowBranch,hHere,ite_true,hOp,decide_eq_true_eq] using hAudit
            exact insideWindowDebt (hPc.symm ▸ hh)
          case brx =>
            have hBad : false = true := by
              simpa only [earlyWindowBranch,hHere,ite_true,hOp] using hAudit
            cases hBad
          all_goals exact advancing hBefore hPc
        · have hu := (scoreSegmentFrame hRun).1
          exact insideWindowDebt (hu.symm ▸ earlyWindowSegment i hs hm hInside)
    simp [w] at hKept
    simp [hKept]
  · by_cases hEnd : s.pc = biasWindowEnd w
    · have hMark : biasReturnMark (earlyWindow i) e = true := by
        simp [biasReturnMark,estep_source_pc hEvent,hEnd,w]
      simp [hMark]
    · have hBefore := lt_of_le_of_ne hInside.2 hEnd
      obtain ⟨ins,hc,hl,hFire⟩ := estep_event_source hEvent
      have hAll : kernel.code.all (fun ins => ins.op.isLocal || Epilogue.ordinaryEvent ins.op) =
          true := by decide +kernel
      have hOp := List.all_eq_true.mp hAll _ (List.mem_of_getElem? hc)
      have hF := Epilogue.ordinaryEventFrame (A := Assumptions.all) (l := l) (g := g) (s := s)
        (by simpa only [hl,Bool.false_or] using hOp)
      have hKept : biasBodyDebt (earlyWindow i) u = 1 := by
        rcases callbackFrame_fires hF hFire with h | h
        · exact insideWindowDebt (h.symm ▸ hInside)
        · exact advancing hBefore h
      simp [hKept]

private theorem earlyGateDebt {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (w : Fin 22) (hGate : s.pc = (biasWindowWait w).pc+1)
    (hReg : s.regs (biasWindowWait w).result = some (.pred true))
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    biasBodyDebt w u = 1 := by
  have hCode := (biasWindowCode w).2.1
  have hc := hGate.symm ▸ hCode
  rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
  · obtain ⟨ins,hc',_,hExec⟩ := tauScoreSource hTau
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    have hGuard : guardHolds s (some ((biasWindowWait w).result,false)) = .ok true := by
      simp [guardHolds,readReg,hReg,bind,Except.bind,pure,Except.pure]
    rcases hExec with ⟨_,hSkip⟩ | ⟨_,_,hExec⟩
    · rw [hGuard] at hSkip
      cases hSkip
    · have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hGate]; fin_cases w <;> decide
      rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl,
        execLocalA_nil] at hExec
      have hDst : u.pc = (biasWindowWait w).pc+3 := by
        have hEq : Except.ok {s with pc := (biasWindowWait w).pc+3} = Except.ok u := hExec
        exact congrArg TState.pc (Except.ok.inj hEq).symm
      have hInside : (biasWindowWait w).pc+3 ≤ biasWindowEnd w := by fin_cases w <;> decide
      exact insideWindowDebt ⟨le_of_eq hDst.symm,hDst ▸ hInside⟩
  · obtain ⟨ins,hc',hl,_⟩ := estep_event_source hEvent
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    cases hl

private theorem earlyWindowStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (i : Fin 3) (hStep : WStep kernel Assumptions.all l g s ev u) :
    let w := earlyWindow i
    ev.toList.countP (biasReturnMark w) + biasBodyDebt w u =
      ev.toList.countP (biasAcquireMark w) + biasBodyDebt w s := by
  let w := earlyWindow i
  dsimp only
  apply Nat.le_antisymm (biasReadOrderStep w hStep)
  have hBounds : (biasWindowWait w).pc+3 ≤ biasWindowEnd w := by
    fin_cases i <;> decide
  by_cases hWait : s.pc = (biasWindowWait w).pc
  · obtain ⟨addr,q,ok,scope,rfl,rfl⟩ := wstep_poll hStep (hWait.symm ▸ (biasWindowCode w).1)
    have hS : ¬ insideBiasBody w (biasWindowWait w).pc := by
      unfold insideBiasBody
      omega
    have hNe : (biasWindowWait w).pc ≠ biasWindowEnd w := by omega
    have hNext : (next (setReg s (biasWindowWait w).result (.pred ok))).pc =
        (biasWindowWait w).pc+1 := by simp [next,setReg,hWait]
    have hReg : (next (setReg s (biasWindowWait w).result (.pred ok))).regs
        (biasWindowWait w).result = some (.pred ok) := by simp [next,setReg]
    change (some ⟨s.pc,.wait addr q ok true scope⟩ : Option Event).toList.countP
      (biasAcquireMark w) + biasBodyDebt w s ≤
      (some ⟨s.pc,.wait addr q ok true scope⟩ : Option Event).toList.countP (biasReturnMark w) +
        biasBodyDebt w (next (setReg s (biasWindowWait w).result (.pred ok)))
    cases ok <;> simp [biasBodyDebt,biasAcquireMark,biasReturnMark,hWait,hNe,hS,hNext,hReg]
  have hNoAcquire : ev.toList.countP (biasAcquireMark w) = 0 := by
    rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
    · rfl
    · have hPc := estep_source_pc hEvent
      have hMark : biasAcquireMark w e = false := by
        cases hc : e.kind <;> simp [biasAcquireMark,hc,hPc]
        rename_i _ _ ok _ _
        cases ok <;> simp_all
      simp [hMark]
  change ev.toList.countP (biasAcquireMark w) + biasBodyDebt w s ≤
    ev.toList.countP (biasReturnMark w) + biasBodyDebt w u
  rw [hNoAcquire,Nat.zero_add]
  by_cases hGate : s.pc = (biasWindowWait w).pc+1
  · by_cases hR : s.regs (biasWindowWait w).result = some (.pred true)
    · have hDebt : biasBodyDebt w s = 1 := by simp [biasBodyDebt,hGate,hR]
      rw [hDebt,earlyGateDebt w hGate hR hStep]
      omega
    · simp [biasBodyDebt,hGate,hR]
  · by_cases hInside : insideBiasBody w s.pc
    · rw [insideWindowDebt hInside]
      exact earlyBodyStep i hInside hStep
    · simp [biasBodyDebt,hGate,hInside]

private theorem earlyWindowPath {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (i : Fin 3) (h : TraceReach kernel Assumptions.all l g s events u) :
    let w := earlyWindow i
    events.countP (biasReturnMark w) + biasBodyDebt w u =
      events.countP (biasAcquireMark w) + biasBodyDebt w s := by
  induction h with
  | refl => simp
  | tau ht _ ih =>
    have hOne := earlyWindowStep i (.inl ⟨rfl,ht⟩)
    simp only [Option.toList_none,List.countP_nil,Nat.zero_add] at hOne
    simpa only [hOne] using ih
  | @event s t u events e he _ ih =>
    have hOne := earlyWindowStep i (.inr ⟨e,rfl,he⟩)
    dsimp only at hOne ih ⊢
    simp only [Option.toList_some,List.countP_cons,List.countP_nil] at hOne ⊢
    omega

private theorem scoreMarkerSum (xs : List Event) :
    (∑ i ∈ statsWindows, xs.countP (biasAcquireMark i)) = xs.countP scoreAcquireMark := by
  let selected (e : Event) : Bool :=
    match e.kind with
    | .wait _ _ true _ _ => true
    | _ => false
  have h := sumDistinctMarks xs 3425 5109 6676 (by decide) (by decide) (by decide) selected
  have hScore (i : Fin 22) :
      (fun e => selected e && e.pc == (biasWindowWait i).pc) = biasAcquireMark i := by
    funext e
    obtain ⟨pc,kind⟩ := e
    cases kind <;> try rfl
    rename_i _ _ ok _ _
    cases ok <;> rfl
  have hMain :
      (fun e => selected e && ([3425,5109,6676] : List Nat).contains e.pc) = scoreAcquireMark := by
    funext e
    obtain ⟨pc,kind⟩ := e
    cases kind <;> try rfl
    rename_i _ _ ok _ _
    cases ok <;> rfl
  rw [hMain] at h
  change (xs.countP scoreAcquireMark) =
    (xs.countP fun e => selected e && e.pc == (biasWindowWait 8).pc) +
    (xs.countP fun e => selected e && e.pc == (biasWindowWait 9).pc) +
    (xs.countP fun e => selected e && e.pc == (biasWindowWait 10).pc) at h
  rw [hScore, hScore, hScore] at h
  simp [statsWindows, Finset.sum_insert]
  rw [← Nat.add_assoc]
  exact h.symm

/-- Physical publication of the early probability packet on a softmax lane. -/
def earlyProbabilityMark (e : Event) : Bool :=
  ([4847,6532,7437] : List Nat).contains e.pc

/-- An actual prefix balances the score acquires, early probability publications,
and one pending publication for each acquired round still in progress. -/
private theorem scoreEarlyLedgerOfPrefix {l : Launch} {g : Nat} {t : TState}
    {before : List Event} (hPath : TraceReach kernel Assumptions.all l g {} before t) :
    before.countP scoreAcquireMark = before.countP earlyProbabilityMark+
      (biasBodyDebt 2 t+biasBodyDebt 4 t+biasBodyDebt 6 t) := by
  have h0 := earlyWindowPath 0 hPath
  have h1 := earlyWindowPath 1 hPath
  have h2 := earlyWindowPath 2 hPath
  change before.countP (biasReturnMark 2) + biasBodyDebt 2 t =
    before.countP (biasAcquireMark 2) + 0 at h0
  change before.countP (biasReturnMark 4) + biasBodyDebt 4 t =
    before.countP (biasAcquireMark 4) + 0 at h1
  change before.countP (biasReturnMark 6) + biasBodyDebt 6 t =
    before.countP (biasAcquireMark 6) + 0 at h2
  have hScore : before.countP scoreAcquireMark =
      before.countP (biasAcquireMark 2) + before.countP (biasAcquireMark 4) +
        before.countP (biasAcquireMark 6) := by
    change before.countP scoreAcquireMark =
      before.countP (biasAcquireMark 8) + before.countP (biasAcquireMark 9) +
        before.countP (biasAcquireMark 10)
    have h := (scoreMarkerSum before).symm
    simp [statsWindows,Finset.sum_insert] at h
    omega
  have hEarly : before.countP earlyProbabilityMark =
      before.countP (biasReturnMark 2) + before.countP (biasReturnMark 4) +
        before.countP (biasReturnMark 6) := by
    change (before.countP fun e => ([4847,6532,7437] : List Nat).contains e.pc) =
      (before.countP fun e => e.pc == 4847) + (before.countP fun e => e.pc == 6532) +
        (before.countP fun e => e.pc == 7437)
    simpa only [Bool.true_and] using
      sumDistinctMarks before 4847 6532 7437 (by decide) (by decide) (by decide) (fun _ => true)
  change before.countP scoreAcquireMark = before.countP earlyProbabilityMark+
    (biasBodyDebt 2 t+biasBodyDebt 4 t+biasBodyDebt 6 t)
  rw [hScore,hEarly]
  omega

/-- A quiescent opening checkpoint or loop head has no in-flight score publication. -/
theorem scoreEarlyLedgerAtHead {l : Launch} {g : Nat} {t : TState}
    {before : List Event} (hPath : TraceReach kernel Assumptions.all l g {} before t)
    (hHead : t.pc = 5006 ∨ t.pc = 5032 ∨ t.pc = 6661 ∨ t.pc = 7605) :
    before.countP scoreAcquireMark = before.countP earlyProbabilityMark := by
  have hClear : biasBodyDebt 2 t+biasBodyDebt 4 t+biasBodyDebt 6 t = 0 := by
    rcases hHead with hPc | hPc | hPc | hPc <;>
      simp [biasBodyDebt,insideBiasBody,biasWindowWait,biasWindowEnd,hPc]
  simpa only [hClear,Nat.add_zero] using scoreEarlyLedgerOfPrefix hPath

/-- An actual biased coefficient store is inside its acquired score round and
precedes the early probability credit. -/
theorem scoreEarlyLedgerAtBiasedCoefficient (hX : Consistent l kernel Assumptions.all m X)
    {g pos : Nat} {a : Acc} {data : List Byte} (he : X.get (g,pos) = some ⟨5682,.wr a data⟩) :
    ((X.tr g).take pos).countP scoreAcquireMark =
      ((X.tr g).take pos).countP earlyProbabilityMark+1 := by
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t,_,hPath,hStep⟩ := hr.before_event he
  have hPc : t.pc = 5682 := (estep_source_pc hStep).symm
  have hDebt : biasBodyDebt 2 t+biasBodyDebt 4 t+biasBodyDebt 6 t = 1 := by
    simp [biasBodyDebt,insideBiasBody,biasWindowWait,biasWindowEnd,hPc]
  exact (scoreEarlyLedgerOfPrefix hPath).trans (congrArg (_ + ·) hDebt)

/-- The biased region's actual fallthrough follows its probability credit. -/
theorem scoreEarlyLedgerAtBiasedFallthrough {l : Launch} {g : Nat} {t : TState}
    {before : List Event} (hPath : TraceReach kernel Assumptions.all l g {} before t)
    (hPc : t.pc = 6654) :
    before.countP scoreAcquireMark = before.countP earlyProbabilityMark := by
  have hDebt : biasBodyDebt 2 t+biasBodyDebt 4 t+biasBodyDebt 6 t = 0 := by
    simp [biasBodyDebt,insideBiasBody,biasWindowWait,biasWindowEnd,hPc]
  simpa only [hDebt,Nat.add_zero] using scoreEarlyLedgerOfPrefix hPath

/-- At every score load, precisely one successful score-ready wait is outstanding.
All earlier waits on the lane have published their early probability packet. -/
theorem actualScoreLoadEarlyLedger (hX : Consistent l kernel Assumptions.all m X) {g j addr : Nat}
    {vals : List Value} {shape : TcShape} (round : Round) (quarter : Fin 4)
    (he : X.get (g,j) = some ⟨scorePc round quarter,.tc (.ld addr vals shape)⟩) :
    let before := (X.tr g).take j
    before.countP scoreAcquireMark = before.countP earlyProbabilityMark+1 := by
  dsimp only
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t,_,hPath,hStep⟩ := hr.before_event he
  let before := (X.tr g).take j
  change TraceReach kernel Assumptions.all l g {} before t at hPath
  have hPc : t.pc = scorePc round quarter := (estep_source_pc hStep).symm
  have hOne : biasBodyDebt 2 t + biasBodyDebt 4 t + biasBodyDebt 6 t = 1 := by
    cases round <;> fin_cases quarter <;>
      simp [biasBodyDebt,insideBiasBody,biasWindowWait,biasWindowEnd,scorePc,hPc]
  rw [scoreEarlyLedgerOfPrefix hPath,hOne]

/-- Every probability store that precedes a score load on its own lane belongs to a
strictly earlier score acquire. The intervening success is counted on the actual trace. -/
theorem scoreLoadAfterStoreHasNewWait (hX : Consistent l kernel Assumptions.all m X)
    (round previous : Round) (quarter storeQuarter : Fin 4) {g store load addr stAddr : Nat}
    {vals stVals : List Value} {shape stShape : TcShape}
    (hStore : X.get (g,store) = some
      ⟨probabilityPc previous storeQuarter,.tc (.st stAddr stVals stShape)⟩)
    (hLoad : X.get (g,load) = some ⟨scorePc round quarter,.tc (.ld addr vals shape)⟩)
    (hBefore : store < load) :
    ((X.tr g).take store).countP scoreAcquireMark <
      ((X.tr g).take load).countP scoreAcquireMark := by
  let w : Fin 22 := match round with | .first => 8 | .biased => 9 | .unbiased => 10
  let event : Event := ⟨probabilityPc previous storeQuarter,.tc (.st stAddr stVals stShape)⟩
  let trail := (X.tr g).drop (store+1)
  let middle := trail.take (load-(store+1))
  have hL : load < (X.tr g).length := len_of_get hLoad
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX hStore)
  obtain ⟨s,u,hStoreStep,hTail⟩ := hRun.after_event hStore (by omega)
  have he : trail[load-(store+1)]? = some ⟨scorePc round quarter,.tc (.ld addr vals shape)⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le (by omega : store+1 ≤ load)]
    exact hLoad
  obtain ⟨t,_,hMiddle,hLoadStep⟩ := hTail.before_event he
  have hWalk : TraceReach kernel Assumptions.all l g s (event::middle) t :=
    .event hStoreStep hMiddle
  have hs : s.pc = probabilityPc previous storeQuarter := (estep_source_pc hStoreStep).symm
  have ht : t.pc = scorePc round quarter := (estep_source_pc hLoadStep).symm
  have hS : biasBodyDebt w s = 0 := by
    cases round <;> cases previous <;> fin_cases storeQuarter <;>
      simp [biasBodyDebt,insideBiasBody,biasWindowWait,biasWindowEnd,probabilityPc,w,hs]
  have hT : biasBodyDebt w t = 1 := by
    cases round <;> fin_cases quarter <;>
      simp [biasBodyDebt,insideBiasBody,biasWindowWait,biasWindowEnd,scorePc,w,ht]
  have hBudget := biasReadOrderPath w hWalk
  rw [hS,hT] at hBudget
  have hMore : 1 ≤ middle.countP (biasAcquireMark w) := by
    have hUnmarked : biasAcquireMark w event = false := rfl
    simp only [List.countP_cons,hUnmarked,Bool.false_eq_true,ite_false] at hBudget
    omega
  have hCoverage (e : Event) : biasAcquireMark w e = true → scoreAcquireMark e = true := by
    obtain ⟨site,kind⟩ := e
    cases kind <;> try solve | intro h; cases h
    case wait loc phase ok acq scope =>
      cases ok
      · intro h
        cases h
      · cases round <;> simp [biasAcquireMark,scoreAcquireMark,w,biasWindowWait] <;> tauto
  have hCount := List.countP_mono_left (l := middle) (fun e _ => hCoverage e)
  rw [show load = store+1+(load-(store+1)) by omega,List.take_add,List.countP_append]
  apply lt_of_lt_of_le (Nat.lt_succ_self _)
  have hUnmarked : scoreAcquireMark event = false := rfl
  have hSame := countP_take_succ_false (p := scoreAcquireMark) hStore hUnmarked
  dsimp only [middle,trail] at hCount hMore
  omega

/-- The local publication of an early quarter is its credit. The local publication
of the last quarter is the warp rendezvous before the elected credit. -/
def probabilityPublicationEnd (round : Round) (quarter : Fin 4) : Nat :=
  if quarter = 3 then probabilityWaitPc round true+1 else
    match round with | .first => 4847 | .biased => 6532 | .unbiased => 7437

/-- A store after a quarter's publication has passed another successful score
wait before issuing the same quarter, including when the visits take different branches. -/
theorem probabilityStoreAfterPublicationHasNewWait (hX : Consistent l kernel Assumptions.all m X)
    (round previous : Round) (quarter : Fin 4) {g publication store addr : Nat} {vals : List Value}
    {shape : TcShape} {e : Event} (hEnd : X.get (g,publication) = some e)
    (hSite : e.pc = probabilityPublicationEnd previous quarter)
    (hStore : X.get (g,store) = some ⟨probabilityPc round quarter,.tc (.st addr vals shape)⟩)
    (hAfter : publication < store) :
    ((X.tr g).take publication).countP scoreAcquireMark <
      ((X.tr g).take store).countP scoreAcquireMark := by
  let window (r : Round) : Fin 22 :=
    if quarter = 3 then
      match r with | .first => 17 | .biased => 18 | .unbiased => 19
    else
      match r with | .first => 2 | .biased => 4 | .unbiased => 6
  let tail := (X.tr g).drop (publication+1)
  let middle := tail.take (store-(publication+1))
  have hLen : store < (X.tr g).length := len_of_get hStore
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX hEnd)
  obtain ⟨s,u,hStep,hTail⟩ := hRun.after_event hEnd (by omega)
  have he : tail[store-(publication+1)]? =
      some ⟨probabilityPc round quarter,.tc (.st addr vals shape)⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le (by omega : publication+1 ≤ store)]
    exact hStore
  obtain ⟨t,_,hMiddle,hStoreStep⟩ := hTail.before_event he
  have hWalk : TraceReach kernel Assumptions.all l g s (e::middle) t := .event hStep hMiddle
  have hs : s.pc = probabilityPublicationEnd previous quarter :=
    (estep_source_pc hStep).symm.trans hSite
  have ht : t.pc = probabilityPc round quarter := (estep_source_pc hStoreStep).symm
  have hStart : biasBodyDebt (window round) s ≤ [e].countP (biasReturnMark (window round)) := by
    cases round <;> cases previous <;> fin_cases quarter <;>
      simp [biasBodyDebt,insideBiasBody,biasWindowWait,biasWindowEnd,biasReturnMark,
        probabilityPublicationEnd,probabilityWaitPc,window,hs,hSite]
  have hFinish : biasBodyDebt (window round) t = 1 := by
    cases round <;> fin_cases quarter <;>
      simp [biasBodyDebt,insideBiasBody,biasWindowWait,biasWindowEnd,probabilityPc,window,ht]
  have hBudget := biasReadOrderPath (window round) hWalk
  rw [hFinish] at hBudget
  have hMore : 1 ≤ (e::middle).countP (biasAcquireMark (window round)) := by
    change 1 ≤ ([e] ++ middle).countP (biasAcquireMark (window round))
    rw [show e::middle = [e] ++ middle by rfl,List.countP_append] at hBudget
    omega
  have hCoverage (event : Event) : biasAcquireMark (window round) event = true →
      scoreAcquireMark event = true := by
    obtain ⟨site,kind⟩ := event
    cases kind <;> try solve | intro h; cases h
    case wait loc phase ok acq scope =>
      cases ok
      · intro h
        cases h
      · cases round <;> fin_cases quarter <;>
          simp [biasAcquireMark,scoreAcquireMark,window,biasWindowWait] <;> tauto
  have hCount := List.countP_mono_left (l := e::middle) (fun event _ => hCoverage event)
  have hPrefix : (X.tr g).take store = (X.tr g).take publication ++ e::middle := by
    have hSplit : (X.tr g)[publication]? = some e := hEnd
    calc
      (X.tr g).take store =
          (X.tr g).take (publication+1) ++ middle := by
        simp only [middle,tail,← List.take_add]
        congr 1
        omega
      _ = (X.tr g).take publication ++ e::middle := by
        rw [List.take_add_one,hSplit,Option.toList_some,List.append_assoc]
        rfl
  rw [hPrefix,List.countP_append]
  omega

/-- The next tail store is in a score visit beyond each earlier warp rendezvous. -/
theorem actualTailStoreBarrierBudget (hX : Consistent l kernel Assumptions.all m X) {g j addr : Nat}
    {vals : List Value} {shape : TcShape} (round : Round)
    (he : X.get (g,j) = some ⟨probabilityPc round 3,.tc (.st addr vals shape)⟩) :
    let before := (X.tr g).take j
    (before.countP fun e => ([4858,6543,7448] : List Nat).contains e.pc) + 1 ≤
      before.countP scoreAcquireMark := by
  let windows : Finset (Fin 22) := {17,18,19}
  let window : Round → Fin 22 := fun r =>
    match r with | .first => 17 | .biased => 18 | .unbiased => 19
  have hLive (r : Round) : window r ∈ windows ∧ insideBiasBody (window r) (probabilityPc r 3) := by
    cases r <;> decide
  have h := windowDebtMatched hX windows he ⟨_,(hLive round).1,(hLive round).2⟩
  let before := (X.tr g).take j
  have hRaw := sumDistinctMarks before 4858 6543 7448 (by decide) (by decide) (by decide)
    (fun _ => true)
  change (∑ i ∈ windows, before.countP (biasReturnMark i)) + 1 ≤
    ∑ i ∈ windows, before.countP (biasAcquireMark i) at h
  change _ + 1 ≤ before.countP scoreAcquireMark
  simp only [Bool.true_and] at hRaw
  rw [hRaw,← scoreMarkerSum]
  simp [windows, statsWindows,Finset.sum_insert,Nat.add_assoc] at h ⊢
  exact h

/-- A nonterminal statistics publication has an earlier successful score acquire for that round. -/
theorem actualStatisticsScoreBudget {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {e : Event} (he : X.get (g,j) = some e) (hMark : scoredStatisticsMark e = true) :
    let before := (X.tr g).take j
    before.countP scoredStatisticsMark + 1 ≤ before.countP scoreAcquireMark := by
  have hActive : ∃ i ∈ statsWindows, biasReturnMark i e = true := by
    have hs : e.pc = 4397 ∨ e.pc = 5683 ∨ e.pc = 6891 := by
      simpa [scoredStatisticsMark] using hMark
    rcases hs with h | h | h
    · exact ⟨8, by decide, beq_iff_eq.mpr h⟩
    · exact ⟨9, by decide, beq_iff_eq.mpr h⟩
    · exact ⟨10, by decide, beq_iff_eq.mpr h⟩
  have h := windowCreditsMatched hp hX statsWindows he hActive
  simpa only [statsMarkerSum, scoreMarkerSum] using h

/-- Before any event, each preceding nonterminal publication has a successful score acquisition. -/
theorem precedingStatisticsScoreBudget (hX : Consistent l kernel Assumptions.all m X) {g j : Nat}
    {e : Event} (he : X.get (g,j) = some e) :
    let before := (X.tr g).take j
    before.countP scoredStatisticsMark ≤ before.countP scoreAcquireMark := by
  obtain ⟨_, hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨u,_,hPath,_⟩ := hr.before_event he
  change TraceReach kernel Assumptions.all l g {} ((X.tr g).take j) u at hPath
  dsimp only
  rw [← statsMarkerSum, ← scoreMarkerSum]
  apply Finset.sum_le_sum
  intro i hi
  have h := biasReadOrderPath i hPath
  have hZero : biasBodyDebt i ({} : TState) = 0 := by fin_cases i <;> rfl
  rw [hZero, Nat.add_zero] at h
  omega

private theorem reachedWindowGuard (hX : Consistent l kernel Assumptions.all m X) (window : Fin 22)
    {g j : Nat} {e : Event} (he : X.get (g,j) = some e) (hEnd : e.pc = biasWindowEnd window) :
    ∃ k < j, ∃ q target acq scope, X.get (g,k) =
      some ⟨(biasWindowWait window).pc, .wait target q true acq scope⟩ := by
  obtain ⟨_, hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨u, _, hPath, hE⟩ := hr.before_event he
  have hP := (estep_source_pc hE).symm.trans hEnd
  have hDebt : biasBodyDebt window u = 1 := by
    unfold biasBodyDebt
    rw [hP]
    fin_cases window <;> rfl
  have hEntry : biasBodyDebt window ({} : TState) = 0 := by fin_cases window <;> rfl
  have hBudget := biasReadOrderPath window hPath
  rw [hDebt, hEntry, Nat.add_zero] at hBudget
  have hPos : 0 < ((X.tr g).take j).countP (biasAcquireMark window) := by
    change ((X.tr g).take j).countP (biasReturnMark window) + 1 ≤
      ((X.tr g).take j).countP (biasAcquireMark window) at hBudget
    omega
  obtain ⟨k,e,hGet,hMark,_⟩ := MbarRing.Slot.exists_nth_countP (biasAcquireMark window) hPos
  have hLt := (List.getElem?_eq_some_iff.mp hGet).1
  simp only [List.length_take] at hLt
  have hK : k < j := by omega
  rw [List.getElem?_take_of_lt hK] at hGet
  obtain ⟨site,kind⟩ := e
  cases kind <;> simp [biasAcquireMark] at hMark
  rename_i area q ok acq scope
  cases ok <;> simp at hMark
  exact ⟨k,hK,q,area,acq,scope,by rw [← hMark]; exact hGet⟩

/-- Each terminal MMA output commit requires its stage's terminal joint probability wait. -/
theorem terminalMmaProbabilityWaitSource (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hSite : e.pc = if stage = 0 then 2642 else 2646) :
    ∃ k < j, ∃ q target acq scope, X.get (g,k) =
      some ⟨if stage = 0 then 2548 else 2595, .wait target q true acq scope⟩ := by
  fin_cases stage
  · exact reachedWindowGuard hX 11 he hSite
  · exact reachedWindowGuard hX 12 he hSite

/-- A lane counted one successful Bias acquire for each preceding biased publication. -/
theorem biasAcquiresCoverBiasedPublications (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {e : Event} (he : X.get (g,j) = some e) :
    let before := (X.tr g).take j
    before.countP (barrierMark 4397) + before.countP (barrierMark 5683) ≤
      before.countP readSuccess := by
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t,_,hPath,_⟩ := hr.before_event he
  let before := (X.tr g).take j
  change TraceReach kernel Assumptions.all l g {} before t at hPath
  have hA := biasReadOrderPath 15 hPath
  have hB := biasReadOrderPath 16 hPath
  have hMark (ev : Event) :
      readSuccess ev = (biasAcquireMark 15 ev || biasAcquireMark 16 ev) := by
    obtain ⟨site,kind⟩ := ev
    cases kind <;> try rfl
    rename_i _ _ ok _ _
    cases ok <;> rfl
  have hSplit : before.countP readSuccess =
      before.countP (biasAcquireMark 15) + before.countP (biasAcquireMark 16) := by
    rw [show readSuccess = _ from funext hMark]
    apply countP_or_disj
    intro ev _ h
    have siteOf (window : Fin 22) (hMark : biasAcquireMark window ev = true) :
        ev.pc = (biasWindowWait window).pc := by
      unfold biasAcquireMark at hMark
      split at hMark
      · exact beq_iff_eq.mp hMark
      · cases hMark
    have hFirst : ev.pc = 3498 := siteOf 15 h.1
    have hSecond : ev.pc = 5181 := siteOf 16 h.2
    omega
  change before.countP (biasReturnMark 15) + before.countP (biasReturnMark 16) ≤ _
  have h0 : biasBodyDebt 15 ({} : TState) = 0 := rfl
  have h1 : biasBodyDebt 16 ({} : TState) = 0 := rfl
  rw [h0,Nat.add_zero] at hA
  rw [h1,Nat.add_zero] at hB
  rw [hSplit]
  omega

end PTX.Kernels.TmlFa4Fwd.Softmax
