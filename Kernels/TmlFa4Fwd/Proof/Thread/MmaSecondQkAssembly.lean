-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkAssembly
import Kernels.TmlFa4Fwd.Flow.Code.Part034
import Kernels.TmlFa4Fwd.Flow.Code.Part035

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

/-- The broadcast, parity and launch operands before the second opening QK setup. -/
def secondQKInputFacts (l : Launch) : List (Nat × Value) :=
  [(2602,b32 128),(2563,b32 0)] ++ secondQKCommonOperands l

private def secondQKStep (done : Nat) : Nat := if done = 0 then 2219 else 2218+5*done

private def secondQKCarry (l : Launch) (lead : Bool) : List (Nat × Value) :=
  [(9656,b32 (firstKLow l)),(9660,b32 0x40004040),(9632,b32 0x8200490),
   (9655,b32 (scoreColumn 1)),(9653,.pred lead),(2563,b32 0),(2535,b32 l.sharedBase)]

private structure SecondQKAssembly (l : Launch) (done : Nat) (lead : Bool) (s : TState) : Prop where
  atStep : At s (secondQKStep done) (secondQKCarry l lead)
  q : ∀ i : Fin 8, s.regs (9624+i.val) = some
    (b64 (sharedDescriptorWord (qStart l (if i.val < done then 1 else 0)+qkFragment i) 16))
  k : ∀ i : Fin 8, i.val < done → s.regs (9661+i.val) = some
    (b64 (sharedDescriptorWord (kvStart l 0+qkFragment i) 16))

private def secondAssemblyPreserved (step : Fin 8) : List Nat :=
  [9656,9660,9632,9655,9653,2563,2535] ++
  ((List.finRange 8).filter (· != step)).map (fun i => 9624+i.val) ++
  ((List.finRange 8).filter (· != step)).map (fun i => 9661+i.val)

set_option maxRecDepth 100000 in
private theorem secondAssemblyStable (step : Fin 8) :
    ((kernel.code.drop (qkSetupPc 1 step)).take (qkFirstSetupCount step)).all
      (fun ins => (secondAssemblyPreserved step).all
        (fun r => !(writesRegs ins.op).contains r)) = true := by
  fin_cases step <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem secondAssemblyLinear (step : Fin 8) :
    ((kernel.code.drop (qkSetupPc 1 step)).take (qkFirstSetupCount step-1)).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  fin_cases step <;> kernel_rfl

private theorem secondAssemblyAdvance {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (step : Fin 8) {lead : Bool} {s : TState}
    (hs : SecondQKAssembly l step.val lead s) :
    ∃ u, run kernel Assumptions.all l g (qkFirstSetupCount step) s = some u ∧
      SecondQKAssembly l (step.val+1) lead u := by
  let hi := startupQLow l+qkFragment step/16
  let lo := hi-2048
  have hShared := hp.shared.2.1
  have hFrag : qkFragment step/16 ≤ 1030 := by fin_cases step <;> decide
  have hBack : 2048 ≤ lo := by dsimp [lo,hi,startupQLow]; omega
  have hHigh : lo+2048 = hi := by omega
  have hNext : lo+2048 < 2^32 := by rw [hHigh]; dsimp [hi,startupQLow]; omega
  have hQ : lo < 2^32 := by omega
  have hK : firstKLow l+1030 < 2^32 := by
    have hZero : kvSlot 0 = 0 := rfl
    simp only [firstKLow,kvStart,hZero,Nat.mul_zero,Nat.add_zero]
    omega
  have hBefore : s.pc = qkSetupPc 1 step := hs.atStep.1.trans (by fin_cases step <;> rfl)
  have hAfter : qkSetupPc 1 step+qkFirstSetupCount step = secondQKStep (step.val+1) := by
    fin_cases step <;> rfl
  have hWord : s.regs (9624+step.val) = some (b64 (lo+2^32*0x40004040)) := by
    simpa only [Nat.lt_irrefl,↓reduceIte,(qWords l step).2] using hs.q step
  obtain ⟨u,hu,hU⟩ := qkSetupFragment l g 1 step hQ hBack hNext hK s
    ⟨hBefore,hs.atStep.2.1,hs.atStep.2.2.1,hs.atStep.2.2.2.1,
      hWord,hs.atStep.2.2.2.2.1,hs.atStep.2.2.2.2.2.1,trivial⟩
  have hFrame (r : Nat) (hr : r ∈ secondAssemblyPreserved step) : u.regs r = s.regs r :=
    schedulerLocalFrame (secondAssemblyStable step) (secondAssemblyLinear step) hu
      hBefore.ge (by rw [hBefore]) hr
  have hRetain : Holds u.regs (secondQKCarry l lead) := by
    apply holdsSchedulerFrame (regs := secondAssemblyPreserved step) hs.atStep.2.2.2.2 hFrame
    intro pair hm
    simp only [secondQKCarry,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [secondAssemblyPreserved]
  have hScope : 1904 ≤ qkSetupPc 1 step ∧ qkSetupPc 1 step+qkFirstSetupCount step ≤ 2768 := by
    fin_cases step <;> decide
  refine ⟨u,localRun hScope.1 hScope.2 hBefore (secondAssemblyLinear step) hu,
    ⟨hU.1.trans hAfter,hU.2.1,hU.2.2.1,hU.2.2.2.1,hRetain⟩,?_,?_⟩
  · intro i
    by_cases hI : i = step
    · subst i
      have hRetarget : qkRetargetLow 1 lo = hi := hHigh
      simpa only [Nat.lt_succ_self,↓reduceIte,(qWords l step).1,hRetarget] using hU.2.2.2.2.1
    · have hVal : i.val ≠ step.val := fun h => hI (Fin.ext h)
      have hLt : (i.val < step.val+1) = (i.val < step.val) := propext (by omega)
      rw [hFrame (9624+i.val) (by
        simp only [secondAssemblyPreserved,List.mem_append]
        exact .inl (.inr (List.mem_map_of_mem (List.mem_filter.mpr ⟨by simp,by simp [hI]⟩))))]
      simpa only [hLt] using hs.q i
  · intro i hI
    by_cases hEq : i = step
    · subst i
      simpa only [kWord,qkBReg] using hU.2.2.2.2.2.1
    · have hVal : i.val ≠ step.val := fun h => hEq (Fin.ext h)
      rw [hFrame (9661+i.val) (by
        simp only [secondAssemblyPreserved,List.mem_append]
        exact .inr (List.mem_map_of_mem (List.mem_filter.mpr ⟨by simp,by simp [hEq]⟩)))]
      exact hs.k i (by omega)

private theorem secondAssemblyAll {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {lead : Bool} {s : TState} (hs : SecondQKAssembly l 0 lead s) :
    ∀ done ≤ 8, ∃ u, run kernel Assumptions.all l g (secondQKStep done-2219) s = some u ∧
      SecondQKAssembly l done lead u := by
  intro done hDone
  induction done with
  | zero => exact ⟨s,rfl,hs⟩
  | succ done ih =>
    obtain ⟨v,hv,hV⟩ := ih (by omega)
    let step : Fin 8 := ⟨done,by omega⟩
    obtain ⟨u,hu,hU⟩ := secondAssemblyAdvance hp g step hV
    have hLength : (secondQKStep done-2219)+qkFirstSetupCount step =
        secondQKStep (done+1)-2219 := by
      dsimp only [secondQKStep,qkFirstSetupCount,step]
      by_cases h : done = 0
      · simp [h]
      · simp only [ite_eq_right h,Nat.add_one_ne_zero,↓reduceIte]
        omega
    rw [← hLength]
    exact ⟨u,run_comp hv hu,hU⟩

/-- The second opening setup switches all eight query descriptors to bank one and reconstructs
their matching first-slot key words. The only tensor issuer is the elected lane. -/
theorem secondQKAssemblyAtIssue {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {lead : Bool}
    (hs : At s 2216 ((9653,.pred lead) :: secondQKInputFacts l)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 2259 [(9653,.pred lead),(2535,b32 l.sharedBase)] ∧
      (lead = true → ∀ i, Holds u.regs (qkIssueFacts l 1 i 0)) := by
  have hSeg : Seg kernel [] l g 3 2216 ((9653,.pred lead) :: secondQKInputFacts l)
      2219 (secondQKCarry l lead ++ qDescriptorFacts l 0) := by
    intro t ht
    simp only [secondQKInputFacts,secondQKCarry,secondQKCommonOperands,secondQKRootFacts,
      scoreColumn,
      qDescriptorFacts,List.finRange_succ,List.finRange_zero,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,Fin.val_succ] at ht ⊢
    seg_fp ht using rfl
  obtain ⟨t,ht,hT⟩ := hSeg s hs
  have hStart := localRun (by decide) (by decide) hs.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) ht
  have hFrame := (holds_append ..).mp hT.2.2.2.2
  have hInitial : SecondQKAssembly l 0 lead t := by
    refine ⟨hT.mono hFrame.1,?_,?_⟩
    · intro i
      have hMem : (9624+i.val,b64 (sharedDescriptorWord (qStart l 0+qkFragment i) 16)) ∈
          qDescriptorFacts l 0 := List.mem_map_of_mem (by simp)
      simpa only [Nat.not_lt_zero,↓reduceIte] using holds_mem hFrame.2 hMem
    · intro i hi
      omega
  obtain ⟨v,hv,hV⟩ := secondAssemblyAll hp g hInitial 8 (by decide)
  have hSet : Seg kernel [] l g 1 2258 [(2563,b32 0)] 2259 [(9654,.pred false)] := by
    intro z hz
    seg_fp hz using rfl
  have hAt : At v 2258 [(2563,b32 0)] := hV.atStep.mono ⟨hV.atStep.2.2.2.2.2.2.2.2.2.1,trivial⟩
  obtain ⟨u,hu,hU⟩ := hSet v hAt
  have hFinal := localRun (by decide) (by decide) hAt.1 rfl hu
  have hTau : Tau kernel [] l g v u := by
    apply tauStep_iff.mp
    unfold run at hu
    cases h : tauStep kernel [] l g v <;> simp_all [run]
  have hCode := Flow.code_2258
  rw [← hAt.1] at hCode
  have hKeep (r : Nat) (hr : r ≠ 9654) : u.regs r = v.regs r :=
    tau_core_regs hCode hTau (by simpa [writesRegs] using hr)
  have hF := hV.atStep.2.2.2.2
  have hGuard := (hKeep 9653 (by decide)).trans hF.2.2.2.2.1
  have hShared := (hKeep 2535 (by decide)).trans hF.2.2.2.2.2.2.1
  refine ⟨u,run_rtg (run_comp (run_comp hStart hv) hFinal),hU.mono ⟨hGuard,hShared,trivial⟩,?_⟩
  intro hLead i
  have hDest := (hKeep 9655 (by decide)).trans hF.2.2.2.1
  have hId := (hKeep 9632 (by decide)).trans hF.2.2.1
  have hQa : u.regs (9624+i.val) = some
      (b64 (sharedDescriptorWord (qStart l 1+qkFragment i) 16)) := by
    rw [hKeep _ (by have := i.isLt; omega)]
    simpa only [ite_eq_left i.isLt] using hV.q i
  have hKb := (hKeep (9661+i.val) (by omega)).trans (hV.k i i.isLt)
  exact ⟨by simpa only [hLead,qkGuard] using hGuard,hDest,hQa,hKb,hId,trivial⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
