-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaWarpQkPacket
public import Kernels.TmlFa4Fwd.Proof.MmaRecurringKeyPack
import all Kernels.TmlFa4Fwd.Proof.MmaRecurringKeyPack
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTiles
import Kernels.TmlFa4Fwd.Proof.MmaQkAssembly

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue
open Thread (keyDescriptorLow)

noncomputable section

private def recurringAssemblyPc (stage : Fin 2) (done : Nat) : Nat :=
  qkSetupPc (recurringKeyBlock stage) 0+(5*done-1)

private def recurringAssembler (l : Launch) (stage : Fin 2) (use : Nat) : List (Nat × Value) :=
  let block := recurringKeyBlock stage
  [(qkBReg block-5,b32 (keyDescriptorLow l use)),(qkBReg block-1,b32 0x40004040)]

private structure RecurringQkAssembly (l : Launch) (stage : Fin 2) (use done : Nat)
    (s : TState) : Prop where
  cursor : At s (recurringAssemblyPc stage done) (recurringAssembler l stage use)
  query : ∀ i : Fin 8, s.regs (9624+i.val) = some
    (b64 (sharedDescriptorWord
      (qStart l (if i.val < done then stage else 1-stage)+qkFragment i) 16))
  key : ∀ i : Fin 8, i.val < done → s.regs (qkBReg (recurringKeyBlock stage)+i.val) = some
    (b64 (sharedDescriptorWord (kvStart l use+qkFragment i) 16))

private def setupKeep (stage : Fin 2) (step : Fin 8) : List Nat :=
  let b := qkBReg (recurringKeyBlock stage)
  [b-5,b-1] ++
    ((List.finRange 8).filter (· != step)).map (fun i => 9624+i.val) ++
    ((List.finRange 8).filter (· != step)).map (fun i => b+i.val)

private theorem recurringAssemblyStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) (step : Fin 8) {use : Nat} {s : TState}
    (hs : RecurringQkAssembly l stage use step.val s) :
    ∃ u, run kernel [] l g (qkFirstSetupCount step) s = some u ∧
      RecurringQkAssembly l stage use (step.val+1) u := by
  let block := recurringKeyBlock stage
  let high := startupQLow l+qkFragment step/16
  let low := if stage = 0 then high else high-2048
  have hBounds : 2048 ≤ low ∧ low+2048 < 2^32 := by
    have hShared := hp.shared.2.1
    have hFrag : qkFragment step/16 ≤ 1030 := by fin_cases step <;> decide
    unfold low high startupQLow
    split_ifs <;> omega
  have hInput : sharedDescriptorWord (qStart l (1-stage)+qkFragment step) 16 =
      low+2^32*0x40004040 := by
    fin_cases stage
    · exact (qWords l step).1
    · exact (qWords l step).2
  have hOutput : sharedDescriptorWord (qStart l stage+qkFragment step) 16 =
      qkRetargetLow block low+2^32*0x40004040 := by
    have hHi : 2048 ≤ high := by dsimp only [high,startupQLow]; omega
    dsimp only [block,low]
    fin_cases stage
    · change _ = high-2048+2^32*0x40004040
      exact (qWords l step).2
    · change _ = (high-2048+2048)+2^32*0x40004040
      rw [Nat.sub_add_cancel hHi]
      exact (qWords l step).1
  have hPc : s.pc = qkSetupPc block step := hs.cursor.1.trans (by
    dsimp only [block]
    fin_cases stage <;> fin_cases step <;> decide)
  have hAfter : qkSetupPc block step+qkFirstSetupCount step =
      recurringAssemblyPc stage (step.val+1) := by
    dsimp only [block]
    fin_cases stage <;> fin_cases step <;> decide
  have hQuery := hs.query step
  rw [ite_eq_right (Nat.lt_irrefl _),hInput] at hQuery
  obtain ⟨u,hu,hU⟩ := qkSetupFragment l g block step (loQ := low) (loK := keyDescriptorLow l use)
    (show low < 2^32 by omega) hBounds.1 hBounds.2 (recurringKWordBound hp use) s
    ⟨hPc,hs.cursor.2.1,hs.cursor.2.2.1,hs.cursor.2.2.2.1,hQuery,
      hs.cursor.2.2.2.2.1,hs.cursor.2.2.2.2.2.1,trivial⟩
  have hSafe : ((kernel.code.drop (qkSetupPc block step)).take (qkFirstSetupCount step)).all
      (fun i => (setupKeep stage step).all fun r => !(writesRegs i.op).contains r) = true := by
    dsimp only [block]
    fin_cases stage <;> fin_cases step <;> decide +kernel
  have hFlow : ((kernel.code.drop (qkSetupPc block step)).take
      (qkFirstSetupCount step-1)).all (fun i => schedulerFallsThrough i.op) = true := by
    dsimp only [block]
    fin_cases stage <;> fin_cases step <;> decide +kernel
  have hKeep {r : Nat} (hr : r ∈ setupKeep stage step) : u.regs r = s.regs r :=
    schedulerLocalFrame hSafe hFlow hu hPc.ge (by rw [hPc]) hr
  have hCarry : Holds u.regs (recurringAssembler l stage use) := by
    exact ⟨(hKeep (by simp [setupKeep])).trans hs.cursor.2.2.2.2.1,
      (hKeep (by simp [setupKeep])).trans hs.cursor.2.2.2.2.2.1,trivial⟩
  refine ⟨u,hu,⟨⟨hU.1.trans hAfter,hU.2.1,hU.2.2.1,hU.2.2.2.1,hCarry⟩,?_,?_⟩⟩
  · intro i
    by_cases hI : i = step
    · subst i
      simpa only [Nat.lt_succ_self,↓reduceIte,hOutput] using hU.2.2.2.2.1
    · have hVal : i.val ≠ step.val := fun h => hI (Fin.ext h)
      have hLt : (i.val < step.val+1) = (i.val < step.val) := propext (by omega)
      rw [hKeep (r := 9624+i.val) (by
        simp only [setupKeep,List.mem_append]
        exact .inl (.inr (List.mem_map_of_mem (List.mem_filter.mpr ⟨by simp,by simp [hI]⟩))))]
      simpa only [hLt] using hs.query i
  · intro i hi
    by_cases hI : i = step
    · subst i
      simpa only [recurringKeyPackedWord] using hU.2.2.2.2.2.1
    · have hVal : i.val ≠ step.val := fun h => hI (Fin.ext h)
      rw [hKeep (r := qkBReg block+i.val) (by
        simp only [setupKeep,List.mem_append]
        exact .inr (List.mem_map_of_mem (List.mem_filter.mpr ⟨by simp,by simp [hI]⟩)))]
      exact hs.key i (by omega)

private theorem recurringAssemblyAll {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) {use : Nat} {s : TState}
    (hs : RecurringQkAssembly l stage use 0 s) :
    ∀ done ≤ 8, ∃ u, run kernel [] l g (5*done-1) s = some u ∧
      RecurringQkAssembly l stage use done u := by
  intro done hDone
  induction done with
  | zero => exact ⟨s,rfl,hs⟩
  | succ done ih =>
    obtain ⟨v,hv,hV⟩ := ih (by omega)
    let step : Fin 8 := ⟨done,by omega⟩
    obtain ⟨u,hu,hU⟩ := recurringAssemblyStep hp g stage step hV
    have hLength : (5*done-1)+qkFirstSetupCount step = 5*(done+1)-1 := by
      dsimp only [qkFirstSetupCount,step]
      by_cases h : done = 0
      · simp [h]
      · simp only [ite_eq_right h]
        omega
    rw [← hLength]
    exact ⟨u,run_comp hv hu,hU⟩

/-- Live destination, current K descriptor, and zero special-predicate sources
carried into the elected recurring QK setup. -/
def recurringQkPhaseReg (stage : Fin 2) : Nat := if stage = 0 then 2573 else 2601

def recurringQkSourceColumn (stage : Fin 2) : Nat := if stage = 0 then 2574 else 2602

def recurringQkEntry (l : Launch) (stage : Fin 2) (use : Nat) (lead : Bool) :
    List (Nat × Value) :=
  let block := recurringKeyBlock stage
  [(qkGuard block,.pred lead),(recurringQkSourceColumn stage,b32 (scoreColumn stage)),
    (2600,b32 (keyDescriptorLow l use)),(9632,b32 0x8200490),(recurringQkPhaseReg stage,b32 0)] ++
    qDescriptorFacts l (1-stage)

private theorem recurringInitialMoves {l : Launch} {g use : Nat} (stage : Fin 2) :
    let block := recurringKeyBlock stage
    Seg kernel [] l g 3 (qkSetupPc block 0-3)
      [(recurringQkSourceColumn stage,b32 (scoreColumn stage)),
        (2600,b32 (keyDescriptorLow l use))]
      (qkSetupPc block 0) ((qkDestination block,b32 (scoreColumn stage))::
        recurringAssembler l stage use) := by
  dsimp only
  fin_cases stage <;> intro s hs <;>
    simp only [recurringQkSourceColumn,recurringKeyBlock,recurringAssembler] at hs ⊢ <;>
    seg_fp hs using rfl

private theorem recurringLastPredicate (l : Launch) (g : Nat) (stage : Fin 2) :
    let block := recurringKeyBlock stage
    Seg kernel [] l g 1 (qkPc block-1) [(recurringQkPhaseReg stage,b32 0)]
      (qkPc block) [(qkGuard block+1,.pred false)] := by
  dsimp only
  fin_cases stage <;> intro s hs <;>
    simp only [recurringQkPhaseReg,recurringKeyBlock] at hs ⊢ <;> seg_fp hs using decide

/-- Run all recurring QK setup instructions from the elected operand checkpoint,
preserving a caller frame and instantiating every canonical K and Q descriptor. -/
theorem recurringQkSetupOfElected {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g : Nat) (stage : Fin 2) (use : Nat) (lead : Bool)
    {F : List (Nat × Value)} {t : TState}
    (ht : At t (qkSetupPc (recurringKeyBlock stage) 0-3)
      (recurringQkEntry l stage use lead ++ F))
    (hFrame : ((kernel.code.drop (qkSetupPc (recurringKeyBlock stage) 0-3)).take 43).all
      (fun ins => (F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (qkPc (recurringKeyBlock stage))
        ((qkGuard (recurringKeyBlock stage),.pred lead)::F ++
          qDescriptorFacts l stage) ∧
      (lead = true → ∀ i, Holds u.regs (qkIssueFacts l (recurringKeyBlock stage) i use)) := by
  let block := recurringKeyBlock stage
  have hEntry := (holds_append ..).mp ht.2.2.2.2
  have hReg := hEntry.1
  obtain ⟨s,hs,hS⟩ := (recurringInitialMoves (l := l) (g := g) (use := use) stage).apply
    (ht.mono ⟨hReg.2.1,hReg.2.2.1,trivial⟩)
  have hPc : qkSetupPc block 0+0 = recurringAssemblyPc stage 0 := by
    dsimp [recurringAssemblyPc,block]
  have hQueryKeep (i : Fin 8) : s.regs (9624+i.val) = t.regs (9624+i.val) := by
    have hAudit : ((kernel.code.drop (qkSetupPc block 0-3)).take 3).all
        (fun ins => ((List.finRange 8).map (fun j => 9624+j.val)).all
          (fun r => !(writesRegs ins.op).contains r)) = true := by
      dsimp only [block]
      fin_cases stage <;> decide +kernel
    have hStraight : ((kernel.code.drop (qkSetupPc block 0-3)).take 2).all
        (fun ins => schedulerFallsThrough ins.op) = true := by
      dsimp only [block]
      fin_cases stage <;> decide +kernel
    exact schedulerLocalFrame hAudit hStraight hs ht.1.ge (by rw [ht.1])
      (List.mem_map_of_mem (by simp))
  have hInitial : RecurringQkAssembly l stage use 0 s := by
    refine ⟨⟨hS.1.trans (by simpa using hPc),hS.2.1,hS.2.2.1,hS.2.2.2.1,
      hS.2.2.2.2.2⟩,?_,?_⟩
    · intro i
      rw [hQueryKeep,ite_eq_right (Nat.not_lt_zero _)]
      exact holds_mem hReg.2.2.2.2.2 (List.mem_map_of_mem (by simp))
    · intro i hi
      exact (Nat.not_lt_zero _ hi).elim
  obtain ⟨v,hv,hV⟩ := recurringAssemblyAll hp g stage hInitial 8 (by decide)
  have hBranchPc : recurringAssemblyPc stage 8 = qkPc block-1 := by
    dsimp only [block]
    fin_cases stage <;> decide
  have hPrefix : run kernel [] l g 42 t = some v := run_comp hs hv
  have hPhase : v.regs (recurringQkPhaseReg stage) = some (b32 0) := by
    have hSafe : ((kernel.code.drop (qkSetupPc block 0-3)).take 42).all
        (fun ins => !((writesRegs ins.op).contains (recurringQkPhaseReg stage))) = true := by
      dsimp only [block]
      fin_cases stage <;> decide +kernel
    have hStraight : ((kernel.code.drop (qkSetupPc block 0-3)).take 41).all
        (fun ins => schedulerFallsThrough ins.op) = true := by
      dsimp only [block]
      fin_cases stage <;> decide +kernel
    have hKeep := schedulerLocalFrame (regs := [recurringQkPhaseReg stage])
      (r := recurringQkPhaseReg stage)
      (by simpa only [List.all_cons,List.all_nil,Bool.and_true] using hSafe)
      hStraight hPrefix ht.1.ge (by rw [ht.1]) (by simp)
    exact hKeep.trans hReg.2.2.2.2.1
  obtain ⟨u,hu,hU⟩ := (recurringLastPredicate l g stage).apply
    ⟨hV.cursor.1.trans hBranchPc,hV.cursor.2.1,hV.cursor.2.2.1,hV.cursor.2.2.2.1,hPhase,trivial⟩
  have hScope : 1904 ≤ qkSetupPc block 0-3 ∧ (qkSetupPc block 0-3)+43 ≤ 2768 := by
    dsimp only [block]; fin_cases stage <;> decide
  have hStraight : ((kernel.code.drop (qkSetupPc block 0-3)).take 42).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
    dsimp only [block]; fin_cases stage <;> decide +kernel
  have hAll := run_comp hPrefix hu
  have hKeepAt := ht.mono hEntry.2
  obtain ⟨hPath,hF⟩ := activeDrainLocalKeep hKeepAt hScope.1 hScope.2 hFrame hStraight hAll
  have hLastKeep {r : Nat} (hr : r ≠ qkGuard block+1) : u.regs r = v.regs r := by
    have hEq : (kernel.code[(qkPc block)-1]?).map (fun i => writesRegs i.op) =
        some [qkGuard block+1] := by
      dsimp only [block]; fin_cases stage <;> decide +kernel
    have hTau : Tau kernel [] l g v u := by
      apply tauStep_iff.mp
      simp only [run] at hu
      cases h : tauStep kernel [] l g v with
      | none => rw [h] at hu; cases hu
      | some w =>
        simp only [h,Option.bind_some,Option.some.injEq] at hu
        exact congrArg some hu
    obtain ⟨ins,hCode⟩ := tau_core_has_code hTau
    have hPc := hV.cursor.1.trans hBranchPc
    rw [← hPc,hCode] at hEq
    have hWrites : writesRegs ins.op = [qkGuard block+1] := Option.some.inj hEq
    exact tau_core_regs hCode hTau (by simpa [hWrites] using hr)
  have hWords (i : Fin 8) : u.regs (9624+i.val) = some
      (b64 (sharedDescriptorWord (qStart l stage+qkFragment i) 16)) := by
    have hBound := i.isLt
    rw [hLastKeep (by dsimp only [block]; fin_cases stage <;> simp [recurringKeyBlock,qkGuard] <;>
      omega)]
    simpa only [ite_eq_left i.isLt] using hV.query i
  have hKeepGid : ((kernel.code.drop (qkSetupPc block 0-3)).take 43).all
      (fun ins => ([qkGuard block,9632]).all
        (fun r => !(writesRegs ins.op).contains r)) = true := by
    dsimp only [block]; fin_cases stage <;> decide +kernel
  have hGuard := (schedulerLocalFrame hKeepGid hStraight hAll ht.1.ge (by rw [ht.1])
    (show qkGuard block ∈ [qkGuard block,9632] by simp)).trans hReg.1
  have hId := (schedulerLocalFrame hKeepGid hStraight hAll ht.1.ge (by rw [ht.1])
    (show 9632 ∈ [qkGuard block,9632] by simp)).trans hReg.2.2.2.1
  refine ⟨u,hPath,hU.mono ⟨hGuard,(holds_append ..).mpr ⟨hF,?_⟩⟩,?_⟩
  · unfold qDescriptorFacts
    generalize List.finRange 8 = steps
    induction steps with
    | nil => trivial
    | cons i rest ih => exact ⟨hWords i,ih⟩
  · intro hLead i
    have hDestSafe : ((kernel.code.drop (qkSetupPc block 0)).take 40).all
        (fun ins => ([qkDestination block]).all
          (fun r => !(writesRegs ins.op).contains r)) = true := by
      dsimp only [block]; fin_cases stage <;> decide +kernel
    have hDestFlow : ((kernel.code.drop (qkSetupPc block 0)).take 39).all
        (fun ins => schedulerFallsThrough ins.op) = true := by
      dsimp only [block]; fin_cases stage <;> decide +kernel
    have hDestFrame := schedulerLocalFrame hDestSafe hDestFlow (run_comp hv hu)
      hS.1.ge (by rw [hS.1]) (show qkDestination block ∈ [qkDestination block] by simp)
    have hDest := hDestFrame.trans hS.2.2.2.2.1
    have hKey := (hLastKeep (r := qkBReg block+i.val) (by
      have hBound := i.isLt
      dsimp only [block]
      fin_cases stage <;> simp [recurringKeyBlock,qkGuard,qkBReg] <;> omega)).trans
      (hV.key i i.isLt)
    have hStage : qkStage block = stage := by dsimp only [block]; fin_cases stage <;> rfl
    change Holds u.regs (qkIssueFacts l block i use)
    rw [qkIssueFacts,hStage]
    exact ⟨by simpa only [hLead] using hGuard,hDest,hWords i,hKey,hId,trivial⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
