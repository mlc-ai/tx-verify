-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkSetup
public import Kernels.TmlFa4Fwd.Proof.MmaQRegisters
public import Kernels.TmlFa4Fwd.Proof.MmaQkCommit
public import Lemmas.Flow.TauFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

def firstKLow (l : Launch) : Nat := kvStart l 0 / 16 + 65536

private def firstQKPc (done : Nat) : Nat := if done = 0 then 2157 else 2156 + 5 * done

private def firstQKCarry (l : Launch) (lead : Bool) : List (Nat × Value) :=
  [(9639, b32 (firstKLow l)), (9643, b32 0x40004040), (9632, b32 0x8200490),
   (9638, b32 (scoreColumn 0)), (9636, .pred lead), (2536, b32 0),
   (1188, b32 (l.sharedBase + 80)), (2562, b32 (l.sharedBase + 8)),
   (2564, b32 (firstKLow l)), (2535,b32 l.sharedBase)]

private structure FirstQKAssembly (l : Launch) (done : Nat) (lead : Bool) (s : TState) : Prop where
  atStep : At s (firstQKPc done) (firstQKCarry l lead)
  q : ∀ i : Fin 8, s.regs (9624 + i.val) = some
    (b64 (sharedDescriptorWord (qStart l (if i.val < done then 0 else 1) + qkFragment i) 16))
  k : ∀ i : Fin 8, i.val < done → s.regs (9644 + i.val) = some
    (b64 (sharedDescriptorWord (kvStart l 0 + qkFragment i) 16))

/-- The two physical query banks differ from one another by 2048 descriptor units. -/
theorem qWords (l : Launch) (step : Fin 8) :
    let lo := startupQLow l + qkFragment step / 16
    sharedDescriptorWord (qStart l 1 + qkFragment step) 16 = lo + 2 ^ 32 * 0x40004040 ∧
      sharedDescriptorWord (qStart l 0 + qkFragment step) 16 = lo - 2048 + 2 ^ 32 * 0x40004040 := by
  intro lo
  have hFrag : qkFragment step % 16 = 0 := by fin_cases step <;> decide
  have hHi : (1 : Fin 2).val = 1 := rfl
  have hLo : (0 : Fin 2).val = 0 := rfl
  simp only [lo, sharedDescriptorWord, startupQLow, qStart, hHi, hLo]
  omega

/-- The opening key fragment uses the first physical slot and its intra-tile displacement. -/
theorem kWord (l : Launch) (step : Fin 8) :
    sharedDescriptorWord (kvStart l 0 + qkFragment step) 16 =
      firstKLow l + qkFragment step / 16 + 2 ^ 32 * 0x40004040 := by
  have hFrag : qkFragment step % 16 = 0 := by fin_cases step <;> decide
  unfold sharedDescriptorWord firstKLow
  omega

private def assemblyPreserved (step : Fin 8) : List Nat :=
  [9639, 9643, 9632, 9638, 9636, 2536, 1188, 2562, 2564, 2535] ++
    (((List.finRange 8).filter (fun i => i != step)).map (fun i => 9624 + i.val)) ++
    (((List.finRange 8).filter (fun i => i != step)).map (fun i => 9644 + i.val))

private theorem firstAssemblyStable (step : Fin 8) :
    ((kernel.code.drop (qkFirstSetupPc step)).take
      (qkFirstSetupCount step)).all
      (fun ins => (assemblyPreserved step).all
        fun r => !(writesRegs ins.op).contains r) = true := by
  fin_cases step <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem firstAssemblyLinear (step : Fin 8) :
    ((kernel.code.drop (qkFirstSetupPc step)).take (qkFirstSetupCount step - 1)).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  fin_cases step <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem firstAssemblyAdvance {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (step : Fin 8) {lead : Bool} {s : TState}
    (hs : FirstQKAssembly l step.val lead s) :
    ∃ u, run kernel Assumptions.all l g (qkFirstSetupCount step) s = some u ∧
      FirstQKAssembly l (step.val + 1) lead u := by
  let lo := startupQLow l + qkFragment step / 16
  have hShared := hp.shared.2.1
  have hOkQ : lo < 2 ^ 32 := by
    have hFrag : qkFragment step / 16 ≤ 1030 := by fin_cases step <;> decide
    dsimp only [lo, startupQLow]
    omega
  have hBackQ : 2048 ≤ lo := by dsimp only [lo, startupQLow]; omega
  have hK : firstKLow l + 1030 < 2 ^ 32 := by
    have hZero : kvSlot 0 = 0 := rfl
    simp only [firstKLow, kvStart, hZero, Nat.mul_zero, Nat.add_zero]
    omega
  have hBefore : s.pc = qkFirstSetupPc step := hs.atStep.1
  have hAfter : qkFirstSetupPc step + qkFirstSetupCount step = firstQKPc (step.val + 1) := by
    fin_cases step <;> rfl
  have hQ : s.regs (9624 + step.val) = some (b64 (lo + 2 ^ 32 * 0x40004040)) := by
    simpa only [Nat.lt_irrefl, ↓reduceIte, (qWords l step).1] using hs.q step
  obtain ⟨u, hu, hU⟩ := qkFirstSetupFragment l g step hOkQ hBackQ hK s
    ⟨hBefore, hs.atStep.2.1, hs.atStep.2.2.1, hs.atStep.2.2.2.1, hQ, hs.atStep.2.2.2.2.1,
      hs.atStep.2.2.2.2.2.1, trivial⟩
  have hFrame (r : Nat) (hr : r ∈ assemblyPreserved step) : u.regs r = s.regs r :=
    schedulerLocalFrame (firstAssemblyStable step) (firstAssemblyLinear step) hu
      hBefore.ge (by rw [hBefore]) hr
  have hRetain : Holds u.regs (firstQKCarry l lead) := by
    apply holdsSchedulerFrame (regs := assemblyPreserved step) hs.atStep.2.2.2.2 hFrame
    intro pair hm
    simp only [firstQKCarry, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [assemblyPreserved]
  have hQstable (i : Fin 8) (hNe : i ≠ step) :
      u.regs (9624 + i.val) = s.regs (9624 + i.val) := by
    apply hFrame
    simp only [assemblyPreserved, List.mem_append]
    exact .inl (.inr (List.mem_map_of_mem (List.mem_filter.mpr ⟨by simp, by simp [hNe]⟩)))
  have hKstable (i : Fin 8) (hNe : i ≠ step) :
      u.regs (9644 + i.val) = s.regs (9644 + i.val) := by
    apply hFrame
    simp only [assemblyPreserved, List.mem_append]
    exact .inr (List.mem_map_of_mem (List.mem_filter.mpr ⟨by simp, by simp [hNe]⟩))
  have hInScope : 1904 ≤ qkFirstSetupPc step ∧
      qkFirstSetupPc step + qkFirstSetupCount step ≤ 2768 := by
    fin_cases step <;> decide
  refine ⟨u, localRun hInScope.1 hInScope.2 hBefore (firstAssemblyLinear step) hu,
    ⟨hU.1.trans hAfter, hU.2.1, hU.2.2.1, hU.2.2.2.1, hRetain⟩, ?_, ?_⟩
  · intro i
    by_cases hI : i = step
    · subst i
      simpa only [Nat.lt_succ_self, ↓reduceIte, (qWords l step).2] using hU.2.2.2.2.1
    · have hVal : i.val ≠ step.val := fun h => hI (Fin.ext h)
      have hLt : (i.val < step.val + 1) = (i.val < step.val) := by
        apply propext
        omega
      rw [hQstable i hI]
      simpa only [hLt] using hs.q i
  · intro i hI
    by_cases hEq : i = step
    · subst i
      simpa only [kWord] using hU.2.2.2.2.2.1
    · have hVal : i.val ≠ step.val := fun h => hEq (Fin.ext h)
      rw [hKstable i hEq]
      exact hs.k i (by omega)

private theorem firstAssemblyAll {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {lead : Bool} {s : TState} (hs : FirstQKAssembly l 0 lead s) :
    ∀ done ≤ 8, ∃ u, run kernel Assumptions.all l g (firstQKPc done - 2157) s = some u ∧
      FirstQKAssembly l done lead u := by
  intro done hDone
  induction done with
  | zero => exact ⟨s, rfl, hs⟩
  | succ done ih =>
    obtain ⟨v, hv, hV⟩ := ih (by omega)
    let step : Fin 8 := ⟨done, by omega⟩
    obtain ⟨u, hu, hU⟩ := firstAssemblyAdvance hp g step hV
    have hLength : (firstQKPc done - 2157) + qkFirstSetupCount step =
        firstQKPc (done + 1) - 2157 := by
      dsimp only [firstQKPc, qkFirstSetupCount, step]
      by_cases h : done = 0
      · simp [h]
      · simp only [ite_eq_right h, Nat.add_one_ne_zero, ↓reduceIte]
        omega
    rw [← hLength]
    exact ⟨u, run_comp hv hu, hU⟩

/-- The three scalar moves after the first election bind the broadcast operands and the common
descriptor word, ready for all eight fragment setups. -/
def firstQKInputFacts (l : Launch) : List (Nat × Value) :=
  [(2574, b32 (scoreColumn 0)), (2564, b32 (firstKLow l)), (9632, b32 0x8200490),
   (2536, b32 0), (1188, b32 (l.sharedBase + 80)), (2562, b32 (l.sharedBase + 8)),
   (2535,b32 l.sharedBase)] ++
    qDescriptorFacts l 1

private theorem firstAssemblyStart {l : Launch} {g : Nat} {lead : Bool} {s : TState}
    (hs : At s 2154 ((9636, .pred lead) :: firstQKInputFacts l)) :
    ∃ u, run kernel Assumptions.all l g 3 s = some u ∧ FirstQKAssembly l 0 lead u := by
  have hSeg : Seg kernel [] l g 3 2154 ((9636, .pred lead) :: firstQKInputFacts l)
      2157 (firstQKCarry l lead ++ qDescriptorFacts l 1) := by
    intro t ht
    simp only [firstQKInputFacts, firstQKCarry, scoreColumn, Fin.val_zero, Nat.mul_zero,
      qDescriptorFacts, List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Fin.val_succ] at ht ⊢
    seg_fp ht using rfl
  obtain ⟨u, hu, hU⟩ := hSeg s hs
  have hRun := localRun (by decide) (by decide) hs.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hu
  have hFacts := ((holds_append _ _ _).mp hU.2.2.2.2)
  refine ⟨u, hRun, hU.mono hFacts.1, ?_, ?_⟩
  · intro i
    have hMem : (9624 + i.val, b64 (sharedDescriptorWord (qStart l 1 + qkFragment i) 16)) ∈
        qDescriptorFacts l 1 := by unfold qDescriptorFacts; exact List.mem_map_of_mem (by simp)
    have hQ := holds_mem hFacts.2 hMem
    simpa only [Nat.not_lt_zero, ↓reduceIte] using hQ
  · intro i hI
    omega

/-- The retained K word and instruction descriptor shared by both opening QK packets. -/
def secondQKRootFacts (l : Launch) : List (Nat × Value) :=
  [(2564,b32 (firstKLow l)),(9632,b32 0x8200490),(2535,b32 l.sharedBase)]

/-- The first packet leaves query registers in the low bank for the second packet to retarget. -/
def secondQKCommonOperands (l : Launch) : List (Nat × Value) :=
  secondQKRootFacts l ++ qDescriptorFacts l 0

private theorem holdsQDescriptorFacts {l : Launch} {regs : Nat → Option Value}
    (stage : Fin 2) (h : ∀ i : Fin 8, regs (9624+i.val) =
      some (b64 (sharedDescriptorWord (qStart l stage+qkFragment i) 16))) :
    Holds regs (qDescriptorFacts l stage) := by
  unfold qDescriptorFacts
  generalize List.finRange 8 = fs
  induction fs with
  | nil => trivial
  | cons i rest ih => exact ⟨h i,ih⟩

private theorem firstAssemblyIssue {l : Launch} {g : Nat} {lead : Bool} {s : TState}
    (hs : FirstQKAssembly l 8 lead s) :
    ∃ u, run kernel Assumptions.all l g 1 s = some u ∧
      At u 2197 [(9636, .pred lead), (1188, b32 (l.sharedBase + 80)),
        (2562, b32 (l.sharedBase + 8))] ∧
      Holds u.regs (secondQKCommonOperands l) ∧
      (lead = true → ∀ i, Holds u.regs (qkIssueFacts l 0 i 0)) := by
  have hSeg : Seg kernel [] l g 1 2196 [(2536, b32 0)] 2197 [(9637, .pred false)] := by
    intro t ht
    seg_fp ht using rfl
  have hAt : At s 2196 [(2536, b32 0)] := hs.atStep.mono ⟨hs.atStep.2.2.2.2.2.2.2.2.2.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := hSeg s hAt
  have hRun := localRun (by decide) (by decide) hAt.1 rfl hu
  have hStep : Tau kernel [] l g s u := by
    apply tauStep_iff.mp
    unfold run at hu
    cases h : tauStep kernel [] l g s <;> simp_all [run]
  have hc := Flow.code_2196
  rw [← hAt.1] at hc
  have hKeep (r : Nat) (hr : r ≠ 9637) : u.regs r = s.regs r :=
    tau_core_regs hc hStep (by simpa [writesRegs] using hr)
  have hF := hs.atStep.2.2.2.2
  have hG := (hKeep 9636 (by decide)).trans hF.2.2.2.2.1
  have hS := (hKeep 1188 (by decide)).trans hF.2.2.2.2.2.2.1
  have hQ := (hKeep 2562 (by decide)).trans hF.2.2.2.2.2.2.2.1
  refine ⟨u, hRun, hU.mono ⟨hG, hS, hQ, trivial⟩, ?_, ?_⟩
  · apply (holds_append ..).mpr
    constructor
    · unfold secondQKRootFacts
      exact ⟨(hKeep 2564 (by decide)).trans hF.2.2.2.2.2.2.2.2.1,
        (hKeep 9632 (by decide)).trans hF.2.2.1,
        (hKeep 2535 (by decide)).trans hF.2.2.2.2.2.2.2.2.2.1,trivial⟩
    · apply holdsQDescriptorFacts
      intro j
      rw [hKeep _ (by have := j.isLt; omega)]
      simpa only [ite_eq_left j.isLt] using hs.q j
  intro hLead i
  have hD := (hKeep 9638 (by decide)).trans hF.2.2.2.1
  have hId := (hKeep 9632 (by decide)).trans hF.2.2.1
  have hQa : u.regs (9624 + i.val) = some
      (b64 (sharedDescriptorWord (qStart l 0 + qkFragment i) 16)) := by
    rw [hKeep _ (by have := i.isLt; omega)]
    simpa only [ite_eq_left i.isLt] using hs.q i
  have hKb := (hKeep (9644 + i.val) (by omega)).trans (hs.k i i.isLt)
  exact ⟨by simpa only [hLead, qkGuard] using hG, hD, hQa, hKb, hId, trivial⟩

/-- The opening descriptor assembly advances both the selected lane and inactive peers. -/
theorem firstQKAssemblyAtIssueWithRemainder {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {lead : Bool}
    (hs : At s 2154 ((9636,.pred lead) :: firstQKInputFacts l)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 2197 [(9636,.pred lead),(1188,b32 (l.sharedBase+80)),(2562,b32 (l.sharedBase+8))] ∧
      Holds u.regs (secondQKCommonOperands l) ∧
      (lead = true → ∀ i, Holds u.regs (qkIssueFacts l 0 i 0)) := by
  obtain ⟨t,hT,ht⟩ := firstAssemblyStart (g := g) hs
  obtain ⟨v,hV,hv⟩ := firstAssemblyAll hp g ht 8 (by decide)
  obtain ⟨u,hU,hu,hRest,hWords⟩ := firstAssemblyIssue hv
  exact ⟨u,run_rtg (run_comp (run_comp hT hV) hU),hu,hRest,hWords⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
