-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaValueOperandDecode
public import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

def valueCarry (l : Launch) (block : Fin 4) (use : Nat) : List (Nat × Value) :=
  [((pvSite block).b - 3, b32 (valueDescriptorLow l use)),
    ((pvSite block).b - 1, b32 0x40004040), (1062, b32 12),
    ((pvSite block).guard, .pred true)]

def valuePackedFrame (l : Launch) (block : Fin 4) (use : Nat) (step : Fin 8) :
    List (Nat × Value) :=
  [((pvSite block).b, b64 (pvLow l use step + 2 ^ 32 * 0x40004040))] ++
    ((if step.val = 0 then [] else [((pvSite block).b - 2, b32 (pvLow l use step))]) ++
      valueCarry l block use)

private theorem valueCarryFresh (l : Launch) (block : Fin 4) (use : Nat) :
    ∀ pair ∈ valueCarry l block use,
      pair.1 ≠ (pvSite block).b - 2 ∧ pair.1 ≠ (pvSite block).b := by
  intro pair mem
  simp only [valueCarry, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl <;> fin_cases block <;> exact of_decide_eq_true rfl

/-- The actual path from the first low-word move to the first PV issue preserves
the arithmetic descriptor and the predicate supplied by its election. -/
theorem startValuePackedFrame {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (block : Fin 4) (use : Nat) {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hs : At s (pvPc block 0 - 4)
      [((pvSrcRegs block).2.2, b32 (valueDescriptorLow l use)), (1062, b32 12),
        ((pvSite block).guard, .pred true)]) (hw : Walk kernel Assumptions.all l g s es vs)
    {later : Event} (hLater : later ∈ es) (hAfter : pvPc block 0 < later.pc) :
    ∃ u pre tail post, es = pre ++ tail ∧ At u (pvPc block 0) (valuePackedFrame l block use 0) ∧
      Walk kernel Assumptions.all l g u tail post ∧ later ∈ tail ∧
      ∀ e ∈ pre, e.pc < pvPc block 0 := by
  obtain ⟨v,hRun,hv⟩ := valueFirstPackedWordFramed hp g block use true s hs
  have hStart : 1904 ≤ pvPc block 0 - 4 := by fin_cases block <;> decide
  have hStop : pvPc block 0 - 4 + 3 ≤ 2768 := by fin_cases block <;> decide
  have hStraight : ((kernel.code.drop (pvPc block 0 - 4)).take (3-1)).all
      (fun i => schedulerFallsThrough i.op) = true := by
    fin_cases block <;> set_option maxRecDepth 100000 in kernel_rfl
  have hLocal := localRun hStart hStop hs.1 hStraight hRun
  rcases advanceWalkLocals hLocal hw with rfl | ⟨rem,_,_,hvWalk⟩
  · cases hLater
  let start := pvPc block 0 - 1
  let finish := pvPc block 0
  let F := valuePackedFrame l block use 0
  have hWord : sharedDescriptorWord (kvStart l use) 16384 =
      pvLow l use 0 + 2 ^ 32 * 0x40004040 := rfl
  have hv' : At v start F :=
    hv.mono (by simpa only [F, valuePackedFrame, valueCarry, Fin.val_zero, ↓reduceIte,
      List.singleton_append, List.nil_append, hWord] using hv.2.2.2.2)
  have hvW : RoleShape v ∧ v.regs 1062 = some (b32 12) :=
    ⟨⟨hv.2.1.symm ▸ Nat.zero_le _, hv.2.2.1, fun _ => hv.2.1⟩, hv.2.2.2.2.2.2.2.1⟩
  have hLo : 1907 ≤ start := by fin_cases block <;> decide
  have hHi : finish < 2768 := by fin_cases block <;> decide
  have hAudit : ((kernel.code.drop start).take (finish-start)).all
      (pvCutCode start finish (F.map Prod.fst)) = true := by
    fin_cases block <;> set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨u,pre,tail,post,hSplit,hPc,hShape,hFrame,hUWalk,hTail,hEarlier⟩ :=
    pvWalkCut hLo hHi hAudit hvWalk (show start ≤ v.pc ∧ v.pc ≤ finish by
      rw [hv'.1]
      exact ⟨le_rfl, Nat.sub_le _ _⟩) hvW hv'.2.2.2.2 hLater hAfter.le
  have hf := normalBeforeLaterEvent hUWalk hTail (show u.pc < later.pc by rw [hPc]; exact hAfter)
  exact ⟨u,pre,tail,post,hSplit,⟨hPc,hShape.1.2.2 (by rw [hPc]; fin_cases block <;> decide),
    hShape.1.2.1,hf,hFrame⟩,hUWalk,hTail,hEarlier⟩

/-- The registers encoding V's shared descriptor advance along each actual PV
fragment gap, including the lower-probability acquire between fragments five and six. -/
theorem advanceValuePackedFrame {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (block : Fin 4) (use : Nat) (step : Fin 7) {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hs : At s (pvPc block (pvPrev step))
      (valuePackedFrame l block use (pvPrev step)))
    (hw : Walk kernel Assumptions.all l g s es vs)
    {later : Event} (hLater : later ∈ es) (hAfter : pvPc block (pvNext step) ≤ later.pc) :
    ∃ u pre tail post, es = pre ++ tail ∧
      At u (pvPc block (pvNext step)) (valuePackedFrame l block use (pvNext step)) ∧
      Walk kernel Assumptions.all l g u tail post ∧ later ∈ tail ∧
      ∀ e ∈ pre, e.pc < pvPc block (pvNext step) := by
  let site := pvSite block
  let lo := pvPc block (pvPrev step)
  let hi := pvAdvancePc block step - 2
  let endPc := pvPc block (pvNext step)
  let F := valuePackedFrame l block use (pvPrev step)
  have hBounds : 1909 < lo ∧ lo ≤ hi ∧ hi < endPc ∧ endPc < 2768 := by
    fin_cases block <;> fin_cases step <;> decide
  have hEnd : pvAdvancePc block step = endPc := by fin_cases block <;> fin_cases step <;> decide
  have hAudit : ((kernel.code.drop lo).take (hi-lo)).all
      (pvCutCode lo hi (F.map Prod.fst)) = true := by
    fin_cases block <;> fin_cases step <;> set_option maxRecDepth 100000 in kernel_rfl
  have hWarp : (1062,b32 12) ∈ F := by simp [F, valuePackedFrame, valueCarry]
  have hsShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩, holds_mem hs.2.2.2.2 hWarp⟩
  obtain ⟨v,pre,tail,visits,hSplit,hPc,hShape,hFrame,hVWalk,hVLater,hBefore⟩ :=
    pvWalkCut (show 1907 ≤ lo by omega) (show hi < 2768 by omega) hAudit hw
      (show lo ≤ s.pc ∧ s.pc ≤ hi by rw [hs.1]; exact ⟨le_rfl,hBounds.2.1⟩)
      hsShape hs.2.2.2.2 hLater (show hi ≤ later.pc by omega)
  have hv : At v hi F := ⟨hPc, hShape.1.2.2 (by omega), hShape.1.2.1,
    normalBeforeLaterEvent hVWalk hVLater (by omega), hFrame⟩
  let old := if step.val < 5 then valueDescriptorLow l use else pvLow l use (pvPrev step)
  have hWord : old + pvAdvanceLowOffset step = pvLow l use (pvNext step) := by
    by_cases h : step.val < 5 <;>
      (simp only [old, pvAdvanceLowOffset, valueDescriptorLow, pvLow, pvPrev, pvNext, h, ↓reduceIte]
       try omega)
  have hb : old + pvAdvanceLowOffset step < 2 ^ 32 := by
    rw [hWord]
    have hLimit := hp.shared.2.1
    have hSlot : kvSlot use < 3 := Nat.mod_lt _ (by decide)
    have hIndex := (pvNext step).isLt
    unfold pvLow kvStart
    omega
  have hLo : (pvAdvanceLowSrc block step,b32 old) ∈ F := by
    by_cases h : step.val < 5
    · simp [F, valuePackedFrame, valueCarry, pvAdvanceLowSrc, old, h]
    · have hNonzero : (pvPrev step).val ≠ 0 := by change step.val ≠ 0; omega
      simp [F, valuePackedFrame, pvAdvanceLowSrc, old, h, hNonzero]
  have hHigh : (site.b-1,b32 0x40004040) ∈ F := by simp [F, valuePackedFrame, valueCarry, site]
  have hCarry : Holds v.regs (valueCarry l block use) :=
    (holds_append ..).mp ((holds_append ..).mp hFrame).2 |>.2
  obtain ⟨u,hLocal,hu⟩ :=
    pvNextDescriptorFramed l g block step hb (valueCarryFresh l block use) v
      (hv.mono ⟨holds_mem hFrame hLo,holds_mem hFrame hHigh,hCarry⟩)
  have hu' : At u endPc (valuePackedFrame l block use (pvNext step)) := by
    rw [← hEnd]
    apply hu.mono
    have hn : (pvNext step).val ≠ 0 := Nat.succ_ne_zero _
    simp only [valuePackedFrame, hn, ↓reduceIte, List.singleton_append]
    have hRegs := hu.2.2.2.2
    rw [hWord] at hRegs
    exact ⟨hRegs.2.1,hRegs.1,hRegs.2.2⟩
  rcases advanceWalkLocals hLocal hVWalk with rfl | ⟨post, _, _, hUWalk⟩
  · cases hVLater
  · exact ⟨u,pre,tail,post,hSplit,hu',hUWalk,hVLater,fun e hm => (hBefore e hm).trans hBounds.2.2.1⟩

private theorem valueFragmentPcIncreases (block : Fin 4) (gap : Fin 7) :
    pvPc block (pvPrev gap) < pvPc block (pvNext gap) := by
  fin_cases block <;> fin_cases gap <;> decide

private theorem valuePackedAtFragment {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (block : Fin 4) (use : Nat) {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hs : At s (pvPc block 0) (valuePackedFrame l block use 0))
    (hw : Walk kernel Assumptions.all l g s es vs)
    {later : Event} (hLater : later ∈ es) (hAfter : ∀ step : Fin 8, pvPc block step < later.pc)
    (step : Fin 8) :
    ∃ u pre tail post, es = pre ++ tail ∧
      At u (pvPc block step) (valuePackedFrame l block use step) ∧
      Walk kernel Assumptions.all l g u tail post ∧ later ∈ tail ∧
      ∀ e ∈ pre, e.pc < pvPc block step := by
  obtain ⟨index,hIndex⟩ := step
  induction index with
  | zero => exact ⟨s, [], es, vs, rfl, hs, hw, hLater, by simp⟩
  | succ n ih =>
    let gap : Fin 7 := ⟨n, by omega⟩
    obtain ⟨v,pre,rest,visits,hBefore,hv,hVWalk,hLive,hEarlier⟩ := ih (by omega)
    have hv' : At v (pvPc block (pvPrev gap)) (valuePackedFrame l block use (pvPrev gap)) := hv
    obtain ⟨u,skip,tail,post,hSplit,hu,hUWalk,hTail,hNew⟩ :=
      advanceValuePackedFrame hp block use gap hv' hVWalk hLive (hAfter _).le
    refine ⟨u,pre++skip,tail,post,by simp [hBefore,hSplit,List.append_assoc],hu,hUWalk,hTail,?_⟩
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact (hEarlier e he).trans (valueFragmentPcIncreases block gap)
    · exact hNew e he

/-- A decoded first V word in the post-election frame reaches the B operand of
every actual fragment before the later recorded event. -/
theorem valuePackedIssues {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (block : Fin 4) (use : Nat) {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hs : At s (pvPc block 0 - 4)
      [((pvSrcRegs block).2.2, b32 (valueDescriptorLow l use)), (1062, b32 12),
        ((pvSite block).guard, .pred true)]) (hw : Walk kernel Assumptions.all l g s es vs)
    {later : Event} (hLater : later ∈ es) (hAfter : ∀ step : Fin 8, pvPc block step < later.pc)
    (step : Fin 8) :
    ∃ pre tail dst op accum mask,
      es = pre ++ ⟨pvPc block step,.tc (.mma dst op accum mask)⟩ :: tail ∧
      op.b = sharedDescriptor (kvStart l use + pvFragment step) 16384 ∧ later ∈ tail ∧
      ∀ e ∈ pre, e.pc < pvPc block step := by
  obtain ⟨t,pre,rest,trace,hSplit,ht,hTWalk,hT,hPre⟩ :=
    startValuePackedFrame hp block use hs hw hLater (hAfter 0)
  obtain ⟨u,gap,tail,post,hRem,hu,hUWalk,hU,hGap⟩ :=
    valuePackedAtFragment hp block use ht hTWalk hT hAfter step
  have hGuard : ((pvSite block).guard,.pred true) ∈ valuePackedFrame l block use step := by
    simp [valuePackedFrame,valueCarry]
  have hLead := holds_mem hu.2.2.2.2 hGuard
  have hCode := pvCode block step
  dsimp only at hCode
  rw [← hu.1] at hCode
  have hout := out_event (A := Assumptions.all) (L := l) (g := g) (K := kernel)
    hu.2.2.2.1 hCode
    (by simp [guardHolds,readReg,hLead,bind,Except.bind,pure,Except.pure]) rfl
  obtain ⟨v,e,after,restVisits,hE,_,hStep,hFinal,hFinalMem⟩ :=
    pvWalkEvent hUWalk hout hU (show u.pc < later.pc by rw [hu.1]; exact hAfter step)
  have hWord : sharedDescriptorWord (kvStart l use + pvFragment step) 16384 =
      pvLow l use step + 2 ^ 32 * 0x40004040 := by
    unfold sharedDescriptorWord pvLow pvFragment
    omega
  have hB : u.regs (pvSite block).b =
      some (b64 (sharedDescriptorWord (kvStart l use + pvFragment step) 16384)) := by
    rw [hWord]
    exact hu.2.2.2.2.1
  obtain ⟨dst,op,accum,mask,rfl,hDescriptor⟩ :=
    pvReturningIssueBOfRegister hp block step use hu.1 hB hStep
  refine ⟨pre++gap,after,dst,op,accum,mask,
    by simp [hSplit,hRem,hE,List.append_assoc],hDescriptor,hFinalMem,?_⟩
  intro e he
  rcases List.mem_append.mp he with he | he
  · have hFirst : pvPc block 0 ≤ pvPc block step := by
      fin_cases block <;> fin_cases step <;> decide
    exact (hPre e he).trans_le hFirst
  · exact hGap e he

end
end PTX.Kernels.TmlFa4Fwd.Mma
