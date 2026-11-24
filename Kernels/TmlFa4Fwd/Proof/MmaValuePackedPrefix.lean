-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaValuePackedTrace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue

noncomputable section

/-- The V source, local low/high words, and warp state used by a PV fragment group.
The fragment election predicate is immaterial to the packing instructions. -/
def packedValueCarry (l : Launch) (block : Fin 4) (use : Nat) : List (Nat × Value) :=
  [((pvSite block).b-3,b32 (valueDescriptorLow l use)),
   ((pvSite block).b-1,b32 0x40004040), ((pvSrcRegs block).2.2,b32 (valueDescriptorLow l use)),
   (1062,b32 12), ((pvSite block).id,b32 0x8210490)]

/-- The descriptor frame at the exact decoded fragment to which the local pack advances. -/
def packedValueFrame (l : Launch) (block : Fin 4) (use : Nat) (step : Fin 8) :
    List (Nat × Value) :=
  ((pvSite block).b,b64 (pvLow l use step+2^32*0x40004040)) ::
    (if step.val = 0 then [] else [((pvSite block).b-2,b32 (pvLow l use step))]) ++
    packedValueCarry l block use

private theorem frameFresh (l : Launch) (block : Fin 4) (use : Nat) :
    ∀ pair ∈ packedValueCarry l block use,
      pair.1 ≠ (pvSite block).b-2 ∧ pair.1 ≠ (pvSite block).b := by
  intro pair mem
  simp only [packedValueCarry,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl <;> fin_cases block <;> exact of_decide_eq_true rfl

private theorem frameShape {l : Launch} {block : Fin 4} {use : Nat} {step : Fin 8}
    {s : TState} (h : At s (pvPc block step) (packedValueFrame l block use step)) :
    RoleShape s ∧ s.regs 1062 = some (b32 12) := by
  refine ⟨⟨h.2.1.symm ▸ by decide,h.2.2.1,fun _ => h.2.1⟩,?_⟩
  apply holds_mem h.2.2.2.2
  simp [packedValueFrame,packedValueCarry]

private theorem cleanBeforeFragment {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {e : Event}
    (hw : Walk kernel Assumptions.all l g s es vs) (he : e ∈ es)
    (hNotUb : ∀ f, e.kind ≠ .ub f) : s.fault = none := by
  cases h : s.fault with
  | none => rfl
  | some fault =>
    have hOut : out kernel Assumptions.all l g s = .ev (.ub fault) := by simp [out,h]
    cases hw with
    | stop => cases he
    | tau ht _ => rw [Tau,hOut] at ht; cases ht
    | ev hv _ =>
      obtain ⟨tm,hm,hf⟩ := hv
      obtain rfl := Out.ev.inj (hm.symm.trans hOut)
      cases hf.2
    | last hv =>
      obtain rfl := List.mem_singleton.mp he
      obtain ⟨tm,hm,hf⟩ := hv
      obtain rfl := Out.ev.inj (hm.symm.trans hOut)
      exact (hNotUb fault (congrArg Event.kind hf.1)).elim

private theorem firstPackedVisit {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (block : Fin 4) (use : Nat) {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit}
    (hs : At s (pvPc block 0-4)
      [((pvSrcRegs block).2.2,b32 (valueDescriptorLow l use)),(1062,b32 12),
        ((pvSite block).id,b32 0x8210490)])
    (hw : Walk kernel Assumptions.all l g s es vs)
    {e : Event} (hEvent : e ∈ es) (hLate : pvPc block 0 ≤ e.pc)
    (hNotUb : ∀ f, e.kind ≠ .ub f) :
    ∃ u pre tail post, es = pre++tail ∧ post.length < vs.length ∧
      At u (pvPc block 0) (packedValueFrame l block use 0) ∧
      Walk kernel Assumptions.all l g u tail post ∧ e ∈ tail ∧
      ∀ ev ∈ pre, pvPc block 0 - 4 ≤ ev.pc ∧ ev.pc < pvPc block 0 := by
  let start := pvPc block 0-4
  let finish := pvPc block 0
  let inputs := [((pvSrcRegs block).2.2,b32 (valueDescriptorLow l use)),(1062,b32 12),
    ((pvSite block).id,b32 0x8210490)]
  have hz := valueFirstPackedWord hp g block use
  obtain ⟨v,hRun,hv⟩ := hz s (hs.mono ⟨hs.2.2.2.2.1,trivial⟩)
  have hStart : 1904 ≤ start := by fin_cases block <;> decide
  have hEnd : start+3 ≤ 2768 := by fin_cases block <;> decide
  have hFlow : ((kernel.code.drop start).take 2).all
      (fun i => schedulerFallsThrough i.op) = true := by
    fin_cases block <;> set_option maxRecDepth 100000 in kernel_rfl
  have hLocal := localRun hStart hEnd hs.1 hFlow hRun
  rcases advanceWalkLocals hLocal hw with rfl | ⟨vVisits,hCount,_,hVWalk⟩
  · cases hEvent
  have hFrame : ((kernel.code.drop start).take 3).all (fun i =>
      (inputs.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
    fin_cases block <;> set_option maxRecDepth 100000 in kernel_rfl
  have hInputs : Holds v.regs inputs := by
    apply holdsSchedulerFrame hs.2.2.2.2
    · intro r hr
      exact schedulerLocalFrame hFrame hFlow hRun hs.1.ge
        (by rw [hs.1]) hr
    · intro pair hm
      exact List.mem_map_of_mem hm
  have h0 : sharedDescriptorWord (kvStart l use) 16384 =
      pvLow l use 0+2^32*0x40004040 := rfl
  have hRegs : Holds v.regs (packedValueFrame l block use 0) := by
    have hOld := hv.2.2.2.2
    rw [h0] at hOld
    exact ⟨hOld.1,hOld.2.1,hOld.2.2.1,hInputs.1,hInputs.2⟩
  let lo := finish-1
  have hI : 1907 ≤ lo ∧ finish < 2768 := by fin_cases block <;> decide
  have hAudit : ((kernel.code.drop lo).take (finish-lo)).all
      (pvCutCode lo finish ((packedValueFrame l block use 0).map Prod.fst)) = true := by
    fin_cases block <;> set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨u,pre,tail,post,hSplit,hPc,hShape,hNew,hUWalk,hFound,hLen,hEarlier⟩ :=
    pvWalkCutLengthRanged hI.1 hI.2 hAudit hVWalk
      (by rw [hv.1]; change lo ≤ lo ∧ lo ≤ finish; omega)
      ⟨⟨hv.2.1.symm ▸ by decide,hv.2.2.1,fun _ => hv.2.1⟩,hInputs.2.1⟩
      hRegs hEvent hLate
  have hSub : 1909 < finish := by fin_cases block <;> decide
  refine ⟨u,pre,tail,post,hSplit,by omega,⟨hPc,hShape.1.2.2 (by omega),hShape.1.2.1,
    cleanBeforeFragment hUWalk hFound hNotUb,hNew⟩,hUWalk,hFound,?_⟩
  intro e he
  obtain ⟨hLower, hUpper⟩ := hEarlier e he
  change finish - 4 ≤ e.pc ∧ e.pc < finish
  change finish - 1 ≤ e.pc at hLower
  omega

private theorem lowWordAdvance (l : Launch) (use : Nat) (step : Fin 7) :
    let old := if step.val < 5 then valueDescriptorLow l use else pvLow l use (pvPrev step)
    old + pvAdvanceLowOffset step = pvLow l use (pvNext step) := by
  fin_cases step <;> rfl

private theorem packedFragmentVisit {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (block : Fin 4) (use : Nat) (step : Fin 7) {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit}
    (hs : At s (pvPc block (pvPrev step)) (packedValueFrame l block use (pvPrev step)))
    (hw : Walk kernel Assumptions.all l g s es vs)
    {e : Event} (hEvent : e ∈ es) (hLate : pvPc block (pvNext step) ≤ e.pc) :
    ∃ u pre tail post, es = pre++tail ∧ post.length ≤ vs.length ∧
      At u (pvPc block (pvNext step)) (packedValueFrame l block use (pvNext step)) ∧
      Walk kernel Assumptions.all l g u tail post ∧ e ∈ tail ∧
      ∀ ev ∈ pre, pvPc block (pvPrev step) ≤ ev.pc ∧ ev.pc < pvPc block (pvNext step) := by
  let site := pvSite block
  let lo := pvPc block (pvPrev step)
  let hi := pvAdvancePc block step-2
  let finish := pvPc block (pvNext step)
  let F := packedValueFrame l block use (pvPrev step)
  have hBounds : 1907 ≤ lo ∧ lo ≤ hi ∧ hi < finish ∧ finish < 2768 := by
    fin_cases block <;> fin_cases step <;> decide
  have hLast : pvAdvancePc block step = finish := by fin_cases block <;> fin_cases step <;> decide
  have hAudit : ((kernel.code.drop lo).take (hi-lo)).all (pvCutCode lo hi (F.map Prod.fst)) =
      true := by fin_cases block <;> fin_cases step <;> set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨v,pre,tail,visits,hSplit,hPc,hShape,hRegs,hWalk,hRemain,hLen,hPrior⟩ :=
    pvWalkCutLengthRanged hBounds.1 (by omega) hAudit hw (show lo ≤ s.pc ∧ s.pc ≤ hi by
      rw [hs.1]; exact ⟨le_rfl,hBounds.2.1⟩) (frameShape hs) hs.2.2.2.2 hEvent (by omega)
  have hSub : 1909 < hi := by fin_cases block <;> fin_cases step <;> decide
  have hv : At v hi F :=
    ⟨hPc,hShape.1.2.2 (by omega),hShape.1.2.1,
      normalBeforeLaterEvent hWalk hRemain (by omega),hRegs⟩
  let old := if step.val < 5 then valueDescriptorLow l use else pvLow l use (pvPrev step)
  have hLow := lowWordAdvance l use step
  have hWord : old+pvAdvanceLowOffset step < 2^32 := by
    rw [hLow]
    have hLimit := hp.shared.2.1
    have hSlot : kvSlot use < 3 := Nat.mod_lt _ (by decide)
    have hIndex := (pvNext step).isLt
    unfold pvLow kvStart
    omega
  have hSrc : (pvAdvanceLowSrc block step,b32 old) ∈ F := by
    by_cases h : step.val < 5
    · simp [F,packedValueFrame,packedValueCarry,pvAdvanceLowSrc,old,h]
    · have hNonzero : (pvPrev step).val ≠ 0 := by change step.val ≠ 0; omega
      simp [F,packedValueFrame,pvAdvanceLowSrc,old,h,hNonzero]
  have hHigh : (site.b-1,b32 0x40004040) ∈ F := by
    simp [F,packedValueFrame,packedValueCarry,site]
  have hCarry : Holds v.regs (packedValueCarry l block use) :=
    (holds_append ..).mp hRegs.2 |>.2
  obtain ⟨u,hRun,hu⟩ := pvNextDescriptorFramed l g block step hWord (frameFresh l block use) v
    (hv.mono ⟨holds_mem hRegs hSrc,holds_mem hRegs hHigh,hCarry⟩)
  rcases advanceWalkLocals hRun hWalk with rfl | ⟨post,hCount,_,hUWalk⟩
  · cases hRemain
  have hu' : At u finish (packedValueFrame l block use (pvNext step)) := by
    rw [← hLast]
    apply hu.mono
    have hn : (pvNext step).val ≠ 0 := Nat.succ_ne_zero _
    simp only [packedValueFrame,hn,↓reduceIte]
    have hHeld := hu.2.2.2.2
    rw [hLow] at hHeld
    exact ⟨hHeld.2.1,hHeld.1,hHeld.2.2⟩
  exact ⟨u,pre,tail,post,hSplit,by omega,hu',hUWalk,hRemain,
    fun ev hm => ⟨(hPrior ev hm).1, (hPrior ev hm).2.trans hBounds.2.2.1⟩⟩

private theorem packedFragmentProgress (block : Fin 4) (gap : Fin 7) :
    pvPc block (pvPrev gap) < pvPc block (pvNext gap) := by
  fin_cases block <;> fin_cases gap <;> decide

private theorem packedVisitTo {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (block : Fin 4) (use : Nat) (step : Fin 8) {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit}
    (hs : At s (pvPc block 0) (packedValueFrame l block use 0))
    (hw : Walk kernel Assumptions.all l g s es vs)
    {e : Event} (he : e ∈ es) (hLate : pvPc block step ≤ e.pc) :
    ∃ u pre tail post, es = pre++tail ∧ post.length ≤ vs.length ∧
      At u (pvPc block step) (packedValueFrame l block use step) ∧
      Walk kernel Assumptions.all l g u tail post ∧ e ∈ tail ∧
      ∀ ev ∈ pre, pvPc block 0 ≤ ev.pc ∧ ev.pc < pvPc block step := by
  obtain ⟨n,hN⟩ := step
  induction n with
  | zero => exact ⟨s,[],es,vs,rfl,le_rfl,hs,hw,he,by simp⟩
  | succ n ih =>
    let gap : Fin 7 := ⟨n,by omega⟩
    have hStepPc := packedFragmentProgress block gap
    have hLate' : pvPc block (pvNext gap) ≤ e.pc := hLate
    obtain ⟨v,pre,rest,visits,hSplit,hLen,hv,hWalk,hMem,hBefore⟩ :=
      ih (by omega) (hStepPc.le.trans hLate')
    obtain ⟨u,skip,tail,post,hPieces,hCount,hu,hTail,hRest,hEarly⟩ :=
      packedFragmentVisit hp block use gap hv hWalk hMem hLate'
    refine ⟨u,pre++skip,tail,post,by simp [hSplit,hPieces,List.append_assoc],
      by omega,hu,hTail,hRest,?_⟩
    intro ev hm
    rcases List.mem_append.mp hm with h | h
    · exact ⟨(hBefore ev h).1, (hBefore ev h).2.trans hStepPc⟩
    · have hFloor : pvPc block 0 ≤ pvPc block (pvPrev gap) := by
        change pvPc block 0 ≤ pvPc block ⟨n, _⟩
        simp only [pvPc, Fin.val_zero]
        split <;> omega
      exact ⟨hFloor.trans (hEarly ev h).1, (hEarly ev h).2⟩

/-- The instruction descriptor immediately precedes the three source and operand moves. -/
def valueIdSite (block : Fin 4) : Nat := pvPc block 0-7

private theorem setValueId (l : Launch) (g : Nat) (block : Fin 4) (use : Nat) :
    Seg kernel [] l g 1 (valueIdSite block)
      [((pvSrcRegs block).2.2,b32 (valueDescriptorLow l use)),(1062,b32 12)]
      (valueIdSite block+1)
      [((pvSrcRegs block).2.2,b32 (valueDescriptorLow l use)),(1062,b32 12),
        ((pvSite block).id,b32 0x8210490)] := by
  fin_cases block <;> intro t ht <;> seg_fp ht using rfl

private theorem idSetupVisit {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (block : Fin 4) (use : Nat)
    (hs : At s (valueIdSite block)
      [((pvSrcRegs block).2.2,b32 (valueDescriptorLow l use)),(1062,b32 12)])
    (hw : Walk kernel Assumptions.all l g s es vs)
    {e : Event} (he : e ∈ es) (hLate : pvPc block 0 ≤ e.pc) :
    ∃ u pre tail post, es = pre++tail ∧ post.length ≤ vs.length ∧
      At u (pvPc block 0-4)
        [((pvSrcRegs block).2.2,b32 (valueDescriptorLow l use)),(1062,b32 12),
          ((pvSite block).id,b32 0x8210490)] ∧
      Walk kernel Assumptions.all l g u tail post ∧ e ∈ tail ∧
      ∀ ev ∈ pre, valueIdSite block ≤ ev.pc ∧ ev.pc < pvPc block 0 := by
  let start := valueIdSite block
  let finish := pvPc block 0-4
  let F := [((pvSrcRegs block).2.2,b32 (valueDescriptorLow l use)),(1062,b32 12),
    ((pvSite block).id,b32 0x8210490)]
  have hBounds : 1909 < start ∧ start+1 ≤ finish ∧ finish < pvPc block 0 ∧
      pvPc block 0 < 2768 := by fin_cases block <;> decide
  obtain ⟨v,hLocal,hv⟩ := setValueId l g block use s hs
  have hr := localRun (show 1904 ≤ start by omega) (show start+1 ≤ 2768 by omega)
    hs.1 rfl hLocal
  rcases advanceWalkLocals hr hw with rfl | ⟨vVisits,hCount,_,hWalk⟩
  · cases he
  have hAudit : ((kernel.code.drop (start+1)).take (finish-(start+1))).all
      (pvCutCode (start+1) finish (F.map Prod.fst)) = true := by
    fin_cases block <;> set_option maxRecDepth 100000 in kernel_rfl
  have hv' : At v (start+1) F := hv
  have hShape : RoleShape v ∧ v.regs 1062 = some (b32 12) :=
    ⟨⟨hv'.2.1.symm ▸ by decide,hv'.2.2.1,fun _ => hv'.2.1⟩,hv'.2.2.2.2.2.1⟩
  obtain ⟨u,pre,tail,post,hSplit,hPc,hu,hRegs,hAfter,hFound,hLen,hEarlier⟩ :=
    pvWalkCutLengthRanged (show 1907 ≤ start+1 by omega) (show finish < 2768 by omega)
      hAudit hWalk (show start+1 ≤ v.pc ∧ v.pc ≤ finish by rw [hv'.1]; omega)
      hShape hv'.2.2.2.2 he (show finish ≤ e.pc by omega)
  exact ⟨u,pre,tail,post,hSplit,by omega,⟨hPc,hu.1.2.2 (by omega),hu.1.2.1,
    normalBeforeLaterEvent hAfter hFound (by omega),hRegs⟩,hAfter,hFound,
    fun ev hm => ⟨by have := (hEarlier ev hm).1; omega,
      (hEarlier ev hm).2.trans hBounds.2.2.1⟩⟩

variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (block : Fin 4) (use : Nat)
    (step : Fin 8) {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s (valueIdSite block)
      [((pvSrcRegs block).2.2,b32 (valueDescriptorLow l use)),(1062,b32 12)])
    (hw : Walk kernel Assumptions.all l g s es vs) {e : Event} (he : e ∈ es)
include hp block use step hs hw he

/-- Replay the actual local B assembly, including each intervening poll. No issue
predicate is needed because all descriptor writes execute on every visiting lane. -/
theorem valuePackedPrefixRanged (hLate : pvPc block step ≤ e.pc) (hNotUb : ∀ f, e.kind ≠ .ub f) :
    ∃ u pre tail post, es = pre++tail ∧ post.length < vs.length ∧
      At u (pvPc block step) (packedValueFrame l block use step) ∧
      Walk kernel Assumptions.all l g u tail post ∧ e ∈ tail ∧
      ∀ ev ∈ pre, valueIdSite block ≤ ev.pc ∧ ev.pc < pvPc block step := by
  have hBegin : pvPc block 0 ≤ pvPc block step := by fin_cases block <;> fin_cases step <;> decide
  obtain ⟨w,setup,remaining,initial,hEntry,hCount0,hw',hsWalk,hRemain,hEarlySetup⟩ :=
    idSetupVisit block use hs hw he (hBegin.trans hLate)
  obtain ⟨v,pre,rest,visits,hSplit,hLen,hv,hWalk,hFound,hBefore⟩ :=
    firstPackedVisit hp block use hw' hsWalk hRemain (hBegin.trans hLate) hNotUb
  obtain ⟨u,gap,tail,post,hPieces,hCount,hu,hTail,hRemain,hEarly⟩ :=
    packedVisitTo hp block use step hv hWalk hFound hLate
  refine ⟨u,setup++pre++gap,tail,post,by simp [hEntry,hSplit,hPieces,List.append_assoc],
    by omega,hu,hTail,hRemain,?_⟩
  intro ev hm
  have hLo : valueIdSite block ≤ pvPc block 0 - 4 := by unfold valueIdSite; omega
  rcases List.mem_append.mp hm with h | h
  · rcases List.mem_append.mp h with h | h
    · exact ⟨(hEarlySetup ev h).1, (hEarlySetup ev h).2.trans_le hBegin⟩
    · exact ⟨hLo.trans (hBefore ev h).1, (hBefore ev h).2.trans_le hBegin⟩
  · exact ⟨(hLo.trans (Nat.sub_le ..)).trans (hEarly ev h).1, (hEarly ev h).2⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
