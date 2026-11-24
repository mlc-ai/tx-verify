-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasStageAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxRecordedEntry
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part081
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Softmax PTX.Kernels.TmlFa4Fwd.Correction

private theorem biasReturnStep {l : Launch} {g : Nat} {s t : TState}
    (hLo : 5184 ≤ s.pc) (hHi : s.pc ≤ 5189) (hStep : Tau kernel Assumptions.all l g s t) :
    t.pc = s.pc+1 ∧ t.pc ≤ 5189 := by
  have hEnd : s.pc ≠ 5189 := by
    intro hPc
    unfold Tau at hStep
    cases hf : s.fault with
    | none => rw [out_event hf (hPc.symm ▸ Flow.code_5189) rfl rfl] at hStep; cases hStep
    | some f => simp [out,hf] at hStep
  have hCode : ∃ i, kernel.code[s.pc]? = some i ∧ Assumptions.coreOp i.op = true ∧
      nextPc i.op s.pc = s.pc+1 ∧ (∀ pc, ¬ BrxTarget i.op pc) := by
    interval_cases h : s.pc
    · exact ⟨_,Flow.code_5184,rfl,rfl,fun _ => nofun⟩
    · exact ⟨_,Flow.code_5185,rfl,rfl,fun _ => nofun⟩
    · exact ⟨_,Flow.code_5186,rfl,rfl,fun _ => nofun⟩
    · exact ⟨_,Flow.code_5187,rfl,rfl,fun _ => nofun⟩
    · exact ⟨_,Flow.code_5188,rfl,rfl,fun _ => nofun⟩
    · exact (hEnd rfl).elim
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by
    simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false]
    omega
  obtain ⟨i,hGet,hCore,hNext,hBranch⟩ := hCode
  have hNil : Tau kernel [] l g s t := by
    exact tauStep_iff.mp ((Assumptions.tauStep_all_eq_nil hOff hGet hCore) ▸
      tauStep_iff.mpr hStep)
  rcases tau_core_frame hGet hNil with rfl | hFrame
  · exact ⟨rfl,by change s.pc+1 ≤ 5189; omega⟩
  · have hPc := hFrame.pc.elim (·.trans hNext) (fun h => (hBranch _ h).elim)
    exact ⟨hPc,by omega⟩

private theorem biasReturnCheckpointUnique {l : Launch} {g : Nat} {s t : TState}
    (hS : s.pc = 5184) (hT : t.pc = 5184)
    (hPath : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t) : s = t := by
  have hWindow : (5184 ≤ t.pc ∧ t.pc ≤ 5189) ∧ (s = t ∨ s.pc < t.pc) := by
    clear hT
    induction hPath with
    | refl => exact ⟨by omega,.inl rfl⟩
    | tail hPast hStep ih =>
      obtain ⟨hPc,hBound⟩ := biasReturnStep ih.1.1 ih.1.2 hStep
      refine ⟨⟨by omega,hBound⟩,.inr ?_⟩
      rcases ih.2 with rfl | hLt <;> omega
  exact hWindow.2.elim id (fun h => (by omega : False).elim)

/-- The resident Bias coordinates and inverse scale are already in the
actual returned acquire state, including when its poll is the final event. -/
theorem repeatedBiasGeometryOfAcquire
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j phase : Nat} (w : Fin 8) (hWarp : w.val = Prologue.warpIndex l g)
    {F : List (Nat × Value)} (cursor : OpeningTripCursor l X g 5184 F)
    {obj : Loc} {acq : Bool} {scope : MbarScope}
    (he : X.get (g,j) = some ⟨5181,.wait obj phase true acq scope⟩)
    (hPos : cursor.pos = j+1) :
    Holds cursor.ready.regs (biasFenceFacts l g w true) ∧
    cursor.ready.regs 7896 = some (joinValue (b32 p.invScaleBits) (b32 p.invScaleBits)) ∧
    cursor.ready.regs 3976 = some (b32 (repeatedBiasRowBase l g)) ∧
    cursor.ready.regs 3977 = some (b32 (repeatedBiasStageOffset w)) ∧
    ∀ i : Fin 14, cursor.ready.regs (3982+4*i.val) = some (b32 (kvSwizzle
      (repeatedBiasRowBase l g+repeatedBiasStageOffset w+repeatedVectorDisplacement i))) := by
  obtain ⟨other,hOther,pos,seed,ending,hBefore,hSeed,hPrefix,hRunEntry⟩ :=
    softmaxRoleEntryRecorded hp hX he (by change 173 < 5181; decide)
      (by change 5181 ≠ 3102; decide) (hWarp ▸ w.isLt)
  have hwEq : other = w := Fin.ext (hOther.trans hWarp.symm)
  subst other
  obtain ⟨t,u,_,hStep,_,hBranch,hU,_,hReach⟩ :=
    repeatedBiasAcquireBranchFromEntry hp w hSeed hRunEntry hBefore he
  have hPre : TraceReach kernel Assumptions.all l g {} ((X.tr g).take j) t := by
    have eq : j = pos+(j-pos) := by omega
    rw [eq,List.take_add]
    simpa only [Nat.add_sub_cancel_left] using hPrefix.append hReach
  obtain ⟨previous,hRecorded,hLocal⟩ := hPre.returnedPrefix
  have hGet : (X.tr g)[j]? = some ⟨5181,.wait obj phase true acq scope⟩ := he
  have hRecordReturn : Run kernel Assumptions.all l g {} ((X.tr g).take (j+1))
      (some (next (setReg t 9755 (.pred true)))) := by
    rw [List.take_add_one,hGet]
    exact hRecorded.snoc hLocal hStep
  have hCursorRun : Run kernel Assumptions.all l g {} ((X.tr g).take (j+1))
      (some cursor.before) := by simpa only [hPos] using cursor.recorded
  have hSame : cursor.before = next (setReg t 9755 (.pred true)) :=
    Option.some.inj (hCursorRun.det hRecordReturn)
  have hU' : u.pc = 5184 := hU.1
  have hReady : cursor.ready = u := by
    rcases rtg_tau_total (hSame ▸ cursor.localSteps) (run_rtg hBranch) with hGo | hBack
    · exact biasReturnCheckpointUnique cursor.checkpoint.1 hU' hGo
    · exact (biasReturnCheckpointUnique hU' cursor.checkpoint.1 hBack).symm
  rw [hReady]
  have hUFacts := (holds_append _ _ _).mp hU.2.2.2.2
  have hFence := ((holds_append _ _ _).mp hUFacts.1).1
  have hRow := ((holds_append _ _ _).mp hUFacts.1).2
  exact ⟨hFence.2,hFence.1,hRow.1,hRow.2.1,
    fun i => holds_mem hUFacts.2 (show (3982+4*i.val,_) ∈ repeatedBiasSavedBases l g w from
      List.mem_map_of_mem (List.mem_finRange i))⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
