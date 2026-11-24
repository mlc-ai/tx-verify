-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorCompletion
public import Lemmas.Tcgen05.TcMmaSource
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTmemAddress
import Lemmas.Flow.TcStBytes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.Flow PTX.EventFrame PTX.Assumption PTX.TcMma Thread

/-- Every decoded store writes full 32-bit words, including stores prepared by the delayed
implicit wait. This holds regardless of the stored number. -/
theorem tensorStoreHasWords {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {addr : Nat}
    {words : List Value} {sh : TcShape} (hSt : X.TSt i addr words sh) :
    ∀ v ∈ words, v.bytes = 4 := by
  obtain ⟨pc,he⟩ := hSt
  have hShape : sh = .s32x32b := by
    rcases Thread.tensorStoreSite hX he with ⟨round,q,rfl⟩ | ⟨stage,chunk,rfl⟩
    · obtain ⟨_,_,_,_,hShape⟩ := Thread.Scores.probabilityStoreAddress hp hX round q he
      exact hShape
    · exact (Correction.rescaleStoreActualAddress hp hX stage chunk he).2.1
  rcases get_source hX he with ⟨_,hf⟩ | ⟨_,_,_,_,_,hFires⟩
  · cases hf
  exact fires_tcSt_bytes hFires rfl (by rw [hShape]; intro _ hf; cases hf)

private theorem mmaEvalIsF32 {d : TcMma.Descriptor} (hk : d.kind = .f16 .bf16 .f32)
    {acc : Bool} {a b : List (Option Byte)} {old : Option Value}
    {row col : Nat} {v : Value}
    (he : TcMma.eval Assumptions.all d acc a b old row col = .ok v) :
    ∃ r : ℝ, v = .float .f32 r := by
  have hm : d.kind ∈ Assumptions.arithScope.mma := by rw [hk]; exact List.mem_cons_self
  have hRule : Assumptions.idealArith.mmaRule d acc a b old row col =
      some (Assumption.execIdealMma d acc a b old row col) := by
    simp [Assumptions.idealArith,Assumption.idealReal,hm]
  rw [show TcMma.eval Assumptions.all d acc a b old row col =
      Assumption.execIdealMma d acc a b old row col by
    simp only [TcMma.eval,hk,Assumptions.all,Assumptions.numeric,List.cons_append,
      List.findSome?,hRule,Option.getD_some]] at he
  rw [Assumption.execIdealMma,hk] at he
  simp only [pure,Except.pure,bind,Except.bind] at he
  repeat' first
    | contradiction
    | exact ⟨_, (Except.ok.inj he).symm⟩
    | split at he

/-- A defined MMA result is a finite FP32 value for this kernel's decoded arithmetic. -/
theorem mmaResultIsF32 {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {source : EvId} {cell : Cell} {v : Value}
    (hResult : Result l Assumptions.all X source cell v) :
    ∃ r : ℝ, v = .float .f32 r := by
  cases hResult with
  | overwrite hIssue _ _ hEval | accumulate hIssue _ _ _ _ hEval
  | accumulateStored hIssue _ _ _ _ hEval =>
    exact mmaEvalIsF32 (mmaBf16Arithmetic hp hX hIssue).1 hEval

/-- Any actual Tensor Memory write with a defined value leaves a full word in its cell. -/
theorem tensorWroteWordBytes {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {source : EvId} {cell : Cell} {v : Value}
    (hw : Wrote l Assumptions.all X source cell v) : v.bytes = 4 := by
  rcases hw with hMma | hStore | hCopy | hShift
  · obtain ⟨_,rfl⟩ := mmaResultIsF32 hp hX hMma
    rfl
  · obtain ⟨addr,vals,sh,index,hStore,hVal,_⟩ := hStore
    have hMem := List.mem_of_getElem? hVal
    exact tensorStoreHasWords hp hX hStore v hMem
  · obtain ⟨_,_,_,_,_,_,_,hCopy,_⟩ := hCopy
    exact (noTensorCopyOperandIssue hX hCopy).elim
  · obtain ⟨_,_,⟨⟨_,hShift,_⟩,_,_,_⟩,_⟩ := hShift
    exact (noTensorShiftIssue hX hShift).elim

end PTX.Kernels.TmlFa4Fwd.Safety
