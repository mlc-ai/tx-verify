-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionInitialTensorCoverage
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Thread.TensorLoadSites
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Softmax
open _root_.PTX.Kernels.TmlFa4Fwd.Correction

private def isSoftmaxTensorPosition (pc : Nat) (i : Instr) : Bool :=
  decide (3425 ≤ pc ∧ pc < 7601) || !tcDataOp i.op

set_option maxRecDepth 100000 in
private theorem softmaxTensorSourceAudit :
    (((kernel.code.drop 3103).take (7743-3103)).zipIdx 3103).all
      (fun (i,pc) => isSoftmaxTensorPosition pc i) = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem startupWithoutTensorData : (kernel.code.take 174).all (fun i => !tcDataOp i.op) =
    true := by decide +kernel

private theorem hintsWithoutTensorData : registerHintSites.all (fun site =>
    match kernel.code[site]? with
    | some i => !tcDataOp i.op
    | none => false) = true := by decide +kernel

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- All actual softmax Tensor Memory collective events are inside the score and probability body. -/
theorem softmaxTensorCollectiveBand (hX : Consistent l kernel Assumptions.all m X) {g j : Nat}
    (hw : warpIndex l g < 8) {e : Event} (he : X.get (g,j) = some e) (hColl : isTcColl e = true) :
    3425 ≤ e.pc ∧ e.pc < 7601 := by
  have hData := arithmeticTensorCollectiveIsData hp hX (hw.trans (by decide)) he hColl
  rcases get_source hX he with ⟨_,hf⟩ | ⟨_,ins,_,_,hc,hf⟩
  · simp [hf,isTcData] at hData
  have hOp := fires_tcData_op hf hData
  by_cases hStartup : e.pc < 174
  · have hGet : (kernel.code.take 174)[e.pc]? = some ins :=
      (List.getElem?_take_of_lt hStartup).trans hc
    have h := List.all_eq_true.mp startupWithoutTensorData _ (List.mem_of_getElem? hGet)
    simp [hOp] at h
  by_cases hHint : e.pc ∈ registerHintSites
  · have h := List.all_eq_true.mp hintsWithoutTensorData _ hHint
    rw [hc] at h
    simp [hOp] at h
  have hSite := roleBodyPcOfEvent hp hX he (by omega) hHint
  have hSoft : e.pc = 9205 ∨ 3103 ≤ e.pc ∧ e.pc ≤ 7742 := by
    simpa [roleBodyPc,show ¬ 14 ≤ warpIndex l g by omega,show warpIndex l g ≠ 13 by omega,
      show warpIndex l g ≠ 12 by omega,hw] using hSite
  rcases hSoft with hExit | ⟨hLo,hHi⟩
  · rw [hExit,Flow.code_9205] at hc
    obtain rfl := Option.some.inj hc
    cases hOp
  · have hGet : (((kernel.code.drop 3103).take (7743-3103)).zipIdx 3103)[e.pc-3103]? =
        some (ins,e.pc) := by
      rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
        Nat.add_sub_of_le hLo,hc]
      rfl
    have h := List.all_eq_true.mp softmaxTensorSourceAudit _ (List.mem_of_getElem? hGet)
    simpa [isSoftmaxTensorPosition,hOp] using h

private theorem scoreLoadOperandsOfSite (hX : Consistent l kernel Assumptions.all m X)
    {g h i j site a b : Nat} {vals data : List Value} {sh sh' : TcShape} (hWarp : SameWarp l g h)
    (hw : warpIndex l g < 8) (he : X.get (g,i) = some ⟨site,.tc (.ld a vals sh)⟩)
    (hf : X.get (h,j) = some ⟨site,.tc (.ld b data sh')⟩) : a = b ∧ sh = sh' := by
  have hBand := softmaxTensorCollectiveBand hp hX hw he rfl
  rcases tensorLoadSite hX he with ⟨round,q,rfl⟩ | ⟨stage,chunk,rfl⟩ | ⟨stage,chunk,rfl⟩
  · obtain ⟨w,hw0,rfl,_,rfl⟩ := Scores.scoreLoadAddress hp hX round q he
    obtain ⟨w',hw1,rfl,_,rfl⟩ := Scores.scoreLoadAddress hp hX round q hf
    have hSame : w = w' := Fin.ext (hw0.trans (hWarp.2.trans hw1.symm))
    subst w'
    unfold scoreAddress laneBase
    rw [hWarp.2]
    exact ⟨rfl,rfl⟩
  · have hOther : 7601 ≤ rescaleLoadPc stage chunk := by
      fin_cases stage <;> fin_cases chunk <;> decide
    exact (Nat.not_lt_of_ge hOther hBand.2).elim
  · have hOther : 7601 ≤ finalizeLoadPc stage chunk := by
      fin_cases stage <;> fin_cases chunk <;> decide
    exact (Nat.not_lt_of_ge hOther hBand.2).elim

private theorem probabilityStoreOperandsOfSite (hX : Consistent l kernel Assumptions.all m X)
    {g h i j site a b : Nat} {vals data : List Value} {sh sh' : TcShape} (hWarp : SameWarp l g h)
    (hw : warpIndex l g < 8) (he : X.get (g,i) = some ⟨site,.tc (.st a vals sh)⟩)
    (hf : X.get (h,j) = some ⟨site,.tc (.st b data sh')⟩) : a = b ∧ sh = sh' := by
  have hBand := softmaxTensorCollectiveBand hp hX hw he rfl
  rcases tensorStoreSite hX he with ⟨round,q,rfl⟩ | ⟨stage,chunk,rfl⟩
  · obtain ⟨w,hw0,rfl,_,rfl⟩ := Scores.probabilityStoreAddress hp hX round q he
    obtain ⟨w',hw1,rfl,_,rfl⟩ := Scores.probabilityStoreAddress hp hX round q hf
    have hSame : w = w' := Fin.ext (hw0.trans (hWarp.2.trans hw1.symm))
    subst w'
    unfold probabilityAddress laneBase
    rw [hWarp.2]
    exact ⟨rfl,rfl⟩
  · have hOther : 7601 ≤ rescaleStorePc stage chunk := by
      fin_cases stage <;> fin_cases chunk <;> decide
    exact (Nat.not_lt_of_ge hOther hBand.2).elim

/-- At the same decoded Tensor Memory site and operation, the softmax lanes of one warp use
the same physical address and shape, with no restriction on their individual values. -/
theorem softmaxTensorOperandsAgree (hX : Consistent l kernel Assumptions.all m X) {g h i j : Nat}
    {e f : Event} (hWarp : SameWarp l g h) (hw : warpIndex l g < 8) (he : X.get (g,i) = some e)
    (hf : X.get (h,j) = some f) (hColl : isTcColl e = true) (hSite : e.pc = f.pc)
    (hOp : correctionTensorOperation e.kind = correctionTensorOperation f.kind) :
    AlignedClass.tc.operands e.kind = AlignedClass.tc.operands f.kind := by
  have hData := arithmeticTensorCollectiveIsData hp hX (hw.trans (by decide)) he hColl
  rcases e with ⟨site,k⟩
  rcases f with ⟨site',k'⟩
  change site = site' at hSite
  subst site'
  cases k <;> try contradiction
  rename_i a
  cases a <;> try contradiction
  all_goals cases k' <;> try contradiction
  all_goals
    rename_i b
    cases b <;> try contradiction
  all_goals first
    | rfl
    | obtain ⟨ha,hs⟩ := scoreLoadOperandsOfSite hp hX hWarp hw he hf
      simp [AlignedClass.operands,tcStatic,ha,hs]
    | obtain ⟨ha,hs⟩ := probabilityStoreOperandsOfSite hp hX hWarp hw he hf
      simp [AlignedClass.operands,tcStatic,ha,hs]
    | simp [correctionTensorOperation] at hOp

end PTX.Kernels.TmlFa4Fwd.Thread
