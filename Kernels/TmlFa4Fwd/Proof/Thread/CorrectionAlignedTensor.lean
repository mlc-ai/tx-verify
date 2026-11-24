-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaAlignedTensor
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTmemAddress
import Kernels.TmlFa4Fwd.Proof.Thread.TensorLoadSites
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Kernels.TmlFa4Fwd.Proof.CorrectionLseFallback
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
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
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame _root_.PTX.Kernels.TmlFa4Fwd.Correction Epilogue Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Thread.Correction

private def outsideCorrectionData (pc : Nat) (ins : Instr) : Bool :=
  (decide (8006 ≤ pc ∧ pc < 9044)) || !tcDataOp ins.op

set_option maxRecDepth 100000 in
private theorem correctionOutsideData :
    let start := 7747
    (((kernel.code.drop start).take (9206 - start)).zipIdx start).all
      (fun (i, pc) => outsideCorrectionData pc i) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem noStartupData : (kernel.code.take 174).all (fun i => !tcDataOp i.op) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem noHintData : registerHintSites.all (fun site => match kernel.code[site]? with
    | some i => !tcDataOp i.op
    | none => false) = true := by kernel_rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

theorem correctionCollectiveBand {g j : Nat} (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    {e : Event} (he : X.get (g,j) = some e) (hColl : isTcColl e = true) :
    8006 ≤ e.pc ∧ e.pc < 9044 := by
  have hData := arithmeticTensorCollectiveIsData hp hX hHi he hColl
  rcases get_source hX he with ⟨_,hf⟩ | ⟨_,ins,_,_,hc,hf⟩
  · simp [hf, isTcData] at hData
  have hOp := fires_tcData_op hf hData
  by_cases hStartup : e.pc < 174
  · have hGet : (kernel.code.take 174)[e.pc]? = some ins :=
      (List.getElem?_take_of_lt hStartup).trans hc
    have hNot := List.all_eq_true.mp noStartupData ins (List.mem_of_getElem? hGet)
    simp [hOp] at hNot
  by_cases hHint : e.pc ∈ registerHintSites
  · have hNot := List.all_eq_true.mp noHintData _ hHint
    rw [hc] at hNot
    simp [hOp] at hNot
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hHint
  unfold roleBodyPc at hRole
  have hBand : 7747 ≤ e.pc ∧ e.pc < 9206 := by
    rcases hRole with hExit | hBody
    · omega
    · split_ifs at hBody <;> omega
  let idx := e.pc - 7747
  have hDecode : (((kernel.code.drop 7747).take (9206 - 7747)).zipIdx 7747)[idx]? =
      some (ins, e.pc) := by
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by dsimp [idx]; omega),
      List.getElem?_drop, Nat.add_sub_of_le hBand.1, hc]
    simp
  have hValid := List.all_eq_true.mp correctionOutsideData (ins, e.pc)
    (List.mem_of_getElem? hDecode)
  simpa [outsideCorrectionData, hOp] using hValid

/-- Every correction Tensor Memory collective requires an assigned tile of the same CTA. -/
theorem correctionTensorCollectiveRequiresWork {g j k : Nat} (hLo : 8 ≤ warpIndex l g)
    (hHi : warpIndex l g < 12) (hk : X.TcK (g,j) k) :
    g / l.block < tilePrefix p p.batch * p.heads := by
  obtain ⟨⟨e,he,hColl⟩,_⟩ := hk
  have hBand := correctionCollectiveBand hp hX hLo hHi he hColl
  have hg := event_thread_lt hX he
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  exact correctionWorkOfLateEvent hp hX hg hLo hHi hl (by omega) (by omega) (hSelf ▸ he)

private theorem loadShapeAtSameSite {g h i j site a b : Nat} {values data : List Value}
    {s t : TcShape} (hWarp : SameWarp l g h) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (he : X.get (g,i) = some ⟨site,.tc (.ld a values s)⟩)
    (hf : X.get (h,j) = some ⟨site,.tc (.ld b data t)⟩) :
    a = b ∧ s = t := by
  have hBand := correctionCollectiveBand hp hX hLo hHi he rfl
  have hAddr (stage : Fin 2) (col : Nat) : outputAddress l g stage col =
      outputAddress l h stage col := by
    unfold outputAddress laneBase
    rw [hWarp.2]
  rcases tensorLoadSite hX he with ⟨round,q,rfl⟩ | ⟨stage,chunk,rfl⟩ | ⟨stage,chunk,rfl⟩
  · have hSite : Softmax.scorePc round q < 8006 := by cases round <;> fin_cases q <;> decide
    exact (Nat.not_lt_of_ge hBand.1 hSite).elim
  · obtain ⟨rfl,rfl,_⟩ := rescaleLoadActualAddress hp hX stage chunk he
    obtain ⟨rfl,rfl,_⟩ := rescaleLoadActualAddress hp hX stage chunk hf
    exact ⟨hAddr ..,rfl⟩
  · obtain ⟨rfl,rfl,_⟩ := finalizeLoadActualAddress hp hX stage chunk he
    obtain ⟨rfl,rfl,_⟩ := finalizeLoadActualAddress hp hX stage chunk hf
    exact ⟨hAddr ..,rfl⟩

private theorem storeShapeAtSameSite {g h i j site a b : Nat} {values data : List Value}
    {s t : TcShape} (hWarp : SameWarp l g h) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (he : X.get (g,i) = some ⟨site,.tc (.st a values s)⟩)
    (hf : X.get (h,j) = some ⟨site,.tc (.st b data t)⟩) :
    a = b ∧ s = t := by
  have hBand := correctionCollectiveBand hp hX hLo hHi he rfl
  rcases tensorStoreSite hX he with ⟨round,q,rfl⟩ | ⟨stage,chunk,rfl⟩
  · have hSite : Softmax.probabilityPc round q < 8006 := by
      cases round <;> fin_cases q <;> decide
    exact (Nat.not_lt_of_ge hBand.1 hSite).elim
  · obtain ⟨rfl,rfl,_⟩ := rescaleStoreActualAddress hp hX stage chunk he
    obtain ⟨rfl,rfl,_⟩ := rescaleStoreActualAddress hp hX stage chunk hf
    refine ⟨?_,rfl⟩
    unfold outputAddress laneBase
    rw [hWarp.2]

omit hp hX in
/-- The data-operation part of a correction collective, with per-lane values and address erased. -/
def correctionTensorOperation : Kind → Option (Fin 4)
  | .tc (.ld ..) => some 0
  | .tc .waitLd => some 1
  | .tc (.st ..) => some 2
  | .tc .waitSt => some 3
  | _ => none

/-- Once two correction lanes agree on the static site and operation, their addresses and shapes
agree. The per-lane loaded and stored values are unconstrained. -/
theorem correctionTensorOperandsAgree {g h i j : Nat} {e f : Event} (hWarp : SameWarp l g h)
    (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12) (he : X.get (g,i) = some e)
    (hf : X.get (h,j) = some f) (hColl : isTcColl e = true) (hSite : e.pc = f.pc)
    (hOp : correctionTensorOperation e.kind = correctionTensorOperation f.kind) :
    AlignedClass.tc.operands e.kind = AlignedClass.tc.operands f.kind := by
  have hData := arithmeticTensorCollectiveIsData hp hX hHi he hColl
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
    | obtain ⟨ha, hs⟩ := loadShapeAtSameSite hp hX hWarp hLo hHi he hf
      simp [AlignedClass.operands, tcStatic, ha, hs]
    | obtain ⟨ha, hs⟩ := storeShapeAtSameSite hp hX hWarp hLo hHi he hf
      simp [AlignedClass.operands, tcStatic, ha, hs]
    | simp [correctionTensorOperation] at hOp

omit hp hX in
set_option maxRecDepth 100000 in
private theorem finalTensorFloor :
    (kernel.code.drop 9044).all (fun i => staysPastEvent 9044 i.op) = true := by kernel_rfl

/-- After issuing its terminal load wait, a correction lane cannot issue another collective. -/
theorem correctionNoTensorCollectiveAfterFinalWait {g i j k : Nat} (hLo : 8 ≤ warpIndex l g)
    (hHi : warpIndex l g < 12) (hOrder : i < j) (hWait : X.get (g,i) = some ⟨9043,.tc .waitLd⟩)
    (hNext : X.TcK (g,j) k) :
    False := by
  obtain ⟨⟨e,he,hColl⟩,_⟩ := hNext
  have hj : j < (X.tr g).length := len_of_get he
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t,u,hStep,hTail⟩ := hr.after_event hWait (by omega)
  have hPc : t.pc = 9043 := (estep_source_pc hStep).symm
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source hStep
  rw [hPc,Flow.code_9043] at hCode
  obtain rfl := Option.some.inj hCode
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp only [eventTmpl,tcTmpl,hBlock,ofExec,pure,Except.pure,↓reduceIte,Fires] at hFire
  have hu : 9044 ≤ u.pc := by rw [Option.some.inj hFire.2]; simp [next,hPc]
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hTail
  have hMem : e ∈ (X.tr g).drop (i+1) := by
    apply List.mem_of_getElem? (i := j-(i+1))
    rwa [List.getElem?_drop,Nat.add_sub_of_le (by omega)]
  have hSeg (site : Nat) (hs : 9044 ≤ site) (hm : site ∈ Assumptions.swExp2Sites) :
      ∀ seg, PTX.Assumption.cuteExp2.matchAt kernel site = some seg → 9044 ≤ seg.stop := by
    simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
    omega
  have hFloor := eventTailEventsOfSegmentFloor finalTensorFloor hSeg hWalk hu e hMem
  exact Nat.not_lt_of_ge hFloor (correctionCollectiveBand hp hX hLo hHi he hColl).2

end PTX.Kernels.TmlFa4Fwd.Thread
