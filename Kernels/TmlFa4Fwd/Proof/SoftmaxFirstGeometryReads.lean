-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstGeometry
public import Kernels.TmlFa4Fwd.Proof.MmaTripReads
import Kernels.TmlFa4Fwd.Flow.Code.Part052
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame

import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
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
import Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

def geometryReadSite : Fin 3 → Mma.TripReadSite
  | 0 => ⟨3369, 7892, 0, 2848⟩
  | 1 => ⟨3370, 7892, 4, 2849⟩
  | 2 => ⟨3373, 7893, 0, 1224⟩

private theorem geometryReadCode (i : Fin 3) :
    kernel.code[(geometryReadSite i).pc]? = some ⟨none, .mem (Mma.tripReadMem (geometryReadSite i))⟩
      := by
  fin_cases i
  · exact Flow.code_3369
  · exact Flow.code_3370
  · exact Flow.code_3373

def geometryReadOperands (p : Params) (batch tile : Nat) (stage : Fin 2) :
    List (Nat × Value) :=
  [(7892, b64 (p.cuQBase + 4*batch)), (7891, b64 (4*batch)), (7503, b64 p.usedKBase),
    (7246, b32 tile), (2772, b32 stage.val)]

/-- Launch pointers and tile coordinates live before the decoded address arithmetic. -/
def geometryAddressInputs (p : Params) (batch tile : Nat) (stage : Fin 2) :
    List (Nat × Value) :=
  [(7247, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
    (7246, b32 tile), (2772, b32 stage.val)]

def firstGeometryAddressInput (p : Params) (l : Launch) (g batch tile : Nat) (stage : Fin 2) :
    List (Nat × Value) :=
  geometryAddressInputs p batch tile stage ++ firstGeometrySync l g stage

private theorem truncate64 (word : BitVec 64) : truncBits 64 word = word := by
  apply BitVec.eq_of_toNat_eq
  simp [truncBits, Nat.mod_eq_of_lt word.isLt]

private theorem requestAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g batch tile : Nat) (stage : Fin 2) (hb : batch < p.batch) :
    Seg kernel Assumptions.all l g 2 3367 (geometryAddressInputs p batch tile stage)
      3369 (geometryReadOperands p batch tile stage) := by
  have hBatch31 := lt_trans hb hp.shape.2.1
  have hBatch32 : batch < 2^32 := by omega
  have hRead := truncBits_ofNat hBatch32 (by decide)
  have hSigned := Loader.int32Signed hBatch31
  have hFour : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := by decide
  have hBatch : (batch : Int) * 4 = ((4 * batch : Nat) : Int) := by push_cast; omega
  intro t ht
  simp only [geometryAddressInputs, geometryReadOperands] at ht ⊢
  seg_fp ht using norm_bits [b64, truncate64, hRead, hSigned, hFour, hBatch,
    BitVec.ofInt_natCast, ← BitVec.ofNat_add]

private def keyReadEntry (p : Params) (batch tile : Nat) (stage : Fin 2) :
    List (Nat × Value) :=
  [(7893, b64 (p.usedKBase+4*batch)), (1223, maskSigned (-(p.qLength batch : Int))),
    (7246, b32 tile), (2772, b32 stage.val)]

private theorem usedKAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g batch tile : Nat) (stage : Fin 2) (hb : batch < p.batch) (hq : 0 < p.qLength batch) :
    Seg kernel Assumptions.all l g 2 3371
      ((2849, b32 (p.qOffset (batch+1))) :: (2848, b32 (p.qOffset batch)) ::
        geometryReadOperands p batch tile stage)
      3373 (keyReadEntry p batch tile stage) := by
  have hA := hp.qOffset_le_total (b := batch) hb.le
  have hB := hp.qOffset_le_total (b := batch+1) (by omega)
  have hTot := hp.shape.2.2.2.2
  have hRange := hp.ranges ⟨p.usedKBase, 4*p.batch⟩ (by simp [Params.inputRegions])
  change p.usedKBase + 4*p.batch ≤ 2^64 at hRange
  change 0 < p.qOffset (batch+1) - p.qOffset batch at hq
  have hNeg := negativeLengthWord (q := p.qOffset (batch+1)-p.qOffset batch) (by omega) hq
  intro t ht
  simp only [geometryReadOperands, keyReadEntry] at ht ⊢
  seg_fp ht using (first
    | solve | simp only [b64, truncate64, ← BitVec.ofNat_add]
    | norm_bits [Params.qLength, hNeg])

private theorem geometryAddressFrame {l : Launch} {g : Nat} {t u : TState} (key : Bool)
    (hPc : t.pc = (if key then 3371 else 3367))
    (hr : run kernel Assumptions.all l g 2 t = some u) :
    ∀ r ∈ firstGeometryCarryRegs, u.regs r = t.regs r := by
  let start : Nat := if key then 3371 else 3367
  refine fixedFrame (first := start) (stop := start+2) (kept := (· ∈ firstGeometryCarryRegs))
    ?_ ?_ (by omega) (by omega) hr
  · intro pc hLo hHi
    cases key <;> simp only [start, Bool.false_eq_true, ite_false, ite_true, Nat.reduceAdd]
      at hLo hHi <;> interval_cases pc
    · exact ⟨_,Flow.code_3367,rfl,rfl,by simp [BrxTarget],by decide⟩
    · exact ⟨_,Flow.code_3368,rfl,rfl,by simp [BrxTarget],by decide⟩
    · exact ⟨_,Flow.code_3371,rfl,rfl,by simp [BrxTarget],by decide⟩
    · exact ⟨_,Flow.code_3372,rfl,rfl,by simp [BrxTarget],by decide⟩
  · intro pc hLo hHi
    cases key <;> simp [start] at hLo hHi <;>
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] <;> omega

private theorem syncReadKeep (l : Launch) (g : Nat) (stage : Fin 2) :
    ∀ x ∈ firstGeometrySync l g stage, x.1 ∈ firstGeometryCarryRegs := by
  intro x hx
  simp only [firstGeometrySync, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact of_decide_eq_true rfl

theorem geometryAddressSegmentFramed {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g batch tile : Nat) (stage : Fin 2) (hb : batch < p.batch)
    {F : List (Nat × Value)} (hF : ∀ x ∈ F, x.1 ∈ firstGeometryCarryRegs) :
    Seg kernel Assumptions.all l g 2 3367 (geometryAddressInputs p batch tile stage ++ F)
      3369 (geometryReadOperands p batch tile stage ++ F) := by
  intro t ht
  obtain ⟨hInput, hKeep⟩ := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨u, hu, hU⟩ := (requestAddress hp g batch tile stage hb).apply (ht.mono hInput)
  have hCarry := Epilogue.holdsSchedulerFrame hKeep (geometryAddressFrame false ht.1 hu) hF
  exact ⟨u, hu, hU.mono ((holds_append ..).mpr ⟨hU.2.2.2.2, hCarry⟩)⟩

private theorem geometryReadTail {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {result : Option TState} (which : Fin 3) (hPc : s.pc = (geometryReadSite which).pc+1)
    (hr : Run kernel Assumptions.all l g s es result) :
    ∀ e ∈ es, (geometryReadSite which).pc < e.pc := by
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hr
  let floor := (geometryReadSite which).pc+1
  have hCode : (kernel.code.drop floor).all (fun i => Thread.staysPastEvent floor i.op) = true := by
    fin_cases which <;> decide +kernel
  have hSegments : Assumptions.swExp2Sites.all (fun s => match cuteExp2.matchAt kernel s with
    | none => false
    | some seg => decide (floor ≤ seg.stop)) = true := by
    fin_cases which <;> decide +kernel
  intro e hMem
  apply Thread.eventTailEventsOfSegmentFloor hCode (fun site _ hSite seg hMatch => ?_)
    hWalk hPc.ge e hMem
  have ha := List.all_eq_true.mp hSegments site hSite
  rw [hMatch,decide_eq_true_eq] at ha
  exact ha

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- An observed opening geometry read uses its launch address and payload, including
when the consistent prefix ends at that read. -/
theorem geometryReadOfObservedPrefix (hX : Consistent l kernel Assumptions.all m X)
    {g j position batch tile : Nat} (stage : Fin 2) (hb : batch < p.batch)
    (hTile : 256*tile < p.qLength batch) (which : Fin 3) {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g,position) = some ⟨(geometryReadSite which).pc,.rd a bytes⟩) (hle : j ≤ position)
    {t : TState} {result : Option TState}
    (ht : At t 3367 (geometryAddressInputs p batch tile stage))
    (hCuQ : ∀ off ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase+4*(batch+off))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*batch)).at k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) result) :
    let addr := if which = 2 then p.usedKBase+4*batch else p.cuQBase+4*(batch+which.val)
    let value := if which = 2 then p.kLength batch else p.qOffset (batch+which.val)
    a = {loc := globalLoc addr,size := 4} ∧ bytes = (b32 value).toBytes.map some := by
  let qBase := p.cuQBase+4*batch
  let kBase := p.usedKBase+4*batch
  have hQ := hp.alignment.2.2.2.2.2.2.2.2.1
  have hK := hp.alignment.2.2.2.2.2.2.2.2.2.1
  have hCuRange := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
  have hKRange := hp.ranges ⟨p.usedKBase,4*p.batch⟩ (by simp [Params.inputRegions])
  change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hCuRange
  change p.usedKBase+4*p.batch ≤ 2^64 at hKRange
  have hEq : qBase + (geometryReadSite 1).off = p.cuQBase+4*(batch+1) := by
    dsimp [qBase,geometryReadSite]
    omega
  have hLength : position < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hasEvent (base : Nat) (hLe : base ≤ position) : (X.tr g).drop base ≠ [] := by
    rw [ne_eq,List.drop_eq_nil_iff]
    omega
  have nextPosition {base site : Nat} {k : Kind}
      (hGet : X.get (g,base) = some ⟨site,k⟩) (hSite : site < (geometryReadSite which).pc)
      (hLe : base ≤ position) : base+1 ≤ position := by
    rcases Nat.eq_or_lt_of_le hLe with rfl | hLt
    · have hSame := congrArg Event.pc (Option.some.inj (hGet.symm.trans he))
      exact (Nat.ne_of_lt hSite hSame).elim
    · exact hLt
  obtain ⟨v,hv,hV⟩ := (requestAddress hp g batch tile stage hb).apply ht
  obtain ⟨he0,hAfter0,hR0⟩ :=
    Mma.wordReadTraceNonempty hX (addr := qBase) (word := p.qOffset batch) (geometryReadSite 0)
      (geometryReadCode 0) hV
      (by simp [geometryReadOperands,geometryReadSite,qBase])
      (by dsimp [qBase,geometryReadSite]; omega) (by dsimp [qBase,geometryReadSite]; omega)
      (hp.cuQ _ hb.le)
      (by simpa only [qBase,geometryReadSite,Nat.add_zero] using hCuQ 0 (by decide))
      (by simp [geometryReadOperands,geometryReadSite])
      (hr.after_local_nonempty (run_rtg hv) (hasEvent j hle)) (hasEvent j hle)
  by_cases hZero : which = 0
  · subst which
    exact Thread.metadataReadPayloadOfSuffix hle he he0 (geometryReadTail 0 hAfter0.1 hR0)
  have hOne := nextPosition he0 (by fin_cases which <;> first | contradiction | decide) hle
  obtain ⟨he1,hAfter1,hR1⟩ :=
    Mma.wordReadTraceNonempty hX (addr := qBase) (word := p.qOffset (batch+1)) (geometryReadSite 1)
      (geometryReadCode 1) hAfter0
      (by simp [geometryReadOperands,geometryReadSite,qBase]) (by rw [hEq]; omega)
      (by rw [hEq]; omega) (by rw [hEq]; exact hp.cuQ _ (by omega))
      (by rw [hEq]; exact hCuQ 1 (by decide))
      (by simp [geometryReadOperands,geometryReadSite])
      hR0 (hasEvent _ hOne)
  by_cases hSecond : which = 1
  · subst which
    have hExact := Thread.metadataReadPayloadOfSuffix hOne he he1
      (geometryReadTail 1 hAfter1.1 hR1)
    change a = {loc := globalLoc (p.cuQBase+4*(batch+1)),size := 4} ∧
        bytes = (b32 (p.qOffset (batch+1))).toBytes.map some
    rw [← hEq]
    exact hExact
  have hLast : which = 2 := by fin_cases which <;> first | contradiction | rfl
  subst which
  have hTwo := nextPosition he1 (by decide) hOne
  obtain ⟨w,hw,hW⟩ := (usedKAddress hp g batch tile stage hb (by omega)).apply hAfter1
  obtain ⟨he2,hAfter2,hR2⟩ :=
    Mma.wordReadTraceNonempty hX (addr := kBase) (word := p.kLength batch) (geometryReadSite 2)
      (geometryReadCode 2) hW (by simp [geometryReadSite,keyReadEntry,kBase])
      (by dsimp [kBase,geometryReadSite]; omega) (by dsimp [kBase,geometryReadSite]; omega)
      (hp.usedK _ hb) hUsedK (by simp [geometryReadSite,keyReadEntry])
      (hR1.after_local_nonempty (run_rtg hw) (hasEvent _ hTwo)) (hasEvent _ hTwo)
  exact Thread.metadataReadPayloadOfSuffix hTwo he he2 (geometryReadTail 2 hAfter2.1 hR2)

omit hp in
/-- The three protected query and key length reads occupy consecutive trace positions. -/
def FirstGeometryReads (p : Params) (X : Execution) (g j batch : Nat) : Prop :=
  X.get (g, j) = some ⟨3369,
    .rd {loc := globalLoc (p.cuQBase+4*batch), size := 4}
      ((b32 (p.qOffset batch)).toBytes.map some)⟩ ∧
  X.get (g, j+1) = some ⟨3370,
    .rd {loc := globalLoc (p.cuQBase+4*(batch+1)), size := 4}
      ((b32 (p.qOffset (batch+1))).toBytes.map some)⟩ ∧
  X.get (g, j+2) = some ⟨3373,
    .rd {loc := globalLoc (p.usedKBase+4*batch), size := 4}
      ((b32 (p.kLength batch)).toBytes.map some)⟩

/-- The actual softmax prefix loads both cumulative query endpoints and used-K and computes
the initial loop geometry from the protected request data. -/
private theorem fetchedGeometryFramedBefore (hX : Consistent l kernel Assumptions.all m X)
    {g j batch tile position : Nat} {target : Event} (stage : Fin 2) (hb : batch < p.batch)
    {F : List (Nat × Value)} (hF : ∀ x ∈ F, x.1 ∈ firstGeometryCarryRegs)
    (hTile : 256*tile < p.qLength batch) {t : TState} {result : Option TState}
    (hTarget : X.get (g,position) = some target) (hLate : 3374 ≤ target.pc) (hPos : j ≤ position)
    (ht : At t 3369 (geometryReadOperands p batch tile stage ++ F))
    (hCuQ : ∀ off ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase+4*(batch+off))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*batch)).at k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) result) :
    ∃ u, At u 3418 (F ++ firstGeometryFacts p batch tile stage) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+3)) result ∧
      FirstGeometryReads p X g j batch := by
  have hQ := hp.alignment.2.2.2.2.2.2.2.2.1
  have hK := hp.alignment.2.2.2.2.2.2.2.2.2.1
  have hCuRange := hp.ranges ⟨p.cuQBase, 4*(p.batch+1)⟩ (by simp [Params.inputRegions])
  have hKRange := hp.ranges ⟨p.usedKBase, 4*p.batch⟩ (by simp [Params.inputRegions])
  change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hCuRange
  change p.usedKBase+4*p.batch ≤ 2^64 at hKRange
  have hSafe (pair : Nat × Value) (hm : pair ∈ F) :
      pair.1 ≠ 2848 ∧ pair.1 ≠ 2849 ∧ pair.1 ≠ 1224 := by
    have hAudit : firstGeometryCarryRegs.all
        (fun r => decide (r ≠ 2848 ∧ r ≠ 2849 ∧ r ≠ 1224)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp hAudit pair.1 (hF pair hm))
  let qBase := p.cuQBase+4*batch
  let kBase := p.usedKBase+4*batch
  have hEq : qBase + (geometryReadSite 1).off = p.cuQBase+4*(batch+1) := by
    dsimp only [qBase, geometryReadSite]
    omega
  have hLength : position < (X.tr g).length := (List.getElem?_eq_some_iff.mp hTarget).1
  have nonempty (base : Nat) (hLe : base ≤ position) : (X.tr g).drop base ≠ [] := by
    rw [ne_eq,List.drop_eq_nil_iff]
    omega
  have nextPosition {base site : Nat} {k : Kind}
      (hGet : X.get (g,base) = some ⟨site,k⟩) (hSite : site < 3374)
      (hLe : base ≤ position) : base+1 ≤ position := by
    rcases Nat.eq_or_lt_of_le hLe with hEq | hLt
    · have hSame := congrArg Event.pc (Option.some.inj ((hEq ▸ hGet).symm.trans hTarget))
      change site = target.pc at hSame
      omega
    · omega
  obtain ⟨hE0, hAfter0, hR0⟩ :=
    Mma.wordReadTraceNonempty hX (addr := qBase) (word := p.qOffset batch) (geometryReadSite 0)
      (geometryReadCode 0) ht
      (by simp [geometryReadOperands, geometryReadSite, qBase])
      (by dsimp [qBase, geometryReadSite]; omega) (by dsimp [qBase, geometryReadSite]; omega)
      (hp.cuQ _ hb.le)
      (by simpa only [qBase, geometryReadSite, Nat.add_zero] using hCuQ 0 (by decide))
      (by
        intro pair hh
        simp only [geometryReadOperands, List.cons_append, List.nil_append, List.mem_cons] at hh
        rcases hh with rfl | rfl | rfl | rfl | rfl | hm
        · exact of_decide_eq_true rfl
        · exact of_decide_eq_true rfl
        · exact of_decide_eq_true rfl
        · exact of_decide_eq_true rfl
        · exact of_decide_eq_true rfl
        · exact (hSafe pair hm).1)
      hr (nonempty j hPos)
  have hOne := nextPosition hE0 (by decide) hPos
  obtain ⟨hE1, hAfter1, hR1⟩ :=
    Mma.wordReadTraceNonempty hX (addr := qBase) (word := p.qOffset (batch+1)) (geometryReadSite 1)
      (geometryReadCode 1) hAfter0
      (by simp [geometryReadOperands, geometryReadSite, qBase]) (by rw [hEq]; omega)
      (by rw [hEq]; omega) (by rw [hEq]; exact hp.cuQ _ (by omega))
      (by rw [hEq]; exact hCuQ 1 (by decide))
      (by
        intro pair hh
        simp only [geometryReadOperands, List.cons_append, List.nil_append, List.mem_cons] at hh
        rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | hm <;>
          first | exact of_decide_eq_true rfl | exact (hSafe pair hm).2.1)
      hR0 (nonempty _ hOne)
  have hTwo := nextPosition hE1 (by decide) hOne
  have hAfter1Regs := hAfter1.2.2.2.2
  change Holds _ (((2849, b32 (p.qOffset (batch+1))) ::
    (2848, b32 (p.qOffset batch)) :: geometryReadOperands p batch tile stage) ++ F) at hAfter1Regs
  obtain ⟨hArgs,hKeep⟩ := (holds_append _ _ _).mp hAfter1Regs
  obtain ⟨v, hvRun, hKey⟩ :=
    (usedKAddress hp g batch tile stage hb (by omega)).apply (hAfter1.mono hArgs)
  have hKeyKeep := Epilogue.holdsSchedulerFrame hKeep (geometryAddressFrame true hAfter1.1 hvRun)
    hF
  have hv : At v 3373 (keyReadEntry p batch tile stage ++ F) :=
    hKey.mono ((holds_append ..).mpr ⟨hKey.2.2.2.2,hKeyKeep⟩)
  obtain ⟨hE2, hAfter2, hR2⟩ :=
    Mma.wordReadTraceNonempty hX (addr := kBase) (word := p.kLength batch) (geometryReadSite 2)
      (geometryReadCode 2) hv (by simp [geometryReadSite, keyReadEntry, kBase])
      (by dsimp [kBase, geometryReadSite]; omega) (by dsimp [kBase, geometryReadSite]; omega)
      (hp.usedK _ hb) hUsedK
      (by
        intro pair hh
        simp only [keyReadEntry, List.cons_append, List.nil_append, List.mem_cons] at hh
        rcases hh with rfl | rfl | rfl | rfl | hm <;>
          first | exact of_decide_eq_true rfl | exact (hSafe pair hm).2.2)
      (hR1.after_local_nonempty (run_rtg hvRun) (nonempty _ hTwo)) (nonempty _ hTwo)
  have hThree := nextPosition hE2 (by decide) hTwo
  have hGeometry : At (next (setReg v 1224 (b32 (p.kLength batch)))) 3374
      (firstGeometryInput p batch tile stage) :=
    hAfter2.mono (by
      refine ⟨holds_mem hAfter2.2.2.2.2 (by simp [keyReadEntry]),
        holds_mem hAfter2.2.2.2.2 (by simp [geometryReadSite]),
        holds_mem hAfter2.2.2.2.2 (by simp [keyReadEntry]),
        holds_mem hAfter2.2.2.2.2 (by simp [keyReadEntry]), trivial⟩)
  obtain ⟨u, huRun, hu⟩ := (firstGeometrySegment hp g batch tile stage hb hTile).apply hGeometry
  have hFrame := geometryFrame (keep := firstGeometryCarryRegs) (by decide) (by decide) hGeometry.1
    (by set_option maxRecDepth 100000 in kernel_rfl) huRun
  have hAfter2Regs := hAfter2.2.2.2.2
  change Holds _ (((1224, b32 (p.kLength batch)) :: keyReadEntry p batch tile stage) ++ F)
    at hAfter2Regs
  have hSync := Epilogue.holdsSchedulerFrame ((holds_append _ _ _).mp hAfter2Regs).2 hFrame hF
  change qBase + 4 = p.cuQBase+4*(batch+1) at hEq
  exact ⟨u, hu.mono ((holds_append _ _ _).mpr ⟨hSync, hu.2.2.2.2⟩),
    hR2.after_local_nonempty (run_rtg huRun) (nonempty _ hThree), hE0,
    by simpa only [hEq, geometryReadSite] using hE1, hE2⟩

private theorem fetchedGeometryFramed (hX : Consistent l kernel Assumptions.all m X)
    {g j batch tile : Nat} (stage : Fin 2) (hb : batch < p.batch) {F : List (Nat × Value)}
    (hF : ∀ x ∈ F, x.1 ∈ firstGeometryCarryRegs) (hTile : 256*tile < p.qLength batch) {t : TState}
    (ht : At t 3369 (geometryReadOperands p batch tile stage ++ F))
    (hCuQ : ∀ off ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase+4*(batch+off))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*batch)).at k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ u, At u 3418 (F ++ firstGeometryFacts p batch tile stage) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+3)) none ∧
      FirstGeometryReads p X g j batch := by
  have hQ := hp.alignment.2.2.2.2.2.2.2.2.1
  have hK := hp.alignment.2.2.2.2.2.2.2.2.2.1
  have hCuRange := hp.ranges ⟨p.cuQBase, 4*(p.batch+1)⟩ (by simp [Params.inputRegions])
  have hKRange := hp.ranges ⟨p.usedKBase, 4*p.batch⟩ (by simp [Params.inputRegions])
  change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hCuRange
  change p.usedKBase+4*p.batch ≤ 2^64 at hKRange
  have hSafe (pair : Nat × Value) (hm : pair ∈ F) :
      pair.1 ≠ 2848 ∧ pair.1 ≠ 2849 ∧ pair.1 ≠ 1224 := by
    have hAudit : firstGeometryCarryRegs.all
        (fun r => decide (r ≠ 2848 ∧ r ≠ 2849 ∧ r ≠ 1224)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp hAudit pair.1 (hF pair hm))
  let qBase := p.cuQBase+4*batch
  let kBase := p.usedKBase+4*batch
  have hEq : qBase + (geometryReadSite 1).off = p.cuQBase+4*(batch+1) := by
    dsimp only [qBase, geometryReadSite]
    omega
  obtain ⟨hE0, hAfter0, hR0⟩ :=
    Mma.wordReadTrace hX (addr := qBase) (word := p.qOffset batch) (geometryReadSite 0)
      (geometryReadCode 0) ht
      (by simp [geometryReadOperands, geometryReadSite, qBase])
      (by dsimp [qBase, geometryReadSite]; omega) (by dsimp [qBase, geometryReadSite]; omega)
      (hp.cuQ _ hb.le)
      (by simpa only [qBase, geometryReadSite, Nat.add_zero] using hCuQ 0 (by decide))
      (by
        intro pair hh
        simp only [geometryReadOperands, List.cons_append, List.nil_append, List.mem_cons] at hh
        rcases hh with rfl | rfl | rfl | rfl | rfl | hm
        · exact of_decide_eq_true rfl
        · exact of_decide_eq_true rfl
        · exact of_decide_eq_true rfl
        · exact of_decide_eq_true rfl
        · exact of_decide_eq_true rfl
        · exact (hSafe pair hm).1)
      hr
  obtain ⟨hE1, hAfter1, hR1⟩ :=
    Mma.wordReadTrace hX (addr := qBase) (word := p.qOffset (batch+1)) (geometryReadSite 1)
      (geometryReadCode 1) hAfter0
      (by simp [geometryReadOperands, geometryReadSite, qBase]) (by rw [hEq]; omega)
      (by rw [hEq]; omega) (by rw [hEq]; exact hp.cuQ _ (by omega))
      (by rw [hEq]; exact hCuQ 1 (by decide))
      (by
        intro pair hh
        simp only [geometryReadOperands, List.cons_append, List.nil_append, List.mem_cons] at hh
        rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | hm <;>
          first | exact of_decide_eq_true rfl | exact (hSafe pair hm).2.1)
      hR0
  have hAfter1Regs := hAfter1.2.2.2.2
  change Holds _ (((2849, b32 (p.qOffset (batch+1))) ::
    (2848, b32 (p.qOffset batch)) :: geometryReadOperands p batch tile stage) ++ F) at hAfter1Regs
  obtain ⟨hArgs,hKeep⟩ := (holds_append _ _ _).mp hAfter1Regs
  obtain ⟨v, hvRun, hKey⟩ :=
    (usedKAddress hp g batch tile stage hb (by omega)).apply (hAfter1.mono hArgs)
  have hKeyKeep := Epilogue.holdsSchedulerFrame hKeep (geometryAddressFrame true hAfter1.1 hvRun)
    hF
  have hv : At v 3373 (keyReadEntry p batch tile stage ++ F) :=
    hKey.mono ((holds_append ..).mpr ⟨hKey.2.2.2.2,hKeyKeep⟩)
  obtain ⟨hE2, hAfter2, hR2⟩ :=
    Mma.wordReadTrace hX (addr := kBase) (word := p.kLength batch) (geometryReadSite 2)
      (geometryReadCode 2) hv (by simp [geometryReadSite, keyReadEntry, kBase])
      (by dsimp [kBase, geometryReadSite]; omega) (by dsimp [kBase, geometryReadSite]; omega)
      (hp.usedK _ hb) hUsedK
      (by
        intro pair hh
        simp only [keyReadEntry, List.cons_append, List.nil_append, List.mem_cons] at hh
        rcases hh with rfl | rfl | rfl | rfl | hm <;>
          first | exact of_decide_eq_true rfl | exact (hSafe pair hm).2.2)
      (hR1.after_local (run_rtg hvRun))
  have hGeometry : At (next (setReg v 1224 (b32 (p.kLength batch)))) 3374
      (firstGeometryInput p batch tile stage) :=
    hAfter2.mono (by
      refine ⟨holds_mem hAfter2.2.2.2.2 (by simp [keyReadEntry]),
        holds_mem hAfter2.2.2.2.2 (by simp [geometryReadSite]),
        holds_mem hAfter2.2.2.2.2 (by simp [keyReadEntry]),
        holds_mem hAfter2.2.2.2.2 (by simp [keyReadEntry]), trivial⟩)
  obtain ⟨u, huRun, hu⟩ := (firstGeometrySegment hp g batch tile stage hb hTile).apply hGeometry
  have hFrame := geometryFrame (keep := firstGeometryCarryRegs) (by decide) (by decide) hGeometry.1
    (by set_option maxRecDepth 100000 in kernel_rfl) huRun
  have hAfter2Regs := hAfter2.2.2.2.2
  change Holds _ (((1224, b32 (p.kLength batch)) :: keyReadEntry p batch tile stage) ++ F)
    at hAfter2Regs
  have hSync := Epilogue.holdsSchedulerFrame ((holds_append _ _ _).mp hAfter2Regs).2 hFrame hF
  change qBase + 4 = p.cuQBase+4*(batch+1) at hEq
  exact ⟨u, hu.mono ((holds_append _ _ _).mpr ⟨hSync, hu.2.2.2.2⟩),
    hR2.after_local (run_rtg huRun), hE0, by simpa only [hEq, geometryReadSite] using hE1, hE2⟩

/-- The selected tile and launch pointers suffice to observe the request's geometry. -/
theorem geometryLengthTrace (hX : Consistent l kernel Assumptions.all m X) {g j batch tile : Nat}
    (stage : Fin 2) (hb : batch < p.batch) (hTile : 256*tile < p.qLength batch) {t : TState}
    (ht : At t 3367 (geometryAddressInputs p batch tile stage))
    (hCuQ : ∀ off ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase+4*(batch+off))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*batch)).at k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ u, At u 3418 (firstGeometryFacts p batch tile stage) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+3)) none ∧
      FirstGeometryReads p X g j batch := by
  obtain ⟨v,hv,hV⟩ := (requestAddress hp g batch tile stage hb).apply ht
  have hV' : At v 3369 (geometryReadOperands p batch tile stage ++ []) := by simpa using hV
  exact fetchedGeometryFramed hp hX stage hb (by simp) hTile hV' hCuQ hUsedK
    (hr.after_local (run_rtg hv))

/-- A finite prefix reaching late softmax work contains the actual length loads. -/
theorem geometryLengthTraceBeforeEvent (hX : Consistent l kernel Assumptions.all m X)
    {g j batch tile position : Nat} {target : Event} (stage : Fin 2) (hb : batch < p.batch)
    (hTile : 256*tile < p.qLength batch) {t : TState} {result : Option TState}
    (hTarget : X.get (g,position) = some target) (hLate : 3374 ≤ target.pc) (hPos : j ≤ position)
    (ht : At t 3367 (geometryAddressInputs p batch tile stage))
    (hCuQ : ∀ off ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase+4*(batch+off))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*batch)).at k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) result) :
    ∃ u, At u 3418 (firstGeometryFacts p batch tile stage) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+3)) result ∧
      FirstGeometryReads p X g j batch := by
  obtain ⟨v,hv,hV⟩ := (requestAddress hp g batch tile stage hb).apply ht
  have hV' : At v 3369 (geometryReadOperands p batch tile stage ++ []) := by simpa using hV
  exact fetchedGeometryFramedBefore hp hX stage hb (by simp) hTile hTarget hLate hPos
    hV' hCuQ hUsedK
    (hr.after_local_nonempty (run_rtg hv) (by
      rw [ne_eq,List.drop_eq_nil_iff]
      have hLen := (List.getElem?_eq_some_iff.mp hTarget).1
      change position < (X.tr g).length at hLen
      omega))

/-- Starting with the selected batch and its launch pointers, softmax reads the request
geometry, acknowledges correction, and reaches the phase-zero QK wait with the address frame. -/
theorem firstGeometryReadyTraceFramed (hX : Consistent l kernel Assumptions.all m X)
    {g j batch tile : Nat} (stage : Fin 2) (hb : batch < p.batch)
    (hTile : 256*tile < p.qLength batch) {t : TState} {F : List (Nat × Value)}
    (hF : ∀ x ∈ F, x.1 ∈ firstGeometryCarryRegs)
    (ht : At t 3367 (firstGeometryAddressInput p l g batch tile stage ++ F))
    (hCuQ : ∀ off ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase+4*(batch+off))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*batch)).at k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ fails u, FirstGeometryReads p X g j batch ∧
      (X.tr g).drop (j+3) =
        List.replicate fails ⟨3420, .wait (waitLoc l g stage 0) 1 false true .cta⟩ ++
          ⟨3420, .wait (waitLoc l g stage 0) 1 true true .cta⟩ ::
            (X.tr g).drop (j+3+fails+1) ∧
      At u 3425 ([(1229, b32 (Mma.trips p batch tile-1)), (2770, b32 0)] ++
        firstGeometryAckFacts p l g batch tile stage ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+3+fails+1)) none := by
  have hRegs : ∀ x ∈ firstGeometrySync l g stage ++ F, x.1 ∈ firstGeometryCarryRegs := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact syncReadKeep l g stage x h
    · exact hF x h
  have hAt : At t 3367 (geometryAddressInputs p batch tile stage ++
      (firstGeometrySync l g stage ++ F)) := by
    simpa only [firstGeometryAddressInput, List.append_assoc] using ht
  obtain ⟨v, hv, hvAt⟩ := (geometryAddressSegmentFramed hp g batch tile stage hb hRegs).apply hAt
  obtain ⟨w, hwAt, hw, hReads⟩ := fetchedGeometryFramed hp hX stage hb hRegs hTile hvAt hCuQ hUsedK
    (hr.after_local (run_rtg hv))
  have hwAt' : At w 3418 ((firstGeometrySync l g stage ++ firstGeometryFacts p batch tile stage) ++
      F) := by
    rw [List.append_assoc]
    obtain ⟨hInput, hGeom⟩ := (holds_append ..).mp hwAt.2.2.2.2
    obtain ⟨hSync, hFrame⟩ := (holds_append ..).mp hInput
    exact hwAt.mono ((holds_append ..).mpr ⟨hSync, (holds_append ..).mpr ⟨hGeom, hFrame⟩⟩)
  obtain ⟨fails, u, hEvents, huAt, hu⟩ := firstGeometryAckTraceFramed hp stage hb hTile hF hwAt' hw
  exact ⟨fails, u, hReads, hEvents, huAt, hu⟩

/-- Protected opening metadata loads occur in a maximal trace at the selected cursor. -/
theorem geometryReadsOfMaximal (hMax : Maximal l kernel Assumptions.all m X) {g j batch tile : Nat}
    (hg : g < l.threads) (stage : Fin 2) (hb : batch < p.batch) {F : List (Nat × Value)}
    (hF : ∀ x ∈ F, x.1 ∈ firstGeometryCarryRegs) (hTile : 256*tile < p.qLength batch) {s t : TState}
    {ending : Option TState} (ht : At t 3369 (geometryReadOperands p batch tile stage ++ F))
    (hCuQ : ∀ off ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase+4*(batch+off))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*batch)).at k))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some s))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop j) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t) (hPos : 0 < j)
    (hBound : j ≤ (X.tr g).length) (hRelease : j = (X.tr g).length → Step.Released l X g) :
    ∃ last u, At u 3418 (F ++ firstGeometryFacts p batch tile stage) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+3)) (some last) ∧
      Run kernel Assumptions.all l g last ((X.tr g).drop (j+3)) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) last u ∧
      FirstGeometryReads p X g j batch := by
  have hQ := hp.alignment.2.2.2.2.2.2.2.2.1
  have hK := hp.alignment.2.2.2.2.2.2.2.2.2.1
  have hCuRange := hp.ranges ⟨p.cuQBase, 4*(p.batch+1)⟩ (by simp [Params.inputRegions])
  have hKRange := hp.ranges ⟨p.usedKBase, 4*p.batch⟩ (by simp [Params.inputRegions])
  change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hCuRange
  change p.usedKBase+4*p.batch ≤ 2^64 at hKRange
  have hSafe (pair : Nat × Value) (hm : pair ∈ F) :
      pair.1 ≠ 2848 ∧ pair.1 ≠ 2849 ∧ pair.1 ≠ 1224 := by
    have hAudit : firstGeometryCarryRegs.all
        (fun r => decide (r ≠ 2848 ∧ r ≠ 2849 ∧ r ≠ 1224)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp hAudit pair.1 (hF pair hm))
  let qBase := p.cuQBase+4*batch
  let kBase := p.usedKBase+4*batch
  have hEq : qBase + (geometryReadSite 1).off = p.cuQBase+4*(batch+1) := by
    dsimp only [qBase, geometryReadSite]
    omega
  obtain ⟨u0, hE0, hAfter0, hPast0, hR0⟩ :=
    Mma.wordReadOfMaximal hMax hg (addr := qBase) (word := p.qOffset batch) (geometryReadSite 0)
      (geometryReadCode 0) ht
      (by simp [geometryReadOperands, geometryReadSite, qBase])
      (by dsimp [qBase, geometryReadSite]; omega) (by dsimp [qBase, geometryReadSite]; omega)
      (hp.cuQ _ hb.le)
      (by simpa only [qBase, geometryReadSite, Nat.add_zero] using hCuQ 0 (by decide))
      (by
        intro pair hh
        simp only [geometryReadOperands, List.cons_append, List.nil_append, List.mem_cons] at hh
        rcases hh with rfl | rfl | rfl | rfl | rfl | hm
        · exact of_decide_eq_true rfl
        · exact of_decide_eq_true rfl
        · exact of_decide_eq_true rfl
        · exact of_decide_eq_true rfl
        · exact of_decide_eq_true rfl
        · exact (hSafe pair hm).1)
      hPrefix hr hLocal hPos hBound hRelease
  obtain ⟨u1, hE1, hAfter1, hPast1, hR1⟩ :=
    Mma.wordReadOfMaximal hMax hg (addr := qBase) (word := p.qOffset (batch+1)) (geometryReadSite 1)
      (geometryReadCode 1) hAfter0
      (by simp [geometryReadOperands, geometryReadSite, qBase]) (by rw [hEq]; omega)
      (by rw [hEq]; omega) (by rw [hEq]; exact hp.cuQ _ (by omega))
      (by rw [hEq]; exact hCuQ 1 (by decide))
      (by
        intro pair hh
        simp only [geometryReadOperands, List.cons_append, List.nil_append, List.mem_cons] at hh
        rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | hm <;>
          first | exact of_decide_eq_true rfl | exact (hSafe pair hm).2.1)
      hPast0 hR0 .refl (Nat.succ_pos _) (len_of_get hE0)
      (Prologue.releasedIfLast hE0 (by intro h; cases h))
  have hAfter1Regs := hAfter1.2.2.2.2
  change Holds _ (((2849, b32 (p.qOffset (batch+1))) ::
    (2848, b32 (p.qOffset batch)) :: geometryReadOperands p batch tile stage) ++ F) at hAfter1Regs
  obtain ⟨hArgs,hKeep⟩ := (holds_append _ _ _).mp hAfter1Regs
  obtain ⟨v, hvRun, hKey⟩ :=
    (usedKAddress hp g batch tile stage hb (by omega)).apply (hAfter1.mono hArgs)
  have hKeyKeep := Epilogue.holdsSchedulerFrame hKeep (geometryAddressFrame true hAfter1.1 hvRun)
    hF
  have hv : At v 3373 (keyReadEntry p batch tile stage ++ F) :=
    hKey.mono ((holds_append ..).mpr ⟨hKey.2.2.2.2,hKeyKeep⟩)
  obtain ⟨u2, hE2, hAfter2, hPast2, hR2⟩ :=
    Mma.wordReadOfMaximal hMax hg (addr := kBase) (word := p.kLength batch) (geometryReadSite 2)
      (geometryReadCode 2) hv (by simp [geometryReadSite, keyReadEntry, kBase])
      (by dsimp [kBase, geometryReadSite]; omega) (by dsimp [kBase, geometryReadSite]; omega)
      (hp.usedK _ hb) hUsedK
      (by
        intro pair hh
        simp only [keyReadEntry, List.cons_append, List.nil_append, List.mem_cons] at hh
        rcases hh with rfl | rfl | rfl | rfl | hm <;>
          first | exact of_decide_eq_true rfl | exact (hSafe pair hm).2.2)
      hPast1 hR1 (run_rtg hvRun) (Nat.succ_pos _) (len_of_get hE1)
      (Prologue.releasedIfLast hE1 (by intro h; cases h))
  have hIndex : j + 1 + 1 + 1 = j + 3 := by omega
  rw [hIndex] at hPast2 hR2
  have hGeometry : At u2 3374
      (firstGeometryInput p batch tile stage) :=
    hAfter2.mono (by
      refine ⟨holds_mem hAfter2.2.2.2.2 (by simp [keyReadEntry]),
        holds_mem hAfter2.2.2.2.2 (by simp [geometryReadSite]),
        holds_mem hAfter2.2.2.2.2 (by simp [keyReadEntry]),
        holds_mem hAfter2.2.2.2.2 (by simp [keyReadEntry]), trivial⟩)
  obtain ⟨u, huRun, hu⟩ := (firstGeometrySegment hp g batch tile stage hb hTile).apply hGeometry
  have hFrame := geometryFrame (keep := firstGeometryCarryRegs) (by decide) (by decide) hGeometry.1
    (by set_option maxRecDepth 100000 in kernel_rfl) huRun
  have hAfter2Regs := hAfter2.2.2.2.2
  change Holds _ (((1224, b32 (p.kLength batch)) :: keyReadEntry p batch tile stage) ++ F)
    at hAfter2Regs
  have hSync := Epilogue.holdsSchedulerFrame ((holds_append _ _ _).mp hAfter2Regs).2 hFrame hF
  change qBase + 4 = p.cuQBase+4*(batch+1) at hEq
  exact ⟨u2, u, hu.mono ((holds_append _ _ _).mpr ⟨hSync, hu.2.2.2.2⟩),
    hPast2, hR2, run_rtg huRun, hE0, by simpa only [hEq, geometryReadSite] using hE1, hE2⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
