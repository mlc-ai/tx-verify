-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderFirstBiasOrigins
public import Kernels.TmlFa4Fwd.Proof.LoaderSingleBiasVisit
import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasTensorOrdinal
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingPrefixCoordinates
import Kernels.TmlFa4Fwd.Proof.LoaderBiasTensorActor
import Lemmas.Flow.NthEv
import Lemmas.Flow.TensorLoadFacts
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Epilogue Protocol.Bias Softmax Thread.Loader

/-- A priming Bias issue reads the three coordinates from its actual source registers.
The observed descriptor comes from the matching acquire. -/
theorem firstBiasBoxAtIssueRegisters {p : Params} {l : Launch} {X : Execution}
    {g wait col row head : Nat} {tensor : EvId} {stage half : Fin 2}
    {o : TensorCopy.Observation} {t u : TState}
    (hBox : AcquiredBiasBox p l X stage g wait tensor half o)
    (hStep : EStep kernel Assumptions.all l tensor.1 t
      ⟨(inputSite (firstBiasIssueSite stage half)).pc, .tensorIssue p.biasMapAddress o.spec⟩
      (some u))
    (hCol : t.regs (inputSite (firstBiasIssueSite stage half)).colReg = some (b32 col))
    (hRow : t.regs (inputSite (firstBiasIssueSite stage half)).rowReg = some (b32 row))
    (hHead : t.regs 7169 = some (b32 head))
    (hc : col < 2 ^ 31) (hr : row < 2 ^ 31) (hh : head < 2 ^ 31) :
    FirstBiasBox p l X stage g wait col row head half tensor := by
  let site := inputSite (firstBiasIssueSite stage half)
  change t.regs site.colReg = some (b32 col) at hCol
  change t.regs site.rowReg = some (b32 row) at hRow
  have hPc : t.pc = site.pc := (estep_source_pc hStep).symm
  obtain ⟨ins, hCode, _, hFires⟩ := estep_event_source hStep
  rw [hPc, inputSiteCode] at hCode
  obtain rfl := Option.some.inj hCode
  have hCopy := fires_cpTensor_copy hFires rfl
  have hRead : [.reg site.colReg, .reg site.rowReg, .reg 7169].mapM
      (readBits l tensor.1 t 32) = .ok [BitVec.ofNat 64 col, BitVec.ofNat 64 row,
        BitVec.ofNat 64 head] := by
    simp only [List.mapM_cons, List.mapM_nil, readBits_b32 hCol (by omega),
      readBits_b32 hRow (by omega), readBits_b32 hHead (by omega), bind, Except.bind,
      pure, Except.pure]
  have hDecode := tensorLoadCopy_origin_all hCopy hRead
  have hBit {n : Nat} (hn : n < 2 ^ 31) :
      (BitVec.ofNat 32 (BitVec.ofNat 64 n).toNat).toInt = (n : Int) := by
    rw [toNat_ofNat_lt (by omega : n < 2 ^ 64)]
    exact toInt_ofNat_lt32 hn
  apply hBox.firstBiasBox
  rcases o with ⟨⟨⟨outer, descriptor, origin, base, rows⟩, barrier, cluster, group⟩, effects⟩
  have hRank : outer = 2 := congrArg Sigma.fst hBox.descriptor
  subst outer
  congr 1
  funext axis
  rw [hDecode axis]
  fin_cases axis
  · exact hBit hc
  · exact hBit hr
  · exact hBit hh

private def biasCoordinateRoots (l : Launch) (warp : Fin 2) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]

private def biasCoordinateRowReg : Fin 2 → Nat
  | 0 => 1087
  | 1 => 1115

private def biasCoordinateFrame (l : Launch) (warp stage : Fin 2) (row head : Nat) :
    List (Nat × Value) :=
  [(biasCoordinateRowReg stage, b32 row), (7169, b32 head), (1090, b32 0)] ++
    biasCoordinateRoots l warp

private def biasSetColumnPc (stage half : Fin 2) : Nat :=
  if stage.val = 0 then firstBiasPrepPc stage half
  else (inputSite (firstBiasIssueSite stage half)).pc - 1

private def biasSetColumnSteps (stage : Fin 2) : Nat :=
  if stage.val = 0 then 2 else 1

private theorem biasUpperRow {l : Launch} {g row head : Nat} (warp : Fin 2)
    (hRow : row + 128 < 2 ^ 32) :
    Seg kernel [] l g 1 764 (biasCoordinateFrame l warp 0 row head)
      765 (biasCoordinateFrame l warp 1 (row + 128) head) := by
  intro t ht
  simp only [biasCoordinateFrame, biasCoordinateRowReg, biasCoordinateRoots,
    List.cons_append, List.nil_append] at ht ⊢
  seg_fp ht using norm_bits

private theorem biasSetColumn {l : Launch} {g row head : Nat} (warp stage half : Fin 2) :
    let site := inputSite (firstBiasIssueSite stage half)
    Seg kernel [] l g (biasSetColumnSteps stage) (biasSetColumnPc stage half)
      (biasCoordinateFrame l warp stage row head)
      (biasSetColumnPc stage half + biasSetColumnSteps stage)
      ((site.colReg, b32 (firstVisitBiasBoxColumn half)) ::
        biasCoordinateFrame l warp stage row head) := by
  fin_cases stage <;> fin_cases half
  all_goals
    dsimp [firstBiasIssueSite, inputSite, firstBiasPrepPc, firstBiasPrepSteps, biasSetColumnPc,
      biasSetColumnSteps, biasCoordinateFrame, biasCoordinateRowReg, biasCoordinateRoots,
      firstVisitBiasBoxColumn]
    intro t ht
    seg_fp ht using rfl

private theorem primingBiasCut {l : Launch} {g start cut stop : Nat} {t : TState}
    {es : List Event} {vs : List Visit} {F : List (Nat × Value)} {event : Event}
    (hAt : At t start F) (hStart : 174 ≤ start ∧ start ≤ cut) (hLimit : cut ≤ 1901)
    (hCut : cut < stop) (hCode : ((kernel.code.drop start).take (cut - start)).all
      (fun i => loaderPipelineCutOp start cut (stop - 1) (F.map Prod.fst) i.op) = true)
    (hInsn : ∃ ins, kernel.code[cut]? = some ins ∧ ins.op.isLocal = true)
    (hw : Walk kernel Assumptions.all l g t es vs) (he : event ∈ loaderSliceEvents 174 stop vs)
    (hLo : cut ≤ event.pc) (hCont : ¬ Ends event) :
    ∃ u tail visits, At u cut F ∧ Walk kernel Assumptions.all l g u tail visits ∧
      event ∈ loaderSliceEvents 174 stop visits := by
  obtain ⟨u, _, tail, _, visits, _, _, _, hu, hShape, hFrame, _, hTail, hSaw⟩ :=
    loaderObservedCut hStart.1 hStart.1 hLimit hCut hCode hw
      ⟨hAt.1.symm ▸ le_rfl, hAt.1.symm ▸ hStart.2⟩
      (ringShapeOfAt hAt) hAt.2.2.2.2 he hLo hCont
  exact ⟨u, tail, visits, pipelineAtCut hu hShape hFrame
    (walkWithContinuingEventClean hTail (memEventsOfLoaderSlice hTail hSaw) hCont) hInsn, hTail,
    hSaw⟩

private theorem biasRowOfPrimingCursor {l : Launch} {g row head stop : Nat}
    (warp stage : Fin 2) {t : TState} {es : List Event} {visits : List Visit} {event : Event}
    (hRow : row + 128 < 2 ^ 32) (hAt : At t 488 (biasCoordinateFrame l warp 0 row head))
    (hw : Walk kernel Assumptions.all l g t es visits)
    (he : event ∈ loaderSliceEvents 174 stop visits) (hCont : ¬ Ends event)
    (hTail : ∀ bound, ((kernel.code.drop stop).take (1901 - stop)).all
      (fun i => loaderPipelineCutOp stop 1901 bound [2535, 1062] i.op) = true)
    (hHi : event.pc < stop) (hStop : stop ≤ 1901)
    (hUpper : stage.val = 1 → 764 ≤ event.pc ∧
      ((kernel.code.drop 488).take (764 - 488)).all
        (fun i => loaderPipelineCutOp 488 764 (stop - 1)
          [1087, 7169, 1090, 2535, 1062] i.op) = true) :
    ∃ u tail vs,
      At u (if stage.val = 0 then 488 else 765)
        (biasCoordinateFrame l warp stage (row + 128 * stage.val) head) ∧
      Walk kernel Assumptions.all l g u tail vs ∧ event ∈ loaderSliceEvents 174 stop vs := by
  fin_cases stage
  · exact ⟨t, es, visits, hAt, hw, he⟩
  obtain ⟨hLo, hAudit⟩ := hUpper rfl
  obtain ⟨s, es', ws, hS, hW, hSaw⟩ := primingBiasCut hAt (by decide) (by decide)
    (by omega : 764 < stop) hAudit ⟨_, Flow.code_764, rfl⟩ hw he hLo hCont
  obtain ⟨u, hu, hU⟩ := (biasUpperRow (g := g) warp hRow).apply hS
  have huA := (loaderLinear (regs := []) (by decide) (by decide) hS.1 (by simp) rfl hu).1
  have hMem := memEventsOfLoaderSlice hW hSaw
  obtain ⟨vs, hW'⟩ := loaderWalkAfterLocals hW (List.ne_nil_of_mem hMem) (run_rtg huA)
  have hSlice := loaderEventInClosedSlice warp (by omega) hStop hTail
    hW' (by rw [hU.1]; decide) (ringShapeOfAt hU) hU.2.2.2.2.2.2.2 hMem hHi
  exact ⟨u, es', vs, hU, hW', hSlice⟩

/-- The four real first Bias issues recover their source frame from the packed-row cursor. -/
private theorem primingBiasCoordinateSource {l : Launch} {g row head address : Nat}
    (warp stage half : Fin 2) {t : TState} {es : List Event} {visits : List Visit}
    {spec : TensorCopy.Spec}
    (hRow : row + 128 < 2 ^ 32)
    (hAt : At t 488 (biasCoordinateFrame l warp 0 row head))
    (hw : Walk kernel Assumptions.all l g t es visits)
    (he : (⟨(inputSite (firstBiasIssueSite stage half)).pc, .tensorIssue address spec⟩ : Event)
      ∈ es) :
    let site := inputSite (firstBiasIssueSite stage half)
    ∃ s u, EStep kernel Assumptions.all l g s ⟨site.pc, .tensorIssue address spec⟩ (some u) ∧
      s.regs site.colReg = some (b32 (firstVisitBiasBoxColumn half)) ∧
      s.regs site.rowReg = some (b32 (row + 128 * stage.val)) ∧
      s.regs 7169 = some (b32 head) := by
  dsimp only
  let site := inputSite (firstBiasIssueSite stage half)
  let event : Event := ⟨site.pc, .tensorIssue address spec⟩
  let stop := site.pc + 1
  let start := if stage.val = 0 then 488 else 765
  let cut := biasSetColumnPc stage half
  let n := biasSetColumnSteps stage
  let F := biasCoordinateFrame l warp stage (row + 128 * stage.val) head
  let G := (site.colReg, b32 (firstVisitBiasBoxColumn half)) :: F
  have hStart : 174 ≤ start ∧ start ≤ cut := by fin_cases stage <;> fin_cases half <;> decide
  have hStop : 174 ≤ stop ∧ stop ≤ 1901 := by fin_cases stage <;> fin_cases half <;> decide
  have hCut : cut + n ≤ site.pc := by fin_cases stage <;> fin_cases half <;> decide
  have hPositive : 0 < n := by fin_cases stage <;> decide
  have hTail (bound : Nat) : ((kernel.code.drop stop).take (1901 - stop)).all
      (fun i => loaderPipelineCutOp stop 1901 bound [2535, 1062] i.op) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hHi : event.pc < stop := Nat.lt_succ_self _
  have hSlice := loaderEventInClosedSlice warp hStop.1 hStop.2 hTail hw
    (by rw [hAt.1]; decide) (ringShapeOfAt hAt) hAt.2.2.2.2.2.2.2 he hHi
  have hCont : ¬ Ends event := by simp [event, Ends]
  have hUpper : stage.val = 1 → 764 ≤ event.pc ∧
      ((kernel.code.drop 488).take (764 - 488)).all
        (fun i => loaderPipelineCutOp 488 764 (stop - 1)
          [1087, 7169, 1090, 2535, 1062] i.op) = true := by
    intro h
    have hs : stage = 1 := Fin.ext h
    subst stage
    fin_cases half
    · exact ⟨by change 764 ≤ 771; decide, by set_option maxRecDepth 100000 in kernel_rfl⟩
    · exact ⟨by change 764 ≤ 779; decide, by set_option maxRecDepth 100000 in kernel_rfl⟩
  obtain ⟨v, tail, vs, hV, hWalk, hSeen⟩ := biasRowOfPrimingCursor warp stage hRow hAt hw hSlice
    hCont hTail hHi hStop.2 hUpper
  have hAudit : ((kernel.code.drop start).take (cut - start)).all
      (fun i => loaderPipelineCutOp start cut (stop - 1) (F.map Prod.fst) i.op) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hInsn : ∃ ins, kernel.code[cut]? = some ins ∧ ins.op.isLocal = true := by
    fin_cases stage <;> fin_cases half
    · exact ⟨_, Flow.code_715, rfl⟩
    · exact ⟨_, Flow.code_723, rfl⟩
    · exact ⟨_, Flow.code_770, rfl⟩
    · exact ⟨_, Flow.code_778, rfl⟩
  obtain ⟨w, tail', vs', hW, hWalk', hSeen'⟩ := primingBiasCut hV hStart (by omega)
    (by dsimp [stop]; omega) hAudit hInsn hWalk hSeen (by change cut ≤ site.pc; omega) hCont
  obtain ⟨u, hu, hU⟩ := (biasSetColumn (g := g) (row := row + 128 * stage.val)
    (head := head) warp stage half).apply hW
  have hStraight : ((kernel.code.drop cut).take (n - 1)).all
      (fun i => schedulerFallsThrough i.op) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have huA := (loaderLinear (regs := []) (Nat.le_trans hStart.1 hStart.2) (by omega)
    hW.1 (List.all_eq_true.mpr (fun _ _ => rfl))
    hStraight hu).1
  have hMem := memEventsOfLoaderSlice hWalk' hSeen'
  obtain ⟨vs'', hLast⟩ := loaderWalkAfterLocals hWalk' (List.ne_nil_of_mem hMem) (run_rtg huA)
  have hLastSlice := loaderEventInClosedSlice warp hStop.1 hStop.2 hTail
    hLast (by rw [hU.1]; omega) (ringShapeOfAt hU) hU.2.2.2.2.2.2.2.2 hMem hHi
  have hStable : ((kernel.code.drop (cut + n)).take (stop - (cut + n))).all
      (fun i => loaderPipelineCutOp (cut + n) stop (stop - 1) (G.map Prod.fst) i.op) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨s, q, _, hF, hStep⟩ := loaderEventWithRegisters (F := G)
    (by omega) (by omega) hStop.2 hStable hLast (by rw [hU.1]) (ringShapeOfAt hU)
    hU.2.2.2.2 hLastSlice hCont
  have hRowReg : site.rowReg = biasCoordinateRowReg stage := by
    fin_cases stage <;> fin_cases half <;> rfl
  exact ⟨s, q, hStep, hF.1, hRowReg.symm ▸ hF.2.1, hF.2.2.1⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- An acquired priming Bias copy reads the selected query head and packed row,
with the first-visit physical column of its observed half. -/
theorem firstBiasBoxOfPrimingAcquireInPrefix {batch g wait : Nat} {stage half : Fin 2}
    {tensor : EvId} {o : TensorCopy.Observation} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hBox : AcquiredBiasBox p l X stage g wait tensor half o)
    (hPriming : ∃ pc < 780, X.get tensor = some ⟨pc,.tensorIssue p.biasMapAddress o.spec⟩) :
    let coords := assignedCoordinates p batch (g / l.block)
    FirstBiasBox p l X stage g wait (firstVisitBiasBoxColumn half)
      (p.qOffset batch + 128 * (2 * coords.1 + stage.val)) coords.2 half tensor := by
  dsimp only
  let coords := assignedCoordinates p batch (g / l.block)
  let row := p.qOffset batch + 256 * coords.1
  obtain ⟨producer, index⟩ := tensor
  obtain ⟨pc, hPriming, he⟩ := hPriming
  have hOwner : producer / l.block = g / l.block := hBox.owner
  have hPc := primingBiasSubboxPc hp hX hBox.subbox hPriming he
  rw [hPc] at he
  let lane := laneOf l producer
  have hLaneLt : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l producer lane = producer :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hWarp : Prologue.warpIndex l producer = 14 := biasTensorActorWarp hp hX hBox.subbox
  have hProducer := event_thread_lt hX he
  have hActive : producer/l.block < tilePrefix p p.batch*p.heads :=
    hOwner ▸ hHi.trans_le
      (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  have hAfterMetadata : 385 < (inputSite (firstBiasIssueSite stage half)).pc := by
    fin_cases stage <;> fin_cases half <;> decide
  obtain ⟨actual,hIn,hLow,hHigh,pos,hPos,s,ending,hStart,hRun,_⟩ :=
    loaderPrimingMetadataOfActiveEvent hp hX hProducer hWarp.ge hLaneLt writes hActive
      (by rw [hLane]; exact he) hAfterMetadata
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hActive
  have hBatch : actual = batch := (hUnique actual ⟨hIn,hLow,hHigh⟩).trans
    (hUnique batch ⟨hb,hOwner.symm ▸ hLo,hOwner.symm ▸ hHi⟩).symm
  subst actual
  rw [hLane] at hRun
  rw [hOwner,hWarp] at hStart
  obtain ⟨hTile,hHead⟩ := assignedCoordinates_valid hp hLo hHi
  obtain ⟨v,hV,hAt⟩ := primingKActiveToAddressLane hp hb hTile hStart
  obtain ⟨_,t,hT,hScratch⟩ :=
    primingVAdmissionWithTripsLane hp hb (hHead.trans hp.heads_signed) hTile hLaneLt hAt
  have hTail : (⟨(inputSite (firstBiasIssueSite stage half)).pc,
      .tensorIssue p.biasMapAddress o.spec⟩ : Event) ∈ (X.tr producer).drop pos := by
    apply List.mem_of_getElem? (i := index - pos)
    rw [List.getElem?_drop, Nat.add_sub_of_le hPos]
    exact he
  have hTrace := hRun.after_local_nonempty (hV.trans hT) (List.ne_nil_of_mem hTail)
  have hFrame : At t 488 (biasCoordinateFrame l 0 0 row coords.2) := by
    have hHeld := (holds_append ..).mp hScratch.2.2.2.2
    have hCarry := ((holds_append ..).mp hHeld.1).2
    have hTrip := hHeld.2
    apply hScratch.mono
    simp only [biasCoordinateFrame,biasCoordinateRowReg,biasCoordinateRoots,
      List.cons_append,List.nil_append,Holds]
    refine ⟨?_,?_,?_,?_,?_,trivial⟩
    · exact holds_mem hTrip (by simp [primingVTripFrame,row,coords])
    · exact holds_mem hTrip (by simp [primingVTripFrame,coords])
    · exact holds_mem hTrip (by simp [primingVTripFrame])
    · exact holds_mem hCarry (by simp [primingVAdmissionCarry])
    · exact holds_mem hTrip (by simp [primingVTripFrame])
  have hPacked : row < p.totalQ := hp.packedRow_lt hb hTile
  have hFit := hp.shape.2.2.2.2.2
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun hTrace
  obtain ⟨s, u, hStep, hCol, hRow, hHeadReg⟩ :=
    primingBiasCoordinateSource 0 stage half (by omega) hFrame hWalk hTail
  change FirstBiasBox p l X stage g wait (firstVisitBiasBoxColumn half)
    (p.qOffset batch + 128 * (2 * coords.1 + stage.val)) coords.2 half (producer, index)
  rw [show p.qOffset batch + 128 * (2 * coords.1 + stage.val) = row + 128 * stage.val by
    simp only [row, Nat.mul_add, ← Nat.mul_assoc]; omega]
  have hc := firstVisitBiasBoxColumnBounds half
  have hStage := stage.isLt
  exact firstBiasBoxAtIssueRegisters hBox hStep hCol hRow hHeadReg (by omega)
    (by omega) (hHead.trans hp.heads_signed)

/-- A generation-zero Bias transfer recovered from the history is an actual priming issue. -/
theorem firstBiasBoxOfOpeningAcquireInPrefix {batch g wait : Nat} {stage half : Fin 2}
    {tensor : EvId} {o : TensorCopy.Observation} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hBox : AcquiredBiasBox p l X stage g wait tensor half o)
    (hOrdinal : biasTensorOrdinal l X stage half tensor = 0) :
    let coords := assignedCoordinates p batch (g / l.block)
    FirstBiasBox p l X stage g wait (firstVisitBiasBoxColumn half)
      (p.qOffset batch + 128 * (2 * coords.1 + stage.val)) coords.2 half tensor := by
  obtain ⟨actor,index⟩ := tensor
  obtain ⟨pc,he⟩ := hBox.issue
  apply firstBiasBoxOfPrimingAcquireInPrefix hp hX hb hLo hHi writes hBox
  refine ⟨pc,?_,he⟩
  by_contra! hLater
  obtain ⟨k,hk,other,hEarlier⟩ :=
    primingBiasEarlierThanRepeated hp hX hBox.subbox he hLater
  obtain ⟨source,hSource⟩ := hEarlier.1
  let mark := biasTensorHalf l (actor/l.block) stage half
  have hMark : mark ⟨source,.tensorIssue p.biasMapAddress other⟩ = true :=
    decide_eq_true ⟨hEarlier.2.1,hEarlier.2.2.1⟩
  have hGrow := countP_take_succ (p := mark) hSource hMark
  have hLimit := countP_take_mono mark (X.tr actor) (show k + 1 ≤ index by omega)
  change ((X.tr actor).take index).countP mark = 0 at hOrdinal
  omega

/-- The priming Bias source in a complete execution. -/
theorem firstBiasBoxOfPrimingAcquire (_hComplete : Complete l X) {batch g wait : Nat}
    {stage half : Fin 2} {tensor : EvId} {o : TensorCopy.Observation} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hBox : AcquiredBiasBox p l X stage g wait tensor half o)
    (hPriming : ∃ pc < 780, X.get tensor = some ⟨pc,.tensorIssue p.biasMapAddress o.spec⟩) :
    let coords := assignedCoordinates p batch (g / l.block)
    FirstBiasBox p l X stage g wait (firstVisitBiasBoxColumn half)
      (p.qOffset batch + 128 * (2 * coords.1 + stage.val)) coords.2 half tensor := by
  exact firstBiasBoxOfPrimingAcquireInPrefix hp hX hb hLo hHi writes hBox hPriming

/-- The actual single-visit Bias copy uses a priming issue, so its source coordinates
follow from the priming cursor. -/
theorem singleVisitFirstBiasBoxOfAcquire (hComplete : Complete l X) {batch g wait : Nat}
    {stage half : Fin 2} {tensor : EvId} {o : TensorCopy.Observation} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 = 1)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hBox : AcquiredBiasBox p l X stage g wait tensor half o) :
    let coords := assignedCoordinates p batch (g / l.block)
    FirstBiasBox p l X stage g wait (firstVisitBiasBoxColumn half)
      (p.qOffset batch + 128 * (2 * coords.1 + stage.val)) coords.2 half tensor := by
  obtain ⟨pc, he⟩ := hBox.issue
  have hOwner := hBox.owner
  have hPriming := singleVisitInputIssueIsPriming hp hX hComplete hb
    (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi) (hOwner.symm ▸ hTrip) writes he
  exact firstBiasBoxOfPrimingAcquire hp hX hComplete hb hLo hHi writes hBox ⟨pc,hPriming,he⟩

end PTX.Kernels.TmlFa4Fwd.Loader
