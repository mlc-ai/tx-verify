-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingInputCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryCredits
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingBiasWarp
import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingPrefixCoordinates
import Lemmas.Flow.TensorLoadFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Epilogue Prologue Thread.Loader

private def queryIssueSite (stage plane : Fin 2) : Fin 14 :=
  ⟨4 * stage.val + plane.val, by have := stage.isLt; have := plane.isLt; omega⟩

private theorem querySubboxEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {spec : TensorCopy.Spec} {stage plane : Fin 2}
    (hBox : QuerySubbox p l X i stage plane spec) :
    X.get i = some ⟨(inputSite (queryIssueSite stage plane)).pc,
      .tensorIssue p.qMapAddress spec⟩ := by
  obtain ⟨_, he⟩ := hBox.1
  obtain ⟨j, rfl⟩ := actualInputIssuePc hX he
  have hDst := (actualInputBoxAt hp hX j he).2.2.2.1
  have hOff := congrArg Loc.addr (hDst.symm.trans hBox.2.2.1)
  change l.sharedBase + (inputSite j).sharedOffset =
    Mma.qStart l stage + 16384 * plane.val at hOff
  simp only [Mma.qStart, Nat.add_assoc, Nat.add_left_cancel_iff] at hOff
  have hJ : j = queryIssueSite stage plane := by
    fin_cases stage <;> fin_cases plane <;> fin_cases j <;>
      first | rfl | simp [inputSite] at hOff
  subst j
  exact he

private def queryCoordinateFrame (l : Launch) (warp : Fin 2) (row head : Nat) :
    List (Nat × Value) :=
  [(1087, b32 row), (7169, b32 head), (2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]

private def queryCoordinateSteps (stage : Fin 2) : Nat := if stage.val = 0 then 1 else 3

private def queryCoordinateSetup (stage plane : Fin 2) : Nat :=
  (inputSite (queryIssueSite stage plane)).pc - queryCoordinateSteps stage

private def queryIssueFrame (l : Launch) (warp stage plane : Fin 2) (row head : Nat) :
    List (Nat × Value) :=
  let site := inputSite (queryIssueSite stage plane)
  [(site.colReg, b32 (64 * plane.val)), (site.rowReg, b32 (row + 128 * stage.val)),
    (7169, b32 head), (2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]

private theorem queryCoordinateSetupCore {l : Launch} {g row head : Nat}
    (warp stage plane : Fin 2) (hRow : row + 128 < 2 ^ 32) :
    Seg kernel [] l g (queryCoordinateSteps stage) (queryCoordinateSetup stage plane)
      (queryCoordinateFrame l warp row head) (inputSite (queryIssueSite stage plane)).pc
      (queryIssueFrame l warp stage plane row head) := by
  fin_cases stage <;> fin_cases plane
  all_goals
    dsimp [queryCoordinateSteps, queryCoordinateSetup, queryCoordinateFrame,
      queryIssueFrame, queryIssueSite, inputSite]
    intro t ht
    seg_fp ht using norm_bits

private theorem queryCoordinateSource {l : Launch} {g row head address : Nat}
    (warp stage plane : Fin 2) {t : TState} {es : List Event} {visits : List Visit}
    {spec : TensorCopy.Spec}
    (hRow : row + 128 < 2 ^ 32)
    (hAt : At t 488 (queryCoordinateFrame l warp row head))
    (hw : Walk kernel Assumptions.all l g t es visits)
    (he : (⟨(inputSite (queryIssueSite stage plane)).pc, .tensorIssue address spec⟩ : Event)
      ∈ es) :
    let site := inputSite (queryIssueSite stage plane)
    ∃ s u, EStep kernel Assumptions.all l g s ⟨site.pc, .tensorIssue address spec⟩ (some u) ∧
      Holds s.regs (queryIssueFrame l warp stage plane row head) := by
  dsimp only
  let site := inputSite (queryIssueSite stage plane)
  let e : Event := ⟨site.pc, .tensorIssue address spec⟩
  let stop := site.pc + 1
  let cut := queryCoordinateSetup stage plane
  let n := queryCoordinateSteps stage
  have hStop : 174 ≤ stop ∧ stop ≤ 1901 := by fin_cases stage <;> fin_cases plane <;> decide
  have hCut : 488 ≤ cut ∧ cut + n = site.pc := by fin_cases stage <;> fin_cases plane <;> decide
  have hSteps : 0 < n := by fin_cases stage <;> decide
  have hTail (bound : Nat) : ((kernel.code.drop stop).take (1901 - stop)).all
      (fun i => loaderPipelineCutOp stop 1901 bound [2535, 1062] i.op) = true := by
    fin_cases stage <;> fin_cases plane <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hHi : e.pc < stop := Nat.lt_succ_self _
  have hCont : ¬ Ends e := by simp [e, Ends]
  have hSlice := loaderEventInClosedSlice warp hStop.1 hStop.2 hTail hw
    (by rw [hAt.1]; decide) (ringShapeOfAt hAt) hAt.2.2.2.2.2.2 he hHi
  have hAudit : ((kernel.code.drop 488).take (cut - 488)).all
      (fun i => loaderPipelineCutOp 488 cut (stop - 1)
        ((queryCoordinateFrame l warp row head).map Prod.fst) i.op) = true := by
    fin_cases stage <;> fin_cases plane <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hInsn : ∃ ins, kernel.code[cut]? = some ins ∧ ins.op.isLocal = true := by
    fin_cases stage <;> fin_cases plane
    · exact ⟨_, Flow.code_692, rfl⟩
    · exact ⟨_, Flow.code_699, rfl⟩
    · exact ⟨_, Flow.code_742, rfl⟩
    · exact ⟨_, Flow.code_750, rfl⟩
  obtain ⟨v, _, tail, _, vs, _, _, _, hv, hvShape, hvFrame, _, hvWalk, hvSaw⟩ :=
    loaderObservedCut (by decide : 174 ≤ 488) (by decide : 174 ≤ 488)
      (show cut ≤ 1901 by omega) (show cut < stop by omega) hAudit hw
      ⟨hAt.1.symm ▸ le_rfl, hAt.1.symm ▸ hCut.1⟩
      (ringShapeOfAt hAt) hAt.2.2.2.2 hSlice (show cut ≤ e.pc by change cut ≤ site.pc; omega)
      hCont
  have hMem := memEventsOfLoaderSlice hvWalk hvSaw
  have hV := pipelineAtCut hv hvShape hvFrame
    (walkWithContinuingEventClean hvWalk hMem hCont) hInsn
  obtain ⟨u, hu, hU⟩ := (queryCoordinateSetupCore (g := g) warp stage plane hRow).apply hV
  have hStraight : ((kernel.code.drop cut).take (n - 1)).all
      (fun i => schedulerFallsThrough i.op) = true := by
    fin_cases stage <;> fin_cases plane <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have huA := (loaderLinear (regs := []) (show 174 ≤ cut by omega) (show cut + n ≤ 1906 by omega)
    hV.1 (List.all_eq_true.mpr (fun _ _ => rfl)) hStraight hu).1
  obtain ⟨_, hWalk⟩ := loaderWalkAfterLocals hvWalk (List.ne_nil_of_mem hMem) (run_rtg huA)
  have hLast := loaderEventInClosedSlice warp hStop.1 hStop.2 hTail hWalk
    (by rw [hU.1]; change 174 ≤ site.pc ∧ site.pc ≤ 1901; omega)
    (ringShapeOfAt hU) hU.2.2.2.2.2.2.2 hMem hHi
  have hStable : ((kernel.code.drop site.pc).take (stop - site.pc)).all
      (fun i => loaderPipelineCutOp site.pc stop (stop - 1)
        ((queryIssueFrame l warp stage plane row head).map Prod.fst) i.op) = true := by
    fin_cases stage <;> fin_cases plane <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨s, u', _, hF, hStep⟩ := loaderEventWithRegisters
    (show 174 ≤ site.pc by omega) (show 174 ≤ site.pc by omega) hStop.2 hStable hWalk
    (by rw [hU.1]) (ringShapeOfAt hU) hU.2.2.2.2 hLast hCont
  exact ⟨s, u', hStep, hF⟩

/-- Each actual Q box uses the assigned packed query row and head, with its own column plane. -/
theorem querySubboxCoordinatesInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {batch : Nat} {i : EvId} {stage plane : Fin 2} {spec : TensorCopy.Spec}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ i.1 / l.block)
    (hHi : i.1 / l.block < tilePrefix p (batch + 1) * p.heads)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hBox : QuerySubbox p l X i stage plane spec) :
    let coords := assignedCoordinates p batch (i.1 / l.block)
    spec = qInputSpec p (64 * plane.val) (p.qOffset batch + 256 * coords.1 + 128 * stage.val)
      coords.2 ⟨.shared, i.1 / l.block, Mma.qStart l stage + 16384 * plane.val⟩
      (Thread.Output.queryObject l (i.1 / l.block) stage) false := by
  dsimp only
  let coords := assignedCoordinates p batch (i.1 / l.block)
  let row := p.qOffset batch + 256 * coords.1
  let site := inputSite (queryIssueSite stage plane)
  have he := querySubboxEvent hp hX hBox
  have hThread := event_thread_lt hX he
  have hBounds : 385 < site.pc ∧ site.pc < 1744 ∧ site.pc ∉ registerHintSites := by
    fin_cases stage <;> fin_cases plane <;> decide
  have hEarly : 173 < site.pc := (show 173 < 385 by decide).trans hBounds.1
  have hWarp : 14 ≤ warpIndex l i.1 := by
    have hFinish := hBounds.2.1
    have hRole := roleBodyPcOfEvent hp hX he hEarly hBounds.2.2
    change roleBodyPc (warpIndex l i.1) site.pc at hRole
    rcases hRole with h | h
    · change site.pc = 9205 at h
      omega
    · split_ifs at h <;> omega
  let warp : Fin 2 := ⟨warpIndex l i.1 - 14,by have := warpIndex_lt hp i.1; omega⟩
  have hWarpEq : warpIndex l i.1 = 14+warp.val := by dsimp [warp]; omega
  let lane := laneOf l i.1
  have hLane : warpLane l i.1 lane = i.1 :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hLaneLt : lane < 32 := Nat.mod_lt _ (by decide)
  have hActive : i.1/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right p.heads
      (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨actual,hIn,hLow,hHigh,pos,hPos,t,ending,hStart,hRun,_⟩ :=
    loaderPrimingMetadataOfActiveEvent hp hX hThread hWarp hLaneLt writes hActive
      (by rw [hLane]; exact he) hBounds.1
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hActive
  have hBatch : actual = batch := (hUnique actual ⟨hIn,hLow,hHigh⟩).trans
    (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst actual
  rw [hLane] at hRun
  rw [hWarpEq] at hStart
  obtain ⟨hTile,hHead⟩ := assignedCoordinates_valid hp hLo hHi
  obtain ⟨u,hSteps,hAt⟩ := primingKActiveToAddressLane hp hb hTile hStart
  obtain ⟨_,v,hV,hScratch⟩ :=
    primingVAdmissionWithTripsLane hp hb (hHead.trans hp.heads_signed) hTile hLaneLt hAt
  have hTail : (⟨site.pc,.tensorIssue p.qMapAddress spec⟩ : Event) ∈ (X.tr i.1).drop pos := by
    apply List.mem_of_getElem? (i := i.2 - pos)
    rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
    exact he
  have hReplay := hRun.after_local_nonempty (hSteps.trans hV) (List.ne_nil_of_mem hTail)
  have hFrame : At v 488 (queryCoordinateFrame l warp row coords.2) := by
    have hHeld := (holds_append ..).mp hScratch.2.2.2.2
    have hCarry := ((holds_append ..).mp hHeld.1).2
    have hTrip := hHeld.2
    apply hScratch.mono
    simp only [queryCoordinateFrame,Holds]
    exact ⟨holds_mem hTrip (by simp [primingVTripFrame,row,coords]),
      holds_mem hTrip (by simp [primingVTripFrame,coords]),
      holds_mem hCarry (by simp [primingVAdmissionCarry]),
      holds_mem hTrip (by simp [primingVTripFrame]),trivial⟩
  have hPacked : row < p.totalQ := hp.packedRow_lt hb hTile
  have hFit := hp.shape.2.2.2.2.2
  have hStage := stage.isLt
  have hPlane := plane.isLt
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun hReplay
  obtain ⟨s, u, hStep, hRegs⟩ :=
    queryCoordinateSource warp stage plane (by omega) hFrame hWalk hTail
  obtain ⟨ins, hCode, _, hFire⟩ := estep_event_source hStep
  rw [(estep_source_pc hStep).symm, inputSiteCode] at hCode
  obtain rfl := Option.some.inj hCode
  have hCol : s.regs site.colReg = some (b32 (64 * plane.val)) := hRegs.1
  have hRow : s.regs site.rowReg = some (b32 (row + 128 * stage.val)) := hRegs.2.1
  have hHeadReg : s.regs 7169 = some (b32 coords.2) := hRegs.2.2.1
  have hH31 : coords.2 < 2 ^ 31 := hHead.trans hp.heads_signed
  have hRead : [.reg site.colReg, .reg site.rowReg, .reg 7169].mapM
      (readBits l i.1 s 32) = .ok [BitVec.ofNat 64 (64 * plane.val),
        BitVec.ofNat 64 (row + 128 * stage.val), BitVec.ofNat 64 coords.2] := by
    simp only [List.mapM_cons, List.mapM_nil, readBits_b32 hCol (by omega),
      readBits_b32 hRow (by omega), readBits_b32 hHeadReg (by omega), bind, Except.bind,
      pure, Except.pure]
  have hOrigin := tensorLoadCopy_origin_all (fires_cpTensor_copy hFire rfl) hRead
  have hBit {x : Nat} (hx : x < 2 ^ 31) :
      (BitVec.ofNat 32 (BitVec.ofNat 64 x).toNat).toInt = (x : Int) := by
    rw [toNat_ofNat_lt (by omega : x < 2 ^ 64)]
    exact toInt_ofNat_lt32 hx
  obtain ⟨_, hBar, hShared, hDesc, hRows, hCluster, hGroup⟩ := hBox
  rcases spec with ⟨⟨outer, desc, origin, sharedBase, rows⟩, barrier, cluster, group⟩
  have hOuter : outer = 2 := congrArg Sigma.fst hDesc
  subst outer
  cases hDesc
  dsimp only at hShared hBar hRows hCluster hGroup
  subst sharedBase barrier rows cluster group
  have hCoords : origin = inputCoordinate (64 * plane.val) (row + 128 * stage.val) coords.2 := by
    funext axis
    dsimp only at hOrigin
    rw [hOrigin axis]
    fin_cases axis
    · exact hBit (by omega)
    · exact hBit (by omega)
    · exact hBit hH31
  subst origin
  rfl

end PTX.Kernels.TmlFa4Fwd.Loader
