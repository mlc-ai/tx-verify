-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseTripFrame
public import Kernels.TmlFa4Fwd.Proof.CorrectionTileIngress
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue Mma

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Protected request reads from the selected lane preserve the row and address through
the correction body to the final LSE checkpoint. -/
theorem correctionLseReadyFromSelected {g batch lane pos j : Nat} {t : TState} {o : Option TState}
    {target : Event} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (ht : At t 7932 (correctionActiveTileFacts p l g batch lane))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k))
    (hr : Run kernel Assumptions.all l (warpLane l g lane) t
      ((X.tr (warpLane l g lane)).drop pos) o) (hJ : pos ≤ j) (hPc : 9057 < target.pc)
    (he : X.get (warpLane l g lane, j) = some target) :
    let thread := warpLane l g lane
    let coords := assignedCoordinates p batch (g / l.block)
    ∃ s rest visits, At s 9057 (lseFootprintEntryFacts p l thread batch coords.2 coords.1) ∧
      Walk kernel Assumptions.all l thread s rest visits ∧ target ∈ rest ∧
      ∃ consumed, (X.tr thread).drop pos = consumed ++ rest ∧
        TraceReach kernel Assumptions.all l thread t consumed s := by
  let thread := warpLane l g lane
  let tile := (assignedCoordinates p batch (g / l.block)).1
  let head := (assignedCoordinates p batch (g / l.block)).2
  let F := [(1613, b32 (rowOf l thread)), (9605, b64 head),
    (7501, b64 p.lseStride), (7500, b64 p.lseBase)]
  have ⟨hTile, hHead⟩ : 256 * tile < p.qLength batch ∧ head < p.heads :=
    assignedCoordinates_valid hp hLo hHi
  have hLen : j < (X.tr thread).length := (List.getElem?_eq_some_iff.mp he).1
  have hNonempty {k : Nat} (hk : k ≤ j) : (X.tr thread).drop k ≠ [] := by
    intro h
    have he := List.drop_eq_nil_iff.mp h
    omega
  obtain ⟨u, huRun, hu⟩ := correctionInputRun hp hb ht
  have hU := hr.after_local_nonempty (run_rtg huRun) (hNonempty hJ)
  let H := correctionInputFacts p batch tile
  have hSave : Holds u.regs F := by
    have h := hu.2.2.2.2
    exact ⟨holds_lookup h (by rfl), holds_lookup h (by rfl), holds_lookup h (by rfl),
      holds_lookup h (by rfl), trivial⟩
  let carry := correctionTileGeometryFacts l thread true ++
    correctionActiveTileFacts p l g batch lane
  have hFacts : Holds u.regs (H ++ carry) := by
    simpa only [List.append_assoc] using hu.2.2.2.2
  have hUAt : At u 7955 (H ++ F) :=
    hu.mono ((holds_append _ _ _).2 ⟨((holds_append _ _ _).1 hFacts).1, hSave⟩)
  obtain ⟨v, hv, hV, h0, h1, h2, _, hTrip⟩ := correctionTripReadsReachFromSuffix hp hX hb hUAt
    (by
      intro rv hm
      have h := List.mem_map_of_mem (f := Prod.fst) hm
      intro h'
      simp only [F, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      omega)
    (by set_option maxRecDepth 100000 in kernel_rfl) hUsedK hU
    (.inr ⟨j, _, hJ, by omega, he⟩)
  have hNot0 : j ≠ pos := by
    intro h
    subst j
    have hEq := congrArg Event.pc (Option.some.inj (he.symm.trans h0))
    change target.pc = 7955 at hEq
    omega
  have hNot1 : j ≠ pos + 1 := by
    intro h
    subst j
    have hEq := congrArg Event.pc (Option.some.inj (he.symm.trans h1))
    change target.pc = 7956 at hEq
    omega
  have hNot2 : j ≠ pos + 2 := by
    intro h
    subst j
    have hEq := congrArg Event.pc (Option.some.inj (he.symm.trans h2))
    change target.pc = 7959 at hEq
    omega
  have hj : pos + 3 ≤ j := by omega
  let K := (1634, b32 (p.qOffset batch)) :: (1635, b32 (p.qLength batch)) :: F
  have hK : Holds v.regs K :=
    ⟨hv.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2⟩
  obtain ⟨w, hRun, hw⟩ := correctionTripAndRowWithFrame (F := K) hp thread hb hTile
    (by set_option maxRecDepth 100000 in kernel_rfl) v
    (hv.mono ⟨hv.2.2.2.2.1, hv.2.2.2.2.2.1, hv.2.2.2.2.2.2.1, hK⟩)
  have hwAt : At w 7985 (lseFootprintEntryFacts p l thread batch head tile) := by
    apply hw.mono
    have h := hw.2.2.2.2
    exact ⟨holds_lookup h (by rfl), holds_lookup h (by rfl), holds_lookup h (by rfl),
      holds_lookup h (by rfl), holds_lookup h (by rfl), holds_lookup h (by rfl),
      holds_lookup h (by rfl), trivial⟩
  have hW := hV.after_local_nonempty (run_rtg hRun) (hNonempty hj)
  obtain ⟨visits, hWalk⟩ := walkFromRun hW
  have he' : target ∈ (X.tr thread).drop (pos + 3) := by
    apply List.mem_of_getElem? (i := j - (pos + 3))
    rwa [List.getElem?_drop, Nat.add_sub_of_le hj]
  obtain ⟨s, es, vs, hs, hS, hEvent, consumed, hEq, hPath⟩ :=
    cutLseReadyFromLateEvent hPc hwAt hWalk he'
  let reads := ((X.tr thread).drop pos).take 3
  have hPrefix := (TraceReach.of_local (run_rtg huRun)).append hTrip
  have hReach : TraceReach kernel Assumptions.all l thread t reads w := by
    simpa only [List.nil_append, List.append_nil] using
      hPrefix.append (TraceReach.of_local (run_rtg hRun))
  have hTrace : (X.tr thread).drop pos = (reads ++ consumed) ++ es := by
    rw [List.append_assoc, ← hEq]
    have hSplit := List.take_append_drop 3 ((X.tr thread).drop pos)
    rw [List.drop_drop] at hSplit
    exact hSplit.symm
  exact ⟨s, es, vs, hs, hS, hEvent, reads ++ consumed, hTrace, hReach.append hPath⟩


omit hp hX in
/-- An LSE write belongs to its CTA's scheduled tile and its correction lane's row. -/
def AssignedLseFootprint (p : Params) (l : Launch) (cta g : Nat) (a : Acc) : Prop :=
  ∃ batch < p.batch, ∃ stage : Fin 2,
    tilePrefix p batch * p.heads ≤ cta ∧ cta < tilePrefix p (batch + 1) * p.heads ∧
    stageRow (assignedCoordinates p batch cta).1 stage + rowOf l g < p.qLength batch ∧
    a.loc = p.lseLoc (p.qOffset batch +
      (stageRow (assignedCoordinates p batch cta).1 stage + rowOf l g))
      (assignedCoordinates p batch cta).2 ∧ a.size = 4

omit hp hX in
theorem AssignedLseFootprint.toSpec {p : Params} {l : Launch} {m : Mem0} {cta g : Nat}
    (hp : Pre p l m) {a : Acc} (h : AssignedLseFootprint p l cta g a) :
    ∃ row < p.totalQ, ∃ head < p.heads, a.loc = p.lseLoc row head ∧ a.size = 4 := by
  obtain ⟨batch, hb, stage, hLo, hHi, hRow, hAddr, hSize⟩ := h
  exact ⟨_, hp.packedRow_lt hb hRow, _, (assignedCoordinates_valid hp hLo hHi).2, hAddr, hSize⟩

/-- An observed LSE write belongs to the selected lane's actual suffix.
The address frame requires the CuQ values while allowing any UsedK load result. -/
theorem correctionLseFootprintFromSelected {g batch lane pos j pc : Nat} {t : TState}
    {o : Option TState} {a : Acc} {bs : List Byte} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (ht : At t 7932 (correctionActiveTileFacts p l g batch lane))
    (hr : Run kernel Assumptions.all l (warpLane l g lane) t
      ((X.tr (warpLane l g lane)).drop pos) o) (hJ : pos ≤ j) (hPc : pc = 9073 ∨ pc = 9082)
    (he : X.get (warpLane l g lane, j) = some ⟨pc, .wr a bs⟩) :
    AssignedLseFootprint p l (g / l.block) (warpLane l g lane) a := by
  let thread := warpLane l g lane
  let coords := assignedCoordinates p batch (g / l.block)
  have ⟨hTile, hHead⟩ : 256 * coords.1 < p.qLength batch ∧ coords.2 < p.heads :=
    assignedCoordinates_valid hp hLo hHi
  let F := [(1613, b32 (rowOf l thread)), (9605, b64 coords.2),
    (7501, b64 p.lseStride), (7500, b64 p.lseBase)]
  let H := correctionInputFacts p batch coords.1
  let tailEvent : Event := ⟨pc, .wr a bs⟩
  have hLen : j < (X.tr thread).length := (List.getElem?_eq_some_iff.mp he).1
  have hLate : 9057 < tailEvent.pc := by change 9057 < pc; omega
  have hNonempty : (X.tr thread).drop pos ≠ [] := by
    intro h
    have hLen' := List.drop_eq_nil_iff.mp h
    omega
  obtain ⟨v, hv, hvAt⟩ := correctionInputRun hp hb ht
  have hSave : Holds v.regs F := by
    have h := hvAt.2.2.2.2
    exact ⟨holds_lookup h (by rfl), holds_lookup h (by rfl),
      holds_lookup h (by rfl), holds_lookup h (by rfl), trivial⟩
  let carry := correctionTileGeometryFacts l thread true ++
    correctionActiveTileFacts p l g batch lane
  have hWords : Holds v.regs (H ++ carry) := by
    simpa only [List.append_assoc] using hvAt.2.2.2.2
  have hAt : At v 7955 (H ++ F) :=
    hvAt.mono ((holds_append _ _ _).2 ⟨((holds_append _ _ _).1 hWords).1, hSave⟩)
  obtain ⟨w, hw, hRun, hRead0, hRead1, _, _⟩ := correctionCuQReadsToUsedK hp hX hb hAt
    (by
      intro rv hm
      have h := List.mem_map_of_mem (f := Prod.fst) hm
      intro he
      simp only [F, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
        at h he
      omega)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (hr.after_local_nonempty (run_rtg hv) hNonempty) (.inr ⟨j, tailEvent, hJ, by omega, he⟩)
  have hBefore : pos + 2 ≤ j := by
    by_contra h
    rcases (show j = pos ∨ j = pos + 1 by omega) with rfl | rfl
    · have hp := congrArg Event.pc (Option.some.inj (he.symm.trans hRead0))
      change pc = 7955 at hp
      omega
    · have hp := congrArg Event.pc (Option.some.inj (he.symm.trans hRead1))
      change pc = 7956 at hp
      omega
  have hMem : tailEvent ∈ (X.tr thread).drop (pos + 2) := by
    apply List.mem_of_getElem? (i := j - (pos + 2))
    rwa [List.getElem?_drop, Nat.add_sub_of_le hBefore]
  have hFrame : At w 7959 ((8993, b64 (p.usedKBase + 4 * batch)) ::
      lseTripAddressFacts p l thread batch coords.2 coords.1) := by
    apply hw.mono
    have h := hw.2.2.2.2
    exact ⟨holds_lookup h (by rfl), holds_lookup h (by rfl), holds_lookup h (by rfl),
      holds_lookup h (by rfl), holds_lookup h (by rfl), holds_lookup h (by rfl),
      holds_lookup h (by rfl), holds_lookup h (by rfl), trivial⟩
  obtain ⟨u, vs, hu, hWalk, hTail⟩ := correctionUsedKAddressFrame hp hb hFrame
    (by
      intro rv hm
      have hr := List.mem_map_of_mem (f := Prod.fst) hm
      simp [lseTripAddressFacts] at hr
      omega)
    hRun (by omega) hMem
  have hQEnd := hp.qOffset_le_total (b := batch + 1) (by omega)
  have hTotal := hp.shape.2.2.2.2
  have hFit : 256 * coords.1 < 2 ^ 32 := by
    change 256 * coords.1 < p.qOffset (batch + 1) - p.qOffset batch at hTile
    omega
  obtain ⟨entry, _, hEntry, hBody⟩ :=
    cutLseTripAddress hFit (by omega) hu hWalk hTail
  obtain ⟨s, es, vs, hs, hS, hEvent⟩ := cutLseReadyPrefix hPc hEntry hBody hTail
  obtain ⟨stage, _, hRow, hAddr, hSize⟩ :=
    correctionLseFootprintFromReady hp hb hHead hTile hs hPc hS hEvent
  exact ⟨batch, hb, stage, hLo, hHi, hRow, by simpa only [Nat.add_assoc] using hAddr, hSize⟩


/-- Finish the chosen request's coordinate shuffles and expose an active correction tile. -/
theorem correctionTileOfChoiceEvent {g first batch lane j shuffles votes : Nat}
    {ends : Nat → Option TState} {target : Event} (hg : g < l.threads) (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (chosen : SchedulerWarpAt l X g 7878 (correctionChosenFacts p l g first batch)
      shuffles votes ends) (hLate : 7884 < target.pc)
    (he : WarpFollowsEvent l X g chosen.pos lane j target) :
    ∃ sh, ∃ active : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch)
      sh votes ends, WarpFollowsEvent l X g active.pos lane j target := by
  obtain ⟨withPrefix, hPrefix⟩ := correctionSelectedPrefixTo hp hX hg hFirst hGroup hb
    chosen (.inr he) (by omega)
  have hPrefix' := hPrefix he
  obtain ⟨coordinates, hCoordinates⟩ := correctionSelectedCoordinatesTo hp hX hg
    hFirst hGroup hb hLo hHi withPrefix (.inr hPrefix') hLate
  have hCoordinates' := hCoordinates hPrefix'
  obtain ⟨active, hActivePos⟩ := correctionActiveCoordinatesAt hp hb hLo hHi coordinates
  have hActive : WarpFollowsEvent l X g active.pos lane j target :=
    hActivePos.symm ▸ hCoordinates'
  exact ⟨_, active, hActive⟩


/-- Finish the request-group ballot and its selected tile while keeping a later actual event. -/
theorem correctionTileOfGroupEvent {g first batch lane j shuffles votes : Nat}
    {ends : Nat → Option TState} {target : Event} (hg : g < l.threads) (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (cur : SchedulerWarpAt l X g 7864 (correctionGroupEntry p l g first) shuffles votes ends)
    (hLate : 7884 < target.pc) (hew : WarpFollowsEvent l X g cur.pos lane j target) :
    ∃ sh, ∃ active : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch)
      sh (votes + 1) ends, WarpFollowsEvent l X g active.pos lane j target := by
  obtain ⟨ballot, hBallotPos⟩ := correctionGroupBallotReadyAt hp hFirst hGroup hb hLo hHi cur
  have hBallot : WarpFollowsEvent l X g ballot.pos lane j target :=
    hBallotPos.symm ▸ hew
  obtain ⟨chosen, hChosen⟩ := correctionSelectBatchTo hp hX hg hFirst hGroup hb
    ballot (.inr hBallot) (by omega)
  have hChosen' := hChosen hBallot
  exact correctionTileOfChoiceEvent hp hX hg hFirst hGroup hb hLo hHi chosen hLate hChosen'


/-- A request-group checkpoint yields the actual LSE footprint through the selected lane's
ballot, coordinate shuffles, protected reads, and correction body. -/
theorem correctionLseFootprintFromGroup {g first batch lane j pc shuffles votes : Nat}
    {ends : Nat → Option TState} {a : Acc} {bs : List Byte} (hg : g < l.threads)
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (cur : SchedulerWarpAt l X g 7864 (correctionGroupEntry p l g first) shuffles votes ends)
    (hPc : pc = 9073 ∨ pc = 9082) (hew : WarpFollowsEvent l X g cur.pos lane j ⟨pc, .wr a bs⟩) :
    AssignedLseFootprint p l (g / l.block) (warpLane l g lane) a := by
  obtain ⟨_, active, hActive⟩ := correctionTileOfGroupEvent hp hX hg hFirst hGroup hb
    hLo hHi cur (by change 7884 < pc; omega) hew
  have hRead := (active.continuation lane hActive.lane).after_local_nonempty
    (active.localSteps lane hActive.lane) hActive.nonempty
  exact correctionLseFootprintFromSelected hp hX hb hLo hHi
    (active.checkpoint lane hActive.lane) hRead hActive.before hPc hActive.get


/-- A correction lane that reaches a later event has completed the first group's scan
and reached the corresponding scheduler branch. -/
theorem correctionFirstRouteOfEvent {g lane j : Nat} {target : Event} (hg : g < l.threads)
    (hLoWarp : 8 ≤ Prologue.warpIndex l g) (hHiWarp : Prologue.warpIndex l g < 12) (hl : lane < 32)
    (hTarget : 7801 < target.pc) (he : X.get (warpLane l g lane, j) = some target) :
    ∃ (ends : Nat → Option TState), ∃ ready : SchedulerWarpAt l X g
        (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 7864 else 7807)
        (correctionFirstRouteFacts p l g) 10 0 ends,
      WarpFollowsEvent l X g ready.pos lane j target := by
  obtain ⟨ends, down, hDown⟩ := firstCorrectionWarpOfEvent hp hX hg hLoWarp hHiWarp hl
    he (by omega)
  obtain ⟨tiles, hPos⟩ := correctionWarpFirstTilesAt hp hg down
  have hTiles : WarpFollowsEvent l X g tiles.pos lane j target := hPos.symm ▸ hDown
  obtain ⟨sum, hSum⟩ := correctionFirstScanTo hp hX hg tiles (.inr hTiles) (by omega)
  have hScanned := hSum hTiles
  obtain ⟨routed, hRoute⟩ := correctionFirstRouteTo hp hX hg sum (.inr hScanned) hTarget
  exact ⟨ends, routed, hRoute hScanned⟩


/-- For an observed LSE write assigned to the first request group, the lane's
actual entry, shuffles, ballot, and protected reads determine its footprint. -/
theorem correctionFirstGroupLseStoreSpec {g lane j pc : Nat} {a : Acc} {bs : List Byte}
    (hg : g < l.threads) (hLoWarp : 8 ≤ Prologue.warpIndex l g)
    (hHiWarp : Prologue.warpIndex l g < 12) (hl : lane < 32)
    (hFirst : g / l.block < tilePrefix p (min p.batch 31) * p.heads) (hPc : pc = 9073 ∨ pc = 9082)
    (he : X.get (warpLane l g lane, j) = some ⟨pc, .wr a bs⟩) :
    AssignedLseFootprint p l (g / l.block) (warpLane l g lane) a := by
  have route := correctionFirstRouteOfEvent hp hX hg hLoWarp hHiWarp hl
    (by change 7801 < pc; omega) he
  rw [ite_eq_left hFirst] at route
  obtain ⟨ends, ready, hReady⟩ := route
  obtain ⟨batch, hBatch, hLo, hHi, selected, hSelect⟩ :=
    correctionFirstBatchTo hp hX hg hFirst ready (.inr hReady) (by change 7873 < pc; omega)
  have hB := hBatch.trans_le (Nat.min_le_left ..)
  have hG : batch < 0 + 31 := hBatch.trans_le (Nat.min_le_right ..)
  have hSelected := hSelect hReady
  obtain ⟨_, active, hActive⟩ := correctionTileOfChoiceEvent hp hX hg (Nat.zero_le _) hG hB
    hLo hHi selected (by change 7884 < pc; omega) hSelected
  have hRead := (active.continuation lane hActive.lane).after_local_nonempty
    (active.localSteps lane hActive.lane) hActive.nonempty
  exact correctionLseFootprintFromSelected hp hX hB hLo hHi (active.checkpoint lane hActive.lane)
    hRead hActive.before hPc hActive.get

end
end PTX.Kernels.TmlFa4Fwd.Correction
