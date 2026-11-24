-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionCoordinateInteger
public import Kernels.TmlFa4Fwd.Proof.CorrectionSelectedCoordinates

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The ABI carried into the active compute path excludes the candidate batch register,
which the ballot replaced with the selected request. -/
def correctionTileFrame (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  (afterCreditFacts p l g).filter (fun pair => pair.1 != 7277)

def correctionActiveTileFacts (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  let pos := assignedCoordinates p batch (g / l.block)
  [(7277, b32 batch), (7276, b32 pos.1), (9605, b64 pos.2), (784, .pred true)] ++
    correctionTileFrame p l (warpLane l g lane)

private theorem holds_frame {R : Nat → Option Value} {F : List (Nat × Value)}
    (h : ∀ rv ∈ F, R rv.1 = some rv.2) : Holds R F := by
  induction F with
  | nil => trivial
  | cons rv rest ih =>
    cases rv with
    | mk r v => exact ⟨h (r, v) (by simp), ih (fun x hx => h x (by simp [hx]))⟩

set_option maxRecDepth 100000 in
private theorem coordinateCoreCode :
    ((kernel.code.drop 7887).take 45).all (fun i => Assumptions.coreOp i.op) = true := by
  kernel_rfl

private theorem coordinateCoreOut {l : Launch} {g : Nat} {t : TState}
    (hLo : 7887 ≤ t.pc) (hHi : t.pc < 7932) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hm : ins ∈ (kernel.code.drop 7887).take 45 := by
      apply List.mem_of_getElem? (i := t.pc - 7887)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp coordinateCoreCode _ hm)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The common warp checkpoint reaches the actual active correction tile, preserving the
original CTA ABI registers needed by the statistics barriers and request reads. -/
theorem correctionActiveCoordinatesPreserving (hp : Pre p l m) {g first batch shuffles votes : Nat}
    (hBatch : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 7887 (correctionCoordinateFacts p l g first batch)
      shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch)
      shuffles votes ends, next.pos = cur.pos ∧ next.before = cur.before := by
  apply cur.advanceLocalPreserving
  intro lane hl
  let thread := warpLane l g lane
  let facts := correctionCoordinateFacts p l g first batch lane
  let F := correctionTileFrame p l thread
  have ht := cur.checkpoint lane hl
  have hH : Holds (cur.state lane).regs facts := ht.2.2.2.2
  have hTile := holds_lookup hH
    (show facts.lookup 5916 = some (b32 (requestTiles p batch)) from rfl)
  have hHeads := holds_lookup hH (show facts.lookup 7142 = some (b32 p.heads) from rfl)
  have hDiff := holds_lookup hH (show facts.lookup 5918 =
    some (b32 (g / l.block - tilePrefix p batch * p.heads)) from rfl)
  have hBatchWord := holds_lookup hH (show facts.lookup 7277 = some (b32 batch) from rfl)
  have hFrame : Holds (cur.state lane).regs F := by
    apply holds_frame
    intro rv hm
    apply holds_mem hH
    obtain ⟨hCarry, hKeep⟩ := List.mem_filter.mp hm
    have hSafe : (rv.1 != 7275) = true := by
      apply bne_iff_ne.mpr
      intro hEq
      have hMem := List.mem_map_of_mem (f := Prod.fst) hCarry
      rw [hEq] at hMem
      exact (of_decide_eq_true rfl : 7275 ∉ (afterCreditFacts p l thread).map Prod.fst) hMem
    change rv ∈ afterCreditFacts p l (warpLane l g lane) at hCarry
    change rv ∈ correctionCoordinateFacts p l g first batch lane
    simp only [correctionCoordinateFacts, correctionPrefixFacts, correctionChosenFacts,
      correctionVoteCarry, correctionGroupABI, firstShuffleFacts, List.mem_append,
      List.mem_cons, List.mem_filter, hCarry, hKeep, hSafe, and_true, or_true]
  obtain ⟨u, hu, hU⟩ := correctionSectionCoordinates hp thread hBatch hLo hHi _
    (ht.mono ⟨hTile, hHeads, hDiff, hH.2.2.2.1, hH.2.2.1, hBatchWord, trivial⟩)
  have hStraight : ((kernel.code.drop 7887).take (45 - 1)).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have huAll := schedulerLocalTransport (lo := 7887) (len := 45) hStraight
    (fun h0 h1 => coordinateCoreOut h0 h1) hu ht.1.ge (by rw [ht.1])
  have hKeep : ∀ r ∈ F.map Prod.fst, u.regs r = (cur.state lane).regs r :=
    fun _ hm => schedulerLocalFrame (lo := 7887) (len := 45)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      hStraight hu ht.1.ge (by rw [ht.1]) hm
  have hRemain := holdsSchedulerFrame hFrame hKeep (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨u, run_rtg huAll, hU.mono ((holds_append _ _ _).2 ⟨hU.2.2.2.2, hRemain⟩)⟩

/-- The active tile keeps the selected coordinate event boundary. -/
theorem correctionActiveCoordinatesAt (hp : Pre p l m) {g first batch shuffles votes : Nat}
    (hBatch : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 7887 (correctionCoordinateFacts p l g first batch)
      shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch)
      shuffles votes ends, next.pos = cur.pos := by
  obtain ⟨next,hPos,_⟩ := correctionActiveCoordinatesPreserving hp hBatch hLo hHi cur
  exact ⟨next,hPos⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
