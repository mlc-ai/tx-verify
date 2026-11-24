-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixMetadata
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmEntry
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part008
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

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

def warmPageRoots (p : Params) (l : Launch) (batch tid : Nat) : List (Nat × Value) :=
  (7170, b32 batch) :: (warmLaneRoots l tid ++
    [(7504, b64 p.pageTableBase), (7505, b64 p.pageTableStride)])

/-- Launch-derived values retained across the initial K/V packets. -/
def warmStartFrame (p : Params) (l : Launch) (batch head trips warp tid : Nat) :
    List (Nat × Value) :=
  [(1088, b32 trips), (1091, b32 (trips - 1)), (1062, b32 warp), (2535, b32 l.sharedBase),
   (1086, b32 (p.kLength batch)), (7295, b64 (l.localBase + 96)),
   (7495, b64 p.kLayout.pageStride), (7493, b64 p.kLayout.rowStride),
   (7300, b64 (p.kLayout.base + 2 * (head * p.kLayout.headStride))),
   (7302, b64 1), (1093, b32 1), (1094, b32 3)] ++
    primingVScratchAbi p l head ++ warmPageRoots p l batch tid

/-- Launch-derived Bias coordinates preserved through the loader's initial packets. -/
def warmBiasRoots (p : Params) (batch tile head : Nat) : List (Nat × Value) :=
  [(1087,b32 (p.qOffset batch + 256*tile)),(7169,b32 head),
    (1089,b32 (vPrimingResidual p batch tile)),(1090,b32 0)]

/-- The loader's role predicate gates every warm Bias issue. -/
private theorem warmRoleSeedCore {l : Launch} {g warp : Nat} (hLo : 14 ≤ warp) (hHi : warp < 16) :
    Seg kernel [] l g 1 538 [(1062,b32 warp)] 539 [(123,.pred (decide (warp ≠ 14)))] := by
  have hCases : warp = 14 ∨ warp = 15 := by omega
  rcases hCases with rfl | rfl <;> intro t ht <;> seg_fp ht using rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g src j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hl : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) {e : Event}
    (he : X.get (warpLane l g src, j) = some e)
include hp hX hg hw hl writes hCTA he

/-- A later loader event forces the actual lane to the post-priming guard,
still holding its selected launch trip count. -/
theorem loaderWarmStartWithBiasRoleOfEvent (hLate : 908 ≤ e.pc) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let thread := warpLane l g src
      ∃ pos ≤ j, ∃ s ending,
        At s 907 ((123,.pred (decide (warpIndex l g ≠ 14))) ::
          warmStartFrame p l batch (co.2 / 6) (Mma.trips p batch co.1)
            (warpIndex l g) (thread % l.block) ++ warmBiasRoots p batch co.1 co.2) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 := by
  obtain ⟨batch, hb, hLo, hHi, pos, hBefore, s, ending, hs, hr, hRank⟩ :=
    loaderPrimingMetadataOfActiveEventWithRoots hp hX hg hw hl writes hCTA he (by omega)
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g src
  let trips := Mma.trips p batch co.1
  let G := warmPageRoots p l batch (thread % l.block)
  let F := warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) (thread % l.block) ++
    warmBiasRoots p batch co.1 co.2
  obtain ⟨hTile, hHead⟩ := assignedCoordinates_valid hp hLo hHi
  have hHeld := (holds_append ..).mp hs.2.2.2.2
  have hs' : At s 386
      (primingKActiveFacts p l batch co.2 co.1 (warpIndex l g) src ++ G) := by
    refine hs.mono ((holds_append ..).mpr ⟨hHeld.1, ?_⟩)
    simp only [G, warmPageRoots, warmLaneRoots, List.cons_append, Holds]
    exact ⟨hHeld.2.1, hHeld.2.2.1, hHeld.2.2.2.1, hHeld.2.2.2.2.1,
      holds_lookup hHeld.1 rfl, holds_lookup hHeld.1 rfl, trivial⟩
  obtain ⟨t, ht, hT⟩ := primingKActiveToAddressLaneWithExtra hp hb hTile
    (by set_option maxRecDepth 100000 in kernel_rfl) hs'
  obtain ⟨_, u, hu, hU⟩ := primingVAdmissionWithTripsLaneExtra hp (g := thread)
    hb (hHead.trans hp.heads_signed) hTile hl
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hT
  have hAt : At u 488 F := by
    refine hU.mono ?_
    simp only [F, warmStartFrame, warmBiasRoots, warmPageRoots, warmLaneRoots, List.cons_append,
      List.nil_append, Holds]
    repeat' apply And.intro
    all_goals first
      | trivial
      | exact holds_lookup hU.2.2.2.2 rfl
      | (have hLaneWarp : (32 * warpIndex l g + src) / 32 = warpIndex l g := by omega
         rw [← hLaneWarp]
         exact holds_lookup hU.2.2.2.2 rfl)
  have huRun := hr.after_local_nonempty (ht.trans hu) (traceAfterObservedEvent he hBefore)
  have hFirstAudit : ∀ branch, ((kernel.code.drop 488).take (538 - 488)).all
      (fun ins => loaderPipelineCutOp 488 538 branch (F.map Prod.fst) ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  have hFirstRank : (((kernel.code.drop 488).take (538 - 488)).zipIdx 488).all
      (fun (ins, pc) => LoaderRankedInstr 538 pc ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨r, first, last, _, hR, hrRun, hrRank, hrOrder⟩ :=
    prefixRankedShuffleCut (by decide) hFirstAudit hFirstRank hAt huRun he hBefore
      (.inl (by omega)) hSafe
  have hWarp := holds_mem hR.2.2.2.2
    (show (1062,b32 (warpIndex l g)) ∈ F by simp [F,warmStartFrame])
  obtain ⟨r',hLocal,hR'⟩ := (warmRoleSeedCore (g := thread) hw (warpIndex_lt hp g)).apply
    (hR.mono ⟨hWarp,trivial⟩)
  obtain ⟨hCore,hFrame⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide)
    hR.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hLocal
  let F' := (123,.pred (decide (warpIndex l g ≠ 14))) :: F
  have hAt' : At r' 539 F' := hR'.mono
    ⟨hR'.2.2.2.2.1,holdsSchedulerFrame hR.2.2.2.2 hFrame
      (fun _ hr => List.mem_map_of_mem hr)⟩
  have hrRun' := hrRun.after_local_nonempty (run_rtg hCore) (traceAfterObservedEvent he hrOrder)
  have hAudit : ∀ branch, ((kernel.code.drop 539).take (907 - 539)).all
      (fun ins => loaderPipelineCutOp 539 907 branch (F'.map Prod.fst) ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  have hRankCode : (((kernel.code.drop 539).take (907 - 539)).zipIdx 539).all
      (fun (ins, pc) => LoaderRankedInstr 907 pc ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨v, front, stop, _, hV, hvRun, hvRank, hvOrder⟩ :=
    prefixRankedShuffleCut (by decide) hAudit hRankCode hAt' hrRun' he hrOrder
      (.inl (by omega)) hSafe
  have hCount : loaderShuffleTail 538 488 + loaderShuffleTail 907 539 = 64 := by
    set_option maxRecDepth 100000 in kernel_rfl
  exact ⟨batch, hb, hLo, hHi, pos + first.length + front.length, hvOrder, v, stop, hV, hvRun,
    by rw [hvRank, hrRank, hRank, Nat.add_assoc, hCount]⟩

/-- A later loader event forces the actual lane to the post-priming guard,
still holding its selected launch trip count. -/
theorem loaderWarmStartWithBiasOfEvent (hLate : 908 ≤ e.pc) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let thread := warpLane l g src
      ∃ pos ≤ j, ∃ s ending,
        At s 907 (warmStartFrame p l batch (co.2 / 6) (Mma.trips p batch co.1)
          (warpIndex l g) (thread % l.block) ++ warmBiasRoots p batch co.1 co.2) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 := by
  obtain ⟨batch,hb,hLo,hHi,pos,hBefore,s,ending,hs,hr,hRank⟩ :=
    loaderWarmStartWithBiasRoleOfEvent hp hX hg hw hl writes hCTA he hLate hSafe
  exact ⟨batch,hb,hLo,hHi,pos,hBefore,s,ending,hs.mono hs.2.2.2.2.2,hr,hRank⟩

/-- A later loader event forces the actual lane to the post-priming guard,
still holding its selected launch trip count. -/
theorem loaderWarmStartOfEvent (hLate : 908 ≤ e.pc) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let thread := warpLane l g src
      ∃ pos ≤ j, ∃ s ending,
        At s 907 (warmStartFrame p l batch (co.2 / 6) (Mma.trips p batch co.1)
          (warpIndex l g) (thread % l.block)) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 := by
  obtain ⟨batch,hb,hLo,hHi,pos,hBefore,s,ending,hs,hr,hRank⟩ :=
    loaderWarmStartWithBiasOfEvent hp hX hg hw hl writes hCTA he hLate hSafe
  exact ⟨batch,hb,hLo,hHi,pos,hBefore,s,ending,hs.mono ((holds_append ..).mp hs.2.2.2.2).1,
    hr,hRank⟩

omit hp hX hg hw hl writes hCTA he in
private def warmResidual (n : Nat) : Nat := (n + (2 ^ 32 - 2)) % 2 ^ 32

omit hp hX hg hw hl writes hCTA he in
private theorem warmResidualCore {l : Launch} {g n : Nat} (hn : n < 2 ^ 31) :
    Seg kernel [] l g 1 907 [(1088, b32 n)] 908 [(1116, b32 (warmResidual n))] := by
  have hN32 : n < 2 ^ 32 := by omega
  have hWide : n + (2 ^ 32 - 2) < 2 ^ 64 := by omega
  have hImm : truncBits 32 (BitVec.ofInt 64 (-2)) = BitVec.ofNat 64 (2 ^ 32 - 2) := rfl
  have hResult : truncBits 32
      (BitVec.ofNat 64 n + truncBits 32 (BitVec.ofInt 64 (-2))) =
      BitVec.ofNat 64 (warmResidual n) := by
    rw [hImm, ← BitVec.ofNat_add, truncBits, toNat_ofNat_lt hWide]
    rfl
  intro s hs
  seg_fp hs using
    simp only [b32, truncBits_ofNat hN32 (by decide), hResult]

omit hp hX hg hw hl writes hCTA he in
/-- The selected request has a tile beyond the initial K/V packets. -/
def HasWarmTile (p : Params) (l : Launch) (g : Nat) : Prop :=
  ∃ batch < p.batch,
    tilePrefix p batch * p.heads ≤ g / l.block ∧
    g / l.block < tilePrefix p (batch + 1) * p.heads ∧
    2 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1

/-- The actual warm arm starts with the exact residual visible trip counter. -/
theorem loaderWarmArmWithBiasRoleOfEventRanked (hLate : 917 ≤ e.pc)
    (hWarm : e.pc < 1353 ∨ HasWarmTile p l g) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let thread := warpLane l g src
      let trips := Mma.trips p batch co.1
      2 ≤ trips ∧
      ∃ pos ≤ j, ∃ s ending,
        At s 912 ((1116, b32 (trips - 2)) ::
          (warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) (thread % l.block) ++
            warmBiasRoots p batch co.1 co.2 ++
            [(123,.pred (decide (warpIndex l g ≠ 14)))])) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 := by
  obtain ⟨batch, hb, hLo, hHi, pos, hBefore, s, ending, hs, hr, hRank⟩ :=
    loaderWarmStartWithBiasRoleOfEvent hp hX hg hw hl writes hCTA he (by omega) hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g src
  let trips := Mma.trips p batch co.1
  let warp := warpIndex l g
  let role : Nat × Value := (123,.pred (decide (warp ≠ 14)))
  let G := warmStartFrame p l batch (co.2 / 6) trips warp (thread % l.block) ++
    warmBiasRoots p batch co.1 co.2
  let F := G ++ [role]
  have hsF : At s 907 F := hs.mono ((holds_append ..).mpr
    ⟨hs.2.2.2.2.2,hs.2.2.2.2.1,trivial⟩)
  obtain ⟨hTile, _⟩ := assignedCoordinates_valid hp hLo hHi
  have hTrip := (Mma.trips_bounds hp hb hTile).2.1
  have hLen := (hp.lengths batch hb).2.2
  change trips ≤ (p.kLength batch + 127) / 128 at hTrip
  have hn : trips < 2 ^ 31 := by omega
  have hTripReg : s.regs 1088 = some (b32 trips) :=
    holds_mem hsF.2.2.2.2 (by simp [F,G,warmStartFrame])
  obtain ⟨u, hu, hU⟩ := warmResidualCore (g := thread) hn s (hsF.mono ⟨hTripReg,trivial⟩)
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := F.map Prod.fst)
    (by decide) (by decide) hsF.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have huF : Holds u.regs F :=
    holdsSchedulerFrame hsF.2.2.2.2 huFrame (fun _ hm => List.mem_map_of_mem hm)
  let F' := (1116, b32 (warmResidual trips)) :: F
  have hWith : At u 908 ([(1088, b32 trips), (1091, b32 (trips - 1))] ++ F') := by
    exact hU.mono ⟨holds_mem huF (by simp [F,G,warmStartFrame]),
      holds_mem huF (by simp [F,G,warmStartFrame]), hU.2.2.2.2.1, huF⟩
  obtain ⟨v, hv, hV⟩ := loaderWarmGateWithFrame (g := thread) hn (F := F')
    (by set_option maxRecDepth 100000 in kernel_rfl) hWith
  have hRun := hr.after_local_nonempty (run_rtg (run_comp huA hv))
    (traceAfterObservedEvent he hBefore)
  have hFrame : Holds v.regs F' := hV.2.2.2.2.2
  have hAt := hV.mono hFrame
  have hTripLive : 2 ≤ trips := by
    rcases hWarm with hPc | ⟨other, hOther, hOtherLo, hOtherHi, hTwo⟩
    swap
    · obtain ⟨chosen, _, only⟩ := tileBatch_existsUnique p hCTA
      have hSame := (only other ⟨hOther, hOtherLo, hOtherHi⟩).trans
        (only batch ⟨hb, hLo, hHi⟩).symm
      subst other
      exact hTwo
    by_contra! hSmall
    have hSkipped : v.pc = 1353 := by simpa [hSmall] using hV.1
    let w : Fin 2 := ⟨warp - 14, by have := warpIndex_lt hp g; dsimp [warp]; omega⟩
    have hWarp : 14 + w.val = warp := by dsimp [w, warp] at *; omega
    have hRole : Holds v.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + w.val))] :=
      ⟨holds_mem hFrame (by simp [F',F,G,warmStartFrame]),
        hWarp.symm ▸ holds_mem hFrame (by simp [F',F,G,warmStartFrame]),trivial⟩
    obtain ⟨vs, hwk⟩ := Mma.walkFromRun hRun
    have hm : e ∈ (X.tr thread).drop pos := by
      apply List.mem_of_getElem? (i := j - pos)
      rw [List.getElem?_drop, Nat.add_sub_of_le hBefore]
      exact he
    have hRange := Epilogue.loaderWalkEventRange w (by decide : 174 ≤ 1353)
      (show 1353 ≤ v.pc ∧ v.pc ≤ 1901 by rw [hSkipped]; decide) (ringShapeOfAt hAt) hRole
      (fun _ => by set_option maxRecDepth 100000 in kernel_rfl) hwk e hm
    omega
  have hResidual : warmResidual trips = trips - 2 := by unfold warmResidual; omega
  refine ⟨batch, hb, hLo, hHi, hTripLive, pos, hBefore, v, ending, ?_, hRun, hRank⟩
  simpa only [F', F,G,role,hResidual, ite_eq_right (Nat.not_lt.mpr hTripLive)] using hAt

/-- The actual warm arm starts with the exact residual visible trip counter. -/
theorem loaderWarmArmWithBiasOfEventRanked (hLate : 917 ≤ e.pc)
    (hWarm : e.pc < 1353 ∨ HasWarmTile p l g) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let thread := warpLane l g src
      let trips := Mma.trips p batch co.1
      2 ≤ trips ∧
      ∃ pos ≤ j, ∃ s ending,
        At s 912 ((1116, b32 (trips - 2)) ::
          (warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) (thread % l.block) ++
            warmBiasRoots p batch co.1 co.2)) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 := by
  obtain ⟨batch,hb,hLo,hHi,hTwo,pos,hBefore,s,ending,hs,hr,hRank⟩ :=
    loaderWarmArmWithBiasRoleOfEventRanked hp hX hg hw hl writes hCTA he hLate hWarm hSafe
  refine ⟨batch,hb,hLo,hHi,hTwo,pos,hBefore,s,ending,hs.mono ?_,hr,hRank⟩
  exact ⟨hs.2.2.2.2.1,((holds_append ..).mp hs.2.2.2.2.2).1⟩

/-- The actual warm arm starts with the exact residual visible trip counter. -/
theorem loaderWarmArmOfEventRanked (hLate : 917 ≤ e.pc) (hWarm : e.pc < 1353 ∨ HasWarmTile p l g)
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let thread := warpLane l g src
      let trips := Mma.trips p batch co.1
      2 ≤ trips ∧
      ∃ pos ≤ j, ∃ s ending,
        At s 912 ((1116, b32 (trips - 2)) ::
          warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) (thread % l.block)) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 := by
  obtain ⟨batch,hb,hLo,hHi,hTrip,pos,hBefore,s,ending,hs,hr,hRank⟩ :=
    loaderWarmArmWithBiasOfEventRanked hp hX hg hw hl writes hCTA he hLate hWarm hSafe
  have hHeld := hs.2.2.2.2
  refine ⟨batch,hb,hLo,hHi,hTrip,pos,hBefore,s,ending,hs.mono ?_,hr,hRank⟩
  exact ⟨hHeld.1,((holds_append ..).mp hHeld.2).1⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
