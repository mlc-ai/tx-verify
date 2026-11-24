-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundEntry
import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation
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
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

section
variable {l : Launch} {X : Execution} {g index j remaining : Nat} {s : TState}
    {ending : Option TState} {F : List (Nat × Value)} (hTrips : remaining < 2 ^ 31)
    (hInit : ((kernel.code.drop 1353).take 2).all (fun ins =>
      schedulerFallsThrough ins.op && (F.map Prod.fst).all
        (fun r => !(loaderRingWrites ins.op).contains r)) = true)
    (hBeforeGate : ∀ bound, ((kernel.code.drop 1355).take (1384 - 1355)).all
      (fun ins => loaderPipelineCutOp 1355 1384 bound
        (([(7181, b32 (min remaining 9)), (1091, b32 remaining)] ++ F).map Prod.fst) ins.op) =
        true)
    (hCompare : ((kernel.code.drop 1384).take 1).all
      (fun ins => (F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true)
    (hBranch : ((kernel.code.drop 1385).take 1).all
      (fun ins => (F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true)
    (hs : At s 1353 ((1091, b32 remaining) :: F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
include hTrips hInit hBeforeGate hCompare hBranch hs hr

set_option maxRecDepth 100000 in
/-- Enter or bypass the actual steady ring with the selected warm trip count and frame. -/
theorem steadyGateFromSeedDemand {e : Event} (he : X.get (g, j) = some e) (hOrder : index ≤ j)
    (hDemand : 1384 ≤ e.pc ∨ Execution.isShfl e = true) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ pos ≤ j, ∃ u stop,
      At u (if min remaining 9 < remaining then 1386 else 1744)
        ([(7181, b32 (min remaining 9)), (1091, b32 remaining)] ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl := by
  let G := [(7181, b32 (min remaining 9)), (1091, b32 remaining)] ++ F
  obtain ⟨t, ht, hT⟩ := loaderSteadyCounterInit hTrips s (hs.mono ⟨hs.2.2.2.2.1, trivial⟩)
  obtain ⟨_, hKeep⟩ := loaderSegmentFrame (lower := 1353) (stop := 1355)
    (by decide) (by decide) hInit ht hs.1.ge (by simp [hs.1])
  have ht' : At t 1355 G := hT.mono ((holds_append ..).mpr ⟨hT.2.2.2.2,
    holdsSchedulerFrame hs.2.2.2.2.2 hKeep (fun _ hm => List.mem_map_of_mem hm)⟩)
  have htRun := hr.after_local_nonempty (run_rtg ht) (traceAfterObservedEvent he hOrder)
  have hRanked : (((kernel.code.drop 1355).take (1384 - 1355)).zipIdx 1355).all
      (fun (ins, pc) => LoaderRankedInstr 1384 pc ins) = true := by kernel_rfl
  have hCount : loaderShuffleTail 1384 1355 = 0 := by kernel_rfl
  have hRankDemand : 1384 ≤ e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail 1384 1355 ≤
        ((X.tr g).take j).countP Execution.isShfl) := hDemand.imp_right fun h => ⟨h, by
    rw [hCount, Nat.add_zero]
    exact countP_take_mono Execution.isShfl _ hOrder⟩
  obtain ⟨v, front, stop, _, hv, hvRun, hRank, hBefore⟩ :=
    prefixRankedShuffleCut (by decide) hBeforeGate hRanked ht' htRun he hOrder hRankDemand hSafe
  obtain ⟨u, hu, hU⟩ := loaderSteadyCounterGateWithFrame hTrips
    (show min remaining 9 < 2 ^ 31 by omega) hCompare hBranch v hv
  have huRun := hvRun.after_local_nonempty (run_rtg hu) (traceAfterObservedEvent he hBefore)
  exact ⟨index + front.length, hBefore, u, stop, hU, huRun, by simpa only [hCount, Nat.add_zero]⟩

set_option maxRecDepth 100000 in
/-- Enter or bypass the actual steady ring with the selected warm trip count and frame. -/
theorem steadyGateFromSeed {e : Event} (he : X.get (g, j) = some e) (hOrder : index ≤ j)
    (hPc : 1384 ≤ e.pc) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ pos ≤ j, ∃ u stop,
      At u (if min remaining 9 < remaining then 1386 else 1744)
        ([(7181, b32 (min remaining 9)), (1091, b32 remaining)] ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl := by
  exact steadyGateFromSeedDemand hTrips hInit hBeforeGate hCompare hBranch hs hr
    he hOrder (.inl hPc) hSafe
end

set_option maxRecDepth 100000 in
/-- An observed steady body event means the selected request outlasted the nine warm visits. -/
theorem observedSteadyTrips {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hPc : 1386 ≤ e.pc ∧ e.pc < 1744) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch, tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      11 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 := by
  obtain ⟨batch, hb, hLo, hHi, i, hOrder, s, ending, hs, hr, _⟩ :=
    loaderWarmStartOfEvent hp hX hg hw hl writes hCTA he (by omega) hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let trips := Mma.trips p batch co.1
  let thread := warpLane l g lane
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWarp : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hw
  let F := [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]
  let G := (1091, b32 (trips - 1)) :: F
  have hs' : At s 907 G := hs.mono
    ⟨holds_lookup hs.2.2.2.2 rfl, holds_lookup hs.2.2.2.2 rfl,
      by rw [hWarp]; exact holds_lookup hs.2.2.2.2 rfl, trivial⟩
  have hBody (branch : Nat) : ((kernel.code.drop 907).take (1353 - 907)).all
      (fun ins => loaderPipelineCutOp 907 1353 branch (G.map Prod.fst) ins.op) = true := by
    kernel_rfl
  obtain ⟨t, front, stop, _, ht, htRun, _, htOrder⟩ :=
    prefixStableCut (by decide) hBody hs' hr he hOrder hSafe (fun _ => 0) (fun _ => false)
      (.inl (by omega)) (fun _ => rfl) (fun _ _ => rfl)
      (fun {_ _ event} _ _ _ _ _ => by cases event <;> rfl)
  obtain ⟨hTile, _⟩ := assignedCoordinates_valid hp hLo hHi
  have hTrip := (Mma.trips_bounds hp hb hTile).2.1
  change trips ≤ (p.kLength batch + 127) / 128 at hTrip
  have hLen := (hp.lengths batch hb).2.2
  have hFit : trips - 1 < 2 ^ 31 := by omega
  obtain ⟨pos, hBefore, u, rest, hu, huRun, _⟩ :=
    steadyGateFromSeed hFit (by kernel_rfl) (fun _ => by kernel_rfl)
      (by kernel_rfl) (by kernel_rfl) ht htRun he htOrder (by omega) hSafe
  refine ⟨batch, hb, hLo, hHi, ?_⟩
  change 11 ≤ trips
  by_contra! hShort
  have hSkipped : ¬ min (trips - 1) 9 < trips - 1 := by omega
  have huPc : u.pc = 1744 := by simpa only [ite_eq_right hSkipped] using hu.1
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun huRun
  have hMember : e ∈ (X.tr thread).drop pos := by
    apply List.mem_of_getElem? (i := j - pos)
    rw [List.getElem?_drop, Nat.add_sub_of_le hBefore]
    exact he
  have hRole : Holds u.regs F := (holds_append ..).mp hu.2.2.2.2 |>.2
  have hRange := loaderWalkEventRange warp (by decide : 174 ≤ 1744)
    (by rw [huPc]; decide) (ringShapeOfAt hu) hRole
    (fun _ => by kernel_rfl) hWalk e hMember
  omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
