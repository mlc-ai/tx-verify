-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyOperandReload
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
import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

set_option maxRecDepth 100000 in
/-- A peer with a steady shuffle ordinal actually enters the steady loop. -/
theorem steadyShuffleBodyFloor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane j batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hMany : 11 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hFloor : 917 ≤ e.pc) (hShfl : Execution.isShfl e = true)
    (hCount : primingSearchShuffleCount batch + 640 <
      ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl) :
    1396 ≤ e.pc := by
  have hSafe : ∀ f, e.kind ≠ .ub f := by
    intro f h
    obtain ⟨pc, kind⟩ := e
    change kind = .ub f at h
    subst kind
    cases hShfl
  obtain ⟨pos, hOrder, s, ending, hs, hr, _⟩ :=
    steadyFirstArmOfDemand hp hX hg hw hl writes hCTA hb hLo hHi hMany he
      hFloor (.inr ⟨hShfl, hCount⟩) hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  obtain ⟨hTile, _⟩ := assignedCoordinates_valid hp hLo hHi
  have hTid : tid < 512 := by unfold tid; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  obtain ⟨u, hu, huAt⟩ := steadyPagePrelude (g := thread) hp hb (by omega) hTid hs
  have huRun := hr.after_local_nonempty hu (traceAfterObservedEvent he hOrder)
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWarp : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hw
  have hRole : Holds u.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] :=
    ⟨holds_lookup huAt.2.2.2.2 rfl, by rw [hWarp]; exact holds_lookup huAt.2.2.2.2 rfl, trivial⟩
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun huRun
  have hMember : e ∈ (X.tr thread).drop pos := by
    apply List.mem_of_getElem? (i := j - pos)
    rw [List.getElem?_drop, Nat.add_sub_of_le hOrder]
    exact he
  exact (loaderWalkEventRange warp (by decide : 174 ≤ 1396)
    (by rw [huAt.1]; decide) (ringShapeOfAt huAt) hRole (fun _ => by kernel_rfl)
    hWalk e hMember).1

/-- The prior K shuffles offset every V shuffle by 32 in a steady traversal. -/
def steadyOperandRank (value : Bool) : Nat := if value then 32 else 0

set_option maxRecDepth 100000 in
/-- An ordinal in a steady packet half forces the observed peer to the associated pointer reload. -/
theorem steadyShuffleSlotFloor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hMany : 11 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1)
    (hMin : 9 ≤ iteration) (value : Bool) (slot : Fin 2)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hFloor : 1396 ≤ e.pc) (hShfl : Execution.isShfl e = true)
    (hDemand : SteadyRoundDemand p l X g lane batch iteration j e)
    (hEnough : primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) +
      steadyOperandRank value + 16 * slot.val ≤
        ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl)
    (hLater : ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl <
      primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) + 64) :
    (steadyPointerReload value slot).pc < e.pc := by
  have hSafe : ∀ f, e.kind ≠ .ub f := by
    intro f h
    obtain ⟨pc, kind⟩ := e
    change kind = .ub f at h
    subst kind
    cases hShfl
  obtain ⟨_, _, pos, hOrder, s, ending, hs, hr, hsRank⟩ :=
    steadyRoundEntryOfEvent hp hX hg hw hl writes hCTA hb hLo hHi hMany hMin
      he hFloor hSafe hDemand
  let cut := (steadyPointerReload value slot).pc + 1
  have hRange : 174 ≤ 1396 ∧ 1396 ≤ cut ∧ cut ≤ 1901 := by
    cases value <;> fin_cases slot <;> decide
  have hAudit (branch : Nat) : ((kernel.code.drop 1396).take (cut - 1396)).all
      (fun ins => loaderPipelineCutOp 1396 cut branch [] ins.op) = true := by
    cases value <;> fin_cases slot <;> kernel_rfl
  have hRanked : (((kernel.code.drop 1396).take (cut - 1396)).zipIdx 1396).all
      (fun (i, pc) => LoaderRankedInstr cut pc i) = true := by
    cases value <;> fin_cases slot <;> kernel_rfl
  have hCount : loaderShuffleTail cut 1396 = steadyOperandRank value + 16 * slot.val := by
    cases value <;> fin_cases slot <;> kernel_rfl
  obtain ⟨t, front, stop, _, ht, htRun, htRank, htBefore⟩ :=
    prefixRankedShuffleCut (F := []) hRange hAudit hRanked (hs.mono trivial) hr he hOrder
      (.inr ⟨hShfl, by rw [hsRank, hCount]; omega⟩) hSafe
  have hNextRange : 174 ≤ cut ∧ cut ≤ 1741 ∧ 1741 ≤ 1901 := by
    cases value <;> fin_cases slot <;> decide
  have hNext (branch : Nat) : ((kernel.code.drop cut).take (1741 - cut)).all
      (fun ins => loaderPipelineCutOp cut 1741 branch [] ins.op) = true := by
    cases value <;> fin_cases slot <;> kernel_rfl
  have hNextRanked : (((kernel.code.drop cut).take (1741 - cut)).zipIdx cut).all
      (fun (i, pc) => LoaderRankedInstr 1741 pc i) = true := by
    cases value <;> fin_cases slot <;> kernel_rfl
  have hNextCount : loaderShuffleTail 1741 cut =
      64 - (steadyOperandRank value + 16 * slot.val) := by
    cases value <;> fin_cases slot <;> kernel_rfl
  refine (loaderRankedEventBounds hNextRange hNext hNextRanked ht htRun he htBefore ?_).1
  rw [htRank, hsRank, hCount, hNextCount]
  have hSlot := slot.isLt
  cases value <;> simp only [steadyOperandRank, ↓reduceIte, Bool.false_eq_true] <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
