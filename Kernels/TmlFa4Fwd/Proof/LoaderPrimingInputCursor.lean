-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVAdmission
public import Kernels.TmlFa4Fwd.Proof.LoaderInputSites
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
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Epilogue

/-- The input loader's selected trip and Bias coordinate registers. -/
def primingInputCursorFrame (p : Params) (l : Launch) (batch tile head : Nat) (warp : Fin 2) :
    List (Nat × Value) :=
  (1089, b32 (vPrimingResidual p batch tile)) :: (2535, b32 l.sharedBase) ::
    primingVTripFrame p batch tile head (14 + warp.val)

private theorem primingInputEventFloor :
    (kernel.code.drop 515).all (fun i => Thread.staysPastEvent 515 i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem primingInputFloorSegments : Assumptions.swExp2Sites.all (fun atPc =>
    match cuteExp2.matchAt kernel atPc with
    | some seg => decide (515 ≤ seg.stop)
    | none => false) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

/-- The selected-request cursor precedes every input-packet event in its loader lane. -/
theorem primingInputCursorBeforePacketEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g index batch : Nat} {event : Event}
    (hb : batch < p.batch) (hLow : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHigh : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (he : X.get (g, index) = some event) (hBounds : 515 ≤ event.pc ∧ event.pc < 1744) :
    ∃ warp : Fin 2, ∃ t pos,
      let coords := assignedCoordinates p batch (g / l.block)
      At t 488 (primingInputCursorFrame p l batch coords.1 coords.2 warp) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) none ∧ pos ≤ index := by
  have hHint : event.pc ∉ registerHintSites := by
    have hLo := hBounds.1
    have hHi := hBounds.2
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hAfter : 173 < event.pc := by have := hBounds.1; omega
  have hWarp : 14 ≤ warpIndex l g := by
    rcases roleBodyPcOfEvent hp hX he hAfter hHint with h | h
    · have := hBounds.2
      change event.pc = 9205 at h
      omega
    · have := hBounds.1
      split_ifs at h <;> omega
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hRole : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hWarp
  have hActive : g / l.block < tilePrefix p p.batch * p.heads :=
    hHigh.trans_le (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (by omega)))
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨b, hb', hLo', hHi', _, hKey, sh, votes, ⟨start⟩⟩ :=
    actualPrimingVAdmissionWithTrips hp hX hComplete hg hWarp hActive writes
  obtain ⟨_, _, hBatch⟩ := tileBatch_existsUnique p hActive
  have hbEq := (hBatch b ⟨hb', hLo', hHi'⟩).trans (hBatch batch ⟨hb, hLow, hHigh⟩).symm
  subst b
  let coords := assignedCoordinates p batch (g / l.block)
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  let pos := start.pos lane
  let t := start.state lane
  have hAt := start.checkpoint lane hl
  have hRun := (start.continuation lane hl).after_local (start.localSteps lane hl)
  rw [hLane] at hRun
  let row := primingLaneRow (Mma.trips p batch coords.1 - 1) (32 * warpIndex l g + lane)
  change 128 * (Mma.trips p batch coords.1 - 1) + 127 < 2 ^ 31 at hKey
  have hSigned : row < 2 ^ 31 := by
    dsimp only [row, primingLaneRow, kvCopyColumn]
    simp only [Bool.false_eq_true, ite_false]
    have hLow := Nat.mod_lt ((32 * warpIndex l g + lane) / 8) (by decide : 0 < 8)
    omega
  have hScratch : At t 488 (primingScratchFacts p l batch row 0) := by
    have hInitial := ((holds_append ..).mp ((holds_append ..).mp hAt.2.2.2.2).1).1
    exact hAt.mono ((holds_append ..).mp hInitial).1
  obtain ⟨_, hTrace, _, _⟩ := primingScratchIteration hp hX (i := pos)
    hb 0 (by simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using hSigned)
    writes hScratch hRun
  let mark : Event := ⟨506, .wr (scratchWordAccess l g 0 0)
    (b32 (primingScratchPage p batch row)).toBytes⟩
  have hMarkMem : mark ∈ (X.tr g).drop pos := by
    rw [hTrace]
    apply List.mem_append_left
    simp [mark, primingScratchEvents]
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hMarkMem
  rw [List.getElem?_drop] at hk
  have hMark := Thread.traceOrderOfPcFloor hX primingInputEventFloor primingInputFloorSegments
    (show X.get (g, pos + k) = some mark from hk) he (by change 506 < 515; decide) hBounds.1
  have hFrame :
      At t 488 (primingInputCursorFrame p l batch coords.1 coords.2 warp) := by
    have hHeld := hAt.2.2.2.2
    have hTrips := ((holds_append ..).mp hHeld).2
    refine hAt.mono ⟨?_, ?_, ?_⟩
    · exact holds_mem hHeld (by simp [coords, primingVAdmissionCarry])
    · exact holds_mem hHeld (by simp [primingVAdmissionCarry])
    · simpa only [hRole] using hTrips
  exact ⟨warp, t, pos, hFrame, hRun, by omega⟩

end PTX.Kernels.TmlFa4Fwd.Loader
