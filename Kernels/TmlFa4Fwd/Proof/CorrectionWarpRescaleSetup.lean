-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionWarpRendezvous
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleInitialize
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleOrdinal
import Kernels.TmlFa4Fwd.Flow.Code.Part124

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The single-block path goes to finalization. Otherwise both stages start with their exact
physical column addresses and the negative KV loop counter. -/
def correctionRescaleSetupFacts (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  let tile := (assignedCoordinates p batch (g / l.block)).1
  let blocks := Mma.trips p batch tile
  let F := correctionBeforeRescale p l g batch lane
  if blocks < 2 then F else
    (7278, remainingRescaleWord blocks) ::
      (rescaleStageAddresses l (warpLane l g lane) 0 ++
        rescaleStageAddresses l (warpLane l g lane) 1 ++ F)

set_option maxRecDepth 100000 in
private theorem rescaleSetupCore :
    ((kernel.code.drop 7989).take 17).all (fun ins => Assumptions.coreOp ins.op) = true := by
  kernel_rfl

private theorem rescaleSetupOut {l : Launch} {g : Nat} {t : TState}
    (hLo : 7989 ≤ t.pc) (hHi : t.pc < 8006) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hm : ins ∈ (kernel.code.drop 7989).take 17 := by
      apply List.mem_of_getElem? (i := t.pc - 7989)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp rescaleSetupCore _ hm)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

private theorem setupLinear {l : Launch} {g pc n : Nat} {t u : TState} {regs : List Nat}
    (hLo : 7989 ≤ pc) (hHi : pc + n ≤ 8006) (ht : t.pc = pc)
    (hWrites : ((kernel.code.drop pc).take n).all
      (fun i => regs.all (fun r => !(writesRegs i.op).contains r)) = true)
    (hFallthrough : ((kernel.code.drop pc).take (n - 1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hr : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧ ∀ r ∈ regs, u.regs r = t.regs r := by
  have hlo : pc ≤ t.pc := ht.ge
  have hhi : t.pc + n ≤ pc + n := by rw [ht]
  exact ⟨schedulerLocalTransport hFallthrough
    (fun ha hb => rescaleSetupOut (by omega) (by omega)) hr hlo hhi,
    fun _ h => schedulerLocalFrame hWrites hFallthrough hr hlo hhi h⟩

/-- A correction lane with its decoded KV count either skips directly to finalization
or seeds the exact rescale counter in its silent preheader. -/
theorem correctionLaneRescaleSetup {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch lane : Nat} {t : TState} (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (ht : At t 7989 (correctionBeforeRescale p l g batch lane)) :
    let blocks := Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1
    ∃ n v, run kernel Assumptions.all l (warpLane l g lane) n t = some v ∧
      At v (if blocks < 2 then 8447 else 8006) (correctionRescaleSetupFacts p l g batch lane) := by
  dsimp only
  let tile := (assignedCoordinates p batch (g / l.block)).1
  let blocks := Mma.trips p batch tile
  have hTile : 256 * tile < p.qLength batch := (assignedCoordinates_valid hp hLo hHi).1
  have hBlocks : blocks < 2 ^ 31 := by
    have hK := (hp.lengths batch hBatch).2.2
    have hCount := (Mma.trips_bounds hp hBatch hTile).2.1
    omega
  let thread := warpLane l g lane
  let F := correctionBeforeRescale p l g batch lane
  have hF : Holds t.regs F := ht.2.2.2.2
  obtain ⟨s, hs, hS⟩ := rescaleEntryCount l thread hBlocks t (ht.mono ⟨hF.1, trivial⟩)
  obtain ⟨hsA, hsFrame⟩ := setupLinear (regs := F.map Prod.fst) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hs
  have hSave := holdsSchedulerFrame hF hsFrame (fun _ hm => List.mem_map_of_mem hm)
  have hBranch : At s 7990 ((730, .pred (decide (blocks < 2))) :: F) :=
    hS.mono ⟨hS.2.2.2.2.1, hSave⟩
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_7990 (decide (blocks < 2)) hBranch hBranch.2.2.2.2.1 (by simp)
  obtain ⟨huA, _⟩ := setupLinear (regs := []) (by decide) (by decide) hBranch.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have hPC := hU.mono hU.2.2.2.2.2
  change ∃ n v, run kernel Assumptions.all l thread n t = some v ∧
    At v (if blocks < 2 then 8447 else 8006) (correctionRescaleSetupFacts p l g batch lane)
  by_cases hSkip : blocks < 2
  · simp only [hSkip, ↓reduceIte]
    have h := hPC
    simp only [hSkip, decide_true, ↓reduceIte] at h
    have hEq : correctionRescaleSetupFacts p l g batch lane = F := by
      unfold correctionRescaleSetupFacts
      rw [ite_eq_left hSkip]
    exact ⟨_, u, run_comp hsA huA, hEq.symm ▸ h⟩
  · have hLive : At u 7991 F := by
      simpa only [hSkip, decide_false, Bool.false_eq_true, ↓reduceIte] using hPC
    have hBase0 := holds_lookup hLive.2.2.2.2
      (show F.lookup 1629 = some (b32 (outputAddress l thread 0 0)) from rfl)
    have hBase1 := holds_lookup hLive.2.2.2.2
      (show F.lookup 1633 = some (b32 (outputAddress l thread 1 0)) from rfl)
    obtain ⟨v, hv, hV⟩ := rescaleInitialize l thread (by omega : 2 ≤ blocks) hBlocks u
      (hLive.mono ⟨hBase0, hBase1, hLive.2.2.2.2.1, trivial⟩)
    obtain ⟨hvA, hvFrame⟩ := setupLinear (regs := F.map Prod.fst)
      (by decide) (by decide) hLive.1 (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hv
    have hPreserved := holdsSchedulerFrame hLive.2.2.2.2 hvFrame
      (fun _ hm => List.mem_map_of_mem hm)
    have hEq : correctionRescaleSetupFacts p l g batch lane =
        (7278, remainingRescaleWord blocks) ::
          (rescaleStageAddresses l thread 0 ++ rescaleStageAddresses l thread 1 ++ F) := by
      unfold correctionRescaleSetupFacts
      rw [ite_eq_right hSkip]
    refine ⟨_, v, run_comp (run_comp hsA huA) hvA, ?_⟩
    rw [ite_eq_right hSkip, hEq]
    exact hV.mono ⟨hV.2.2.2.2.1, (holds_append _ _ _).2 ⟨hV.2.2.2.2.2, hPreserved⟩⟩

/-- The exact correction trip count bounds the repeated waits in every observed suffix,
including one that stops in the silent loop preheader. -/
theorem correctionRescaleBoundFromSetup {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch lane : Nat} {t : TState} (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (ht : At t 7989 (correctionBeforeRescale p l g batch lane))
    {es : List Event} {visits : List Visit} (stage : Fin 2)
    (hw : Walk kernel Assumptions.all l (warpLane l g lane) t es visits) :
    es.countP (isRescaleStageWait stage) ≤
      Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1 := by
  let tile := (assignedCoordinates p batch (g / l.block)).1
  let blocks := Mma.trips p batch tile
  have hTrips : blocks ≤ (p.kLength batch + 127) / 128 :=
    (Mma.trips_bounds hp hBatch (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hK := (hp.lengths batch hBatch).2.2
  obtain ⟨_, u, hRun, hu⟩ := correctionLaneRescaleSetup hp hBatch hLo hHi ht
  rcases Mma.advanceWalkLocals hRun hw with rfl | ⟨_, _, _, hRest⟩
  · simp
  have hEntry : u.pc = (if blocks < 2 then 8447 else 8006) := hu.1
  change es.countP (isRescaleStageWait stage) ≤ blocks - 1
  by_cases hSkip : blocks < 2
  · have hPc : u.pc = 8447 := hEntry.trans (ite_eq_left hSkip)
    rw [correctionRescaleMarkedNone stage hPc.ge hRest]
    exact Nat.zero_le _
  have hPc : u.pc = 8006 := hEntry.trans (ite_eq_right hSkip)
  have hSeed : u.regs 7278 = some (b32 (2^32-blocks)) := by
    have h := hu.2.2.2.2
    unfold correctionRescaleSetupFacts at h
    rw [ite_eq_right hSkip] at h
    exact h.1
  exact correctionRescaleMarkedBound stage hPc (by rw [hu.2.1]; decide)
    (Nat.le_of_not_gt hSkip) (by omega) hSeed hRest

end
end PTX.Kernels.TmlFa4Fwd.Correction
