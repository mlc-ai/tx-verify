-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringValueCopyLength
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadySite
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

set_option maxRecDepth 100000 in
/-- The actual steady K and V vectors use the same full-vector selector. -/
private theorem steadyCacheVectorFullSourceSize {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g j : Nat} {sp : AsyncCopy.Spec}
    (value : Bool) (pair : Fin 16) (upper : Bool)
    (he : X.get (g,j) = some
      ⟨packetPlanePc (recurringPacketSite (if value then 3 else 2)) pair upper,.copy sp⟩) :
    sp.src.size = 16 := by
  have hWarp := copyLoaderWarp hp hX (show X.Copy (g,j) sp from ⟨_,he⟩)
  let lane := laneOf l g
  let thr := warpLane l g lane
  let tid := thr%l.block
  let pc := packetPlanePc (recurringPacketSite (if value then 3 else 2)) pair upper
  let target : Event := ⟨pc,.copy sp⟩
  have hSelf : thr = g := by
    unfold thr warpLane lane laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g%l.block) 32
    omega
  have hRecord : X.get (thr,j) = some target := by rw [hSelf]; exact he
  have hPc : 1396 ≤ pc ∧ pc < 1741 ∧ 1468 < pc := by
    cases value <;> fin_cases pair <;> cases upper <;> decide
  have hCTA := loaderOwnPrefixEventRequiresActiveTile hp hX hWarp
    (hp.cuQ_protected (fun _ _ _ _ => loaderOutputWrites hFrame)) he
    (show 297 < pc by omega) (show pc < 1862 by omega)
  have hg : g < l.threads := event_thread_lt hX he
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hSafe : ∀ f, target.kind ≠ .ub f := by intro f h; cases h
  obtain ⟨batch,hB,hLo,hHi,hMany,round,hMin,_,hOrd⟩ :=
    actualSteadyEventRound hp hX hg hWarp hLane
      (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA hRecord ⟨hPc.1,hPc.2.1⟩ hSafe
  let co := assignedCoordinates p batch (g/l.block)
  let trips := Mma.trips p batch co.1
  let tile := trips-2-round
  let row := 128*tile+tid/8%8
  let len := p.kLength batch
  have hPair := pair.isLt
  have hTail : loaderShuffleTail 1741 pc = 64-((if value then 32 else 0)+2*pair.val+2) := by
    cases value <;> fin_cases pair <;> cases upper <;> kernel_rfl
  change ((X.tr thr).take j).countP Execution.isShfl + loaderShuffleTail 1741 pc =
    primingSearchShuffleCount batch+640+64*(round-9)+64 at hOrd
  have hRank : ((X.tr thr).take j).countP Execution.isShfl =
      primingSearchShuffleCount batch+640+64*(round-9)+(if value then 32 else 0)+2*pair.val+2 := by
    rw [hTail] at hOrd
    cases value <;> simp at hOrd ⊢ <;> omega
  have hDemand : SteadyRoundDemand p l X g lane batch round j target :=
    ⟨.inr (show pc < 1744 by omega),.inr (by
      change _ < ((X.tr thr).take j).countP Execution.isShfl
      rw [hRank]; omega)⟩
  obtain ⟨hRound,hUpper,pos,hPos,s,out,hs,hsRun,hsRank⟩ :=
    steadyRoundEntryOfEvent hp hX hg hWarp hLane (fun _ _ _ _ => loaderOutputWrites hFrame)
      hCTA hB hLo hHi hMany hMin hRecord hPc.1 hSafe hDemand
  change round ≤ trips-2 at hRound
  change 128*(trips-2)+127 < 2^31 at hUpper
  change 11 ≤ trips at hMany
  have hTrips : trips ≤ (len+127)/128 :=
    (Mma.trips_bounds hp hB (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen : len < 2^31 := by have := (hp.lengths batch hB).2.2; omega
  have hLaneRow : tid/8%8 < 8 := Nat.mod_lt _ (by decide)
  have hResidual : 8*pair.val < len-row :=
    recurringKeyResidualLive pair (by omega) hTrips hLaneRow
  have hRow : row < len := by omega
  have hHigh : 128*(trips-2) < 2^31 := by omega
  let F := [(1146,b32 (tid/8%8)),(1086,b32 len)]
  have hCore := steadyKeyCopyTileCore (l := l) (g := thr) hRound hHigh
  obtain ⟨a,ha,hA⟩ := hCore s (hs.mono
    ⟨holds_lookup hs.2.2.2.2 rfl, holds_lookup hs.2.2.2.2 rfl,trivial⟩)
  obtain ⟨ha',hARegs⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide)
    hs.1 (by kernel_rfl) (by kernel_rfl) ha
  have haRun := hsRun.after_local_nonempty (run_rtg ha') (traceAfterObservedEvent hRecord hPos)
  let G := [(1144,b32 tile),(1145,b32 (128*tile))]++F
  have hsF : Holds s.regs F := ⟨holds_lookup hs.2.2.2.2 rfl,
    holds_lookup hs.2.2.2.2 rfl,trivial⟩
  have hAt : At a 1398 G := hA.mono ((holds_append ..).mpr
    ⟨hA.2.2.2.2, holdsSchedulerFrame hsF hARegs (fun _ h => List.mem_map_of_mem h)⟩)
  obtain ⟨b,before,out',_,hb,hbRun,hbRank,hbBefore⟩ :=
    prefixRankedShuffleCut (start := 1398) (stop := 1464) (by decide)
      (by intro n; kernel_rfl) (by kernel_rfl) hAt haRun hRecord hPos
      (.inl (show 1464 ≤ pc by omega)) hSafe
  have hResidualCore := steadyKeyCopyResidualCore (l := l) (g := thr) hRow hLen
  obtain ⟨c,hc,hC⟩ := loaderStraightCore (by decide) (by kernel_rfl) hResidualCore b hb
  have hcRun := hbRun.after_local_nonempty (run_rtg hc) (traceAfterObservedEvent hRecord hbBefore)
  have hZero : loaderShuffleTail 1464 1398 = 0 := by kernel_rfl
  have hNth : ((X.tr thr).take j).countP Execution.isShfl =
      ((X.tr thr).take (pos+before.length)).countP Execution.isShfl+
        (if value then 32 else 0)+2*pair.val+2 := by
    rw [hbRank,hZero,hsRank,hRank]
    simp
  cases value
  · exact recurringKeyCopyFullFromResidual true pair upper hResidual (by omega) hC hcRun
      hbBefore hRecord (by
        simpa only [thr,lane,laneOf,Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using hNth)
  · exact recurringValueCopyFullFromResidual true pair upper hResidual (by omega) hC hcRun
      hbBefore hRecord hNth

/-- An actual steady K copy uses the full source size of its live row. -/
theorem SteadyKeySite.fullSourceSize {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g j : Nat} {sp : AsyncCopy.Spec} (h : SteadyKeySite X (g,j) sp) : sp.src.size = 16 := by
  obtain ⟨pair,upper,he⟩ := h
  exact steadyCacheVectorFullSourceSize hp hX hFrame false pair upper he

/-- An actual steady V copy reuses the full-size selector of its live K row. -/
theorem SteadyValueSite.fullSourceSize {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g j : Nat} {sp : AsyncCopy.Spec} (h : SteadyValueSite X (g,j) sp) : sp.src.size = 16 := by
  obtain ⟨pair,upper,he⟩ := h
  exact steadyCacheVectorFullSourceSize hp hX hFrame true pair upper he

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
