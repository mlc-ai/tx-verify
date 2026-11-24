-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringValueCopyLength
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmValueSite
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeySite
import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundEntry
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

set_option maxRecDepth 100000 in
/-- Both warm cache packets use the same row predicate and byte selector. -/
private theorem warmCacheSourceSizeAtRank {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g j batch round : Nat} {sp : AsyncCopy.Spec}
    (hWarp : 14 ≤ warpIndex l g) (hActive : g/l.block < tilePrefix p p.batch*p.heads)
    (hB : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (value : Bool) (pair : Fin 16) (upper : Bool)
    (he : X.get (g,j) = some
      ⟨packetPlanePc (recurringPacketSite (if value then 1 else 0)) pair upper,.copy sp⟩)
    (hVectorRank : ((X.tr g).take j).countP Execution.isShfl =
      primingSearchShuffleCount batch+64+64*round+(if value then 32 else 0)+2*pair.val+2) :
    sp.src.size = 16 := by
  let lane := laneOf l g
  let co := assignedCoordinates p batch (g/l.block)
  let trips := Mma.trips p batch co.1
  let thr := warpLane l g lane
  let tid := thr%l.block
  let tile := trips-2-round
  let row := 128*tile+tid/8%8
  let len := p.kLength batch
  let pc := packetPlanePc (recurringPacketSite (if value then 1 else 0)) pair upper
  let target : Event := ⟨pc,.copy sp⟩
  have hSelf : thr = g := by
    unfold thr warpLane lane laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g%l.block) 32
    omega
  have hRecord : X.get (thr,j) = some target := by rw [hSelf]; exact he
  have hRank : ((X.tr thr).take j).countP Execution.isShfl =
      primingSearchShuffleCount batch+64+64*round+(if value then 32 else 0)+2*pair.val+2 := by
    rw [hSelf]
    exact hVectorRank
  have hDemand : WarmRoundDemand p l X g lane batch round j target := by
    refine ⟨.inr ?_, .inr ?_⟩
    · change pc < 1353
      cases value <;> fin_cases pair <;> cases upper <;> decide
    · change _ < ((X.tr thr).take j).countP Execution.isShfl
      rw [hRank]; omega
  have hPc : 1002 < pc := by cases value <;> fin_cases pair <;> cases upper <;> decide
  have hSafe : ∀ f, target.kind ≠ .ub f := by intro f h; cases h
  obtain ⟨hRoundIn,hRound,hUpper,pos,hPos,s,out,hs,hsRun,hsRank⟩ :=
    warmRoundEntryOfEvent hp hX (event_thread_lt hX he) hWarp
      (Nat.mod_lt _ (by decide)) (fun _ _ _ _ => loaderOutputWrites hFrame)
      hActive hB hLo hHi hRecord (show 917 ≤ pc by omega) hSafe hDemand
  change round < min (trips-1) 9 at hRoundIn
  change round ≤ trips-2 at hRound
  change 128*(trips-2)+127 < 2^31 at hUpper
  have hSecond : 2 ≤ trips := by omega
  have hTrips : trips ≤ (len+127)/128 :=
    (Mma.trips_bounds hp hB (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen : len < 2^31 := by have := (hp.lengths batch hB).2.2; omega
  have hTid : tid < 512 := by unfold tid; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hLane : tid/8%8 < 8 := Nat.mod_lt _ (by decide)
  have hResidual : 8*pair.val < len-row := recurringKeyResidualLive pair hSecond hTrips hLane
  have hRow : row < len := by omega
  have hHigh : trips-2 < 2^31 := by omega
  let F := [(1116,b32 (trips-2)),(7174,b32 round),(1086,b32 len)]
  let G := (1061,b32 tid)::F
  have hs' : At s 917 G := hs.mono ⟨holds_lookup hs.2.2.2.2 rfl,
    holds_lookup hs.2.2.2.2 rfl, holds_lookup hs.2.2.2.2 rfl,
    holds_lookup hs.2.2.2.2 rfl, trivial⟩
  obtain ⟨a,before,out',_,ha,haRun,haRank,haBefore⟩ :=
    prefixRankedShuffleCut (start := 917) (stop := 981) (by decide)
      (by intro n; kernel_rfl) (by kernel_rfl) hs' hsRun hRecord hPos
      (.inl (show 981 ≤ pc by omega)) hSafe
  obtain ⟨b,hb,hB⟩ := keyCopyLaneOffsetCore (g := thr) hTid false a
    (ha.mono ⟨ha.2.2.2.2.1,trivial⟩)
  obtain ⟨hb',hBRegs⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide)
    ha.1 (by kernel_rfl) (by kernel_rfl) hb
  have hbRun := haRun.after_local_nonempty (run_rtg hb') (traceAfterObservedEvent hRecord haBefore)
  let J := (1979,b32 (tid/8%8))::F
  have hAt : At b 983 J := hB.mono ⟨hB.2.2.2.2.1,
    holdsSchedulerFrame ha.2.2.2.2.2 hBRegs (fun _ h => List.mem_map_of_mem h)⟩
  obtain ⟨c,more,out'',_,hc,hcRun,hcRank,hcBefore⟩ :=
    prefixRankedShuffleCut (start := 983) (stop := 996) (by decide)
      (by intro n; kernel_rfl) (by kernel_rfl) hAt hbRun hRecord haBefore
      (.inl (show 996 ≤ pc by omega)) hSafe
  have hCore := warmKeyCopyResidualCore (l := l) (g := thr) hRound hHigh hLane hRow hLen
  obtain ⟨d,hd,hD⟩ := loaderStraightCore (by decide) (by kernel_rfl) hCore c
    (hc.mono ⟨holds_lookup hc.2.2.2.2 rfl, holds_lookup hc.2.2.2.2 rfl,
      holds_lookup hc.2.2.2.2 rfl, holds_lookup hc.2.2.2.2 rfl,trivial⟩)
  have hdRun := hcRun.after_local_nonempty (run_rtg hd) (traceAfterObservedEvent hRecord hcBefore)
  have hSeedRank : loaderShuffleTail 981 917 = 0 ∧ loaderShuffleTail 996 983 = 0 := by
    constructor <;> kernel_rfl
  have hNth : ((X.tr thr).take j).countP Execution.isShfl =
      ((X.tr thr).take (pos+before.length+more.length)).countP Execution.isShfl+
        (if value then 32 else 0)+2*pair.val+2 := by
    change ((X.tr thr).take (pos+before.length+more.length)).countP Execution.isShfl =
      ((X.tr thr).take (pos+before.length)).countP Execution.isShfl +
        loaderShuffleTail 996 983 at hcRank
    change ((X.tr thr).take (pos+before.length)).countP Execution.isShfl =
      ((X.tr thr).take pos).countP Execution.isShfl + loaderShuffleTail 981 917 at haRank
    change ((X.tr thr).take pos).countP Execution.isShfl =
      primingSearchShuffleCount batch+64+64*round at hsRank
    rw [hcRank,haRank,hSeedRank.1,hSeedRank.2,hsRank,hRank]
    simp
  cases value
  · exact recurringKeyCopyFullFromResidual false pair upper hResidual (by omega) hD hdRun
      hcBefore hRecord (by
        simpa only [thr,lane,laneOf,Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using hNth)
  · exact recurringValueCopyFullFromResidual false pair upper hResidual (by omega) hD hdRun
      hcBefore hRecord hNth

/-- An actual warm K copy uses the full source size of its live row. -/
theorem WarmKeySite.fullSourceSize {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g j : Nat} {sp : AsyncCopy.Spec} (h : WarmKeySite X (g,j) sp) : sp.src.size = 16 := by
  have hWarp := h.issuer hp hX
  have hActive := h.active hp hX hFrame
  obtain ⟨batch,hB,round,pair,upper,hVector⟩ := h.vector hp hX hFrame hWarp hActive
  exact warmCacheSourceSizeAtRank hp hX hFrame hWarp hActive hB hVector.1 hVector.2.1
    false pair upper hVector.2.2.1
    (by simpa only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using hVector.2.2.2)

/-- An actual warm V copy reuses the full-size selector of its live K row. -/
theorem WarmValueSite.fullSourceSize {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g j : Nat} {sp : AsyncCopy.Spec} (h : WarmValueSite X (g,j) sp) : sp.src.size = 16 := by
  have hWarp := h.issuer hp hX
  have hActive := h.active hp hX hFrame
  obtain ⟨batch,hB,round,pair,upper,hLo,hHi,he,hRank⟩ := h.vector hp hX hFrame hWarp hActive
  exact warmCacheSourceSizeAtRank hp hX hFrame hWarp hActive hB hLo hHi true pair upper he hRank

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
