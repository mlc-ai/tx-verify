-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaScanProgress
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
import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame
public import Kernels.TmlFa4Fwd.Proof.MmaFallbackEntry
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof PTX.Assumption Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (mmaStepReg mmaWrites entryFacts startupFacts
  descriptorShufflePos schedulerAbiAtDescriptorWithOrdinal firstGroupRouteKeeping
  fallbackAbi initializeFallbackSearch advanceFallbackSearch groupScanFacts)

private def scanRootRegs : List Nat := [7203, 2535, 7502, 7503, 7506]

private def scanRootBoundary : Fin 2 → Nat
  | 0 => 1917
  | 1 => 1982

private theorem scanRootBoundaryAudit : ∀ boundary : Fin 2,
    let floor := scanRootBoundary boundary
    (kernel.code.drop floor).all (fun i => Thread.staysPastEvent floor i.op) = true ∧
      Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
        | some seg => decide (floor ≤ seg.stop)
        | none => false) = true := by decide +kernel

private theorem scanRootFloor {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    (boundary : Fin 2) (h : TraceReach kernel Assumptions.all l g s es u)
    (hs : scanRootBoundary boundary ≤ s.pc) : scanRootBoundary boundary ≤ u.pc := by
  have audited := scanRootBoundaryAudit boundary
  induction h with
  | refl => exact hs
  | tau hStep _ ih =>
    exact ih (Thread.eventTailStepOfAudit audited.1 audited.2 hs (.inl ⟨rfl, hStep⟩))
  | event hStep _ ih =>
    exact ih (Thread.eventTailStepOfAudit audited.1 audited.2 hs (.inr ⟨_, rfl, hStep⟩))

private theorem scanRootStep {l : Launch} {g r : Nat} {s u : TState} {e : Option Event}
    (hLo : 1917 ≤ s.pc) (hHi : s.pc < 1982) (hReg : r ∈ scanRootRegs)
    (hStep : WStep kernel Assumptions.all l g s e u) : u.regs r = s.regs r := by
  apply mmaStepReg (by omega) (by omega) _ hStep
  intro i hc
  have hCode : ((kernel.code.drop 1917).take (1982 - 1917)).all
      (fun i => scanRootRegs.all (fun r => !(mmaWrites i.op).contains r)) = true := by
    decide +kernel
  have hAt : ((kernel.code.drop 1917).take (1982 - 1917))[s.pc - 1917]? = some i := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
  have hIns := List.all_eq_true.mp hCode i (List.mem_of_getElem? hAt)
  simpa using List.all_eq_true.mp hIns r hReg

private theorem scanRootsPreserved {l : Launch} {g r : Nat} {s u : TState} {es : List Event}
    (h : TraceReach kernel Assumptions.all l g s es u)
    (hs : 1917 ≤ s.pc) (hu : u.pc < 1982) (hr : r ∈ scanRootRegs) :
    u.regs r = s.regs r := by
  have lower {a b : TState} {e : Option Event} (ha : 1917 ≤ a.pc)
      (he : WStep kernel Assumptions.all l g a e b) : 1917 ≤ b.pc :=
    Thread.eventTailStepOfAudit (scanRootBoundaryAudit 0).1 (scanRootBoundaryAudit 0).2 ha he
  induction h with
  | refl => rfl
  | @tau t v u es hStep hTail ih =>
    have ht : t.pc < 1982 := by
      by_contra! hBad
      exact Nat.not_le_of_lt hu (scanRootFloor 1 (.tau hStep hTail) hBad)
    exact (ih (lower hs (.inl ⟨rfl, hStep⟩)) hu).trans
      (scanRootStep hs ht hr (.inl ⟨rfl, hStep⟩))
  | @event t v u es e hStep hTail ih =>
    have ht : t.pc < 1982 := by
      by_contra! hBad
      exact Nat.not_le_of_lt hu (scanRootFloor 1 (.event hStep hTail) hBad)
    exact (ih (lower hs (.inr ⟨_, rfl, hStep⟩)) hu).trans
      (scanRootStep hs ht hr (.inr ⟨_, rfl, hStep⟩))

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
include hp hMax hg

/-- At the actual first group broadcast, the MMA lane retains the launch batch and pointers
from the descriptor shuffle. -/
theorem firstGroupScanLaunchFrame (hw : warpIndex l g = 12) (hProtected : DrainCuQProtected p X) :
    ∃ j e t o, X.get (g, j) = some e ∧ X.ShflK (g, j) 10 ∧ e.pc = 1980 ∧
      e.kind = .shfl .idx
        (b32 (∑ k ∈ Finset.range (laneOf l g + 1), groupLaneTiles p 0 k))
        31 31 (b32 (tilePrefix p (min p.batch 31))) true ∧
      At t 1981 [(7198, b32 (tilePrefix p (min p.batch 31))),
        (7197, b32 (∑ k ∈ Finset.range (laneOf l g + 1), groupLaneTiles p 0 k)),
        (1180, b32 (laneOf l g)), (7139, b32 p.heads), (1072, b32 (g / l.block)),
        (7196, b32 (groupLaneTiles p 0 (laneOf l g))),
        (7203, b32 p.batch), (2535, b32 l.sharedBase), (7502, b64 p.cuQBase),
        (7503, b64 p.usedKBase), (7506, b64 p.cuQBase)] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j + 1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j + 1)) o := by
  obtain ⟨j, e, t, o, he, hShfl, hSite, hKind, ht, hPrefix, hTail⟩ :=
    firstGroupScanTotalWithTiles hp hMax hg hw hProtected
  obtain ⟨s, _, _, hDesc, _, hs, hDescPrefix, _⟩ :=
    schedulerAbiAtDescriptorWithOrdinal hp hMax hg hw
  have hOrder : descriptorShufflePos (laneOf l g) < j :=
    Thread.traceOrderOfPcFloor hMax.1 (scanRootBoundaryAudit 0).1 (scanRootBoundaryAudit 0).2
      hDesc he (by change 1916 < 1917; decide) (by rw [hSite]; decide)
  let n := descriptorShufflePos (laneOf l g) + 1
  have hSplit := List.take_append_drop n ((X.tr g).take (j + 1))
  rw [List.take_take, Nat.min_eq_left (show n ≤ j + 1 by omega)] at hSplit
  have hBetween := hDescPrefix.after_returned_prefix (hSplit.symm ▸ hPrefix)
  have hKeep {r : Nat} (hr : r ∈ scanRootRegs) : t.regs r = s.regs r :=
    scanRootsPreserved hBetween.returning_reach (by rw [hs.1]) (by rw [ht.1]; decide) hr
  have hBatch : t.regs 7203 = some (b32 p.batch) := (hKeep (by decide)).trans
    (holds_mem hs.2.2.2.2 (by simp [entryFacts]))
  have hShared : t.regs 2535 = some (b32 l.sharedBase) := (hKeep (by decide)).trans
    (holds_mem hs.2.2.2.2 (by simp [entryFacts, startupFacts]))
  have hCuQ : t.regs 7502 = some (b64 p.cuQBase) := (hKeep (by decide)).trans
    (holds_mem hs.2.2.2.2 (by simp [entryFacts, startupFacts]))
  have hUsedK : t.regs 7503 = some (b64 p.usedKBase) := (hKeep (by decide)).trans
    (holds_mem hs.2.2.2.2 (by simp [entryFacts, startupFacts]))
  have hCuQScan : t.regs 7506 = some (b64 p.cuQBase) := (hKeep (by decide)).trans
    (holds_mem hs.2.2.2.2 (by simp [entryFacts, startupFacts]))
  refine ⟨j, e, t, o, he, hShfl, hSite, hKind, ht.mono ?_, hPrefix, hTail⟩
  exact ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1,
    ht.2.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.2.2.1, hBatch, hShared, hCuQ, hUsedK, hCuQScan, trivial⟩

/-- Every maximal MMA lane assigned to the first scheduler group reaches the chosen
group with the scanned prefixes and the original launch operands. -/
theorem firstGroupSelectionStart (hw : warpIndex l g = 12) (hProtected : DrainCuQProtected p X)
    (hFirst : g / l.block < tilePrefix p (min p.batch 31) * p.heads) :
    ∃ pos e t u o, 0 < pos ∧ pos ≤ (X.tr g).length ∧
      X.get (g, pos - 1) = some e ∧ e.pc = 1980 ∧ t.pc = 1981 ∧
      ((X.tr g).take pos).countP Execution.isShfl = 11 ∧
      (pos = (X.tr g).length → Step.Released l X g) ∧
      At u 2042 [(7199, b32 0), (7203, b32 p.batch),
        (7198, b32 (∑ i ∈ Finset.range 32, groupLaneTiles p 0 i)),
        (7197, b32 (∑ i ∈ Finset.range (laneOf l g + 1), groupLaneTiles p 0 i)),
        (7200, b32 (tilePrefix p (min p.batch 31) * p.heads)), (7139, b32 p.heads),
        (1072, b32 (g / l.block)), (7196, b32 (groupLaneTiles p 0 (laneOf l g))),
        (7502, b64 p.cuQBase), (7503, b64 p.usedKBase), (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o := by
  obtain ⟨j, e, t, o, he, hShfl, hSite, hKind, ht, hPrefix, hTail⟩ :=
    firstGroupScanLaunchFrame hp hMax hg hw hProtected
  have hCta : g / l.block < 2 ^ 31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  obtain ⟨u, hLocal, hAt, hKeep⟩ := firstGroupRouteKeeping hp g hCta (by at_select ht)
  have hTotal : (∑ i ∈ Finset.range 32, groupLaneTiles p 0 i) =
      tilePrefix p (min p.batch 31) := by
    simpa [tilePrefix, Nat.min_comm] using
      (groupTiles_eq p (Nat.zero_le p.batch) (by decide : 32 ≤ 32))
  have hIsShuffle : Execution.isShfl e = true := by
    cases e with
    | mk site kind =>
      change kind = _ at hKind
      subst kind
      rfl
  have hCount := Flow.countP_take_succ he hIsShuffle
  rw [hShfl.2] at hCount
  have hRelease : e.kind.resume ≠ .blocking false := by rw [hKind]; intro h; cases h
  refine ⟨j + 1, e, t, u, o, by omega, len_of_get he, by simpa only [Nat.add_sub_cancel] using he,
    hSite, ht.1, hCount, releasedIfLast he hRelease,
    ⟨by simpa only [ite_eq_left hFirst] using hAt.1, hAt.2.1, hAt.2.2.1,
      hAt.2.2.2.1, ?_⟩, hPrefix, run_rtg hLocal, hTail⟩
  refine ⟨(hAt.2.2.2.2.2.1), (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
    (hKeep _ (by decide)).trans ?_, (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
    hAt.2.2.2.2.1, (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
    (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
    (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
    (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
    (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
    (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl), trivial⟩
  rw [hTotal]
  exact holds_lookup ht.2.2.2.2 rfl

/-- A maximal MMA lane beyond the first cutoff reaches the second group's actual
lane-indexed read preparation, with the first group's work and the original launch pointers. -/
theorem firstFallbackGroupReached (hw : warpIndex l g = 12) (hProtected : DrainCuQProtected p X)
    (hBatch : 31 < p.batch) (hCut : tilePrefix p 31 * p.heads ≤ g / l.block) :
    let cta := g / l.block
    ∃ pos e t u o, 0 < pos ∧ pos ≤ (X.tr g).length ∧
      X.get (g, pos - 1) = some e ∧ e.pc = 1980 ∧ t.pc = 1981 ∧
      ((X.tr g).take pos).countP Execution.isShfl = 11 ∧
      (pos = (X.tr g).length → Step.Released l X g) ∧
      At u 1993 ([(1183, b32 31), (7200, b32 (cta + 1))] ++
        groupScanFacts .select 31 p.batch cta ++
        (7194, b32 (tilePrefix p 31 * p.heads)) :: fallbackAbi p l g) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o := by
  obtain ⟨j, e, t, o, he, hK, hSite, hKind, ht, hPast, hTail⟩ :=
    firstGroupScanLaunchFrame hp hMax hg hw hProtected
  have hCta : g / l.block < 2 ^ 31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  have hMin : min p.batch 31 = 31 := Nat.min_eq_right hBatch.le
  have hSkip : ¬ g / l.block < tilePrefix p (min p.batch 31) * p.heads := by
    rw [hMin]
    exact Nat.not_lt_of_ge hCut
  obtain ⟨u, hRoute, hU, hKeep⟩ := firstGroupRouteKeeping hp g hCta (by at_select ht)
  have hU' : At u 1985
      ([(1072, b32 (g / l.block)), (7203, b32 p.batch),
        (7200, b32 (tilePrefix p (min p.batch 31) * p.heads))] ++ fallbackAbi p l g) := by
    refine ⟨by simpa only [ite_eq_right hSkip] using hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.1, ?_⟩
    refine ⟨(hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl), hU.2.2.2.2.1,
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hKeep _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl), trivial⟩
  obtain ⟨v, hInit, hV⟩ := initializeFallbackSearch hp hg hU'
  have hV' : At v 1988 (groupScanFacts .select 0 p.batch (g / l.block) ++
      (7194, b32 (tilePrefix p (0 + 31) * p.heads)) :: fallbackAbi p l g) := by
    simpa only [hMin, Nat.zero_add] using hV
  obtain ⟨w, hAdvance, hW⟩ := advanceFallbackSearch hp
    (show 0 + 31 < p.batch from hBatch) hV'
  have hIsShuffle : Execution.isShfl e = true := by
    cases e with
    | mk site kind =>
      change kind = _ at hKind
      subst kind
      rfl
  have hCount := Flow.countP_take_succ he hIsShuffle
  rw [hK.2] at hCount
  have hRelease : e.kind.resume ≠ .blocking false := by rw [hKind]; intro h; cases h
  exact ⟨j + 1, e, t, w, o, by omega, len_of_get he,
    by simpa only [Nat.add_sub_cancel] using he, hSite, ht.1, hCount, releasedIfLast he hRelease,
    hW, hPast, run_rtg (run_comp (run_comp hRoute hInit) hAdvance), hTail⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
