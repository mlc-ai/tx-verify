-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundValueBacking
public import Kernels.TmlFa4Fwd.Proof.LoaderCacheWords
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundValueReload
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundKeyReload
public import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerReload
public import Kernels.TmlFa4Fwd.Proof.LoaderSourceLayout
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmShuffleFloor
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKFirstPrefix
public import Kernels.TmlFa4Fwd.Proof.TerminalSite
public import Kernels.TmlFa4Fwd.Flow.Code.Part019
public import Kernels.TmlFa4Fwd.Proof.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.LoaderWarmValuePacket
import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundEntry
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

/-- A copy at one of the warm V packet's two-plane vector positions. -/
def WarmValueSite (X : Execution) (i : EvId) (sp : AsyncCopy.Spec) : Prop :=
  ∃ (pair : Fin 16) (upper : Bool), X.get i =
    some ⟨packetPlanePc (recurringPacketSite 1) pair upper, .copy sp⟩

/-- The warm V copy was issued by one of the two loader warps. -/
theorem WarmValueSite.issuer {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {sp : AsyncCopy.Spec} (h : WarmValueSite X (g, j) sp) :
    14 ≤ warpIndex l g := by
  obtain ⟨pair, upper, he⟩ := h
  let pc := packetPlanePc (recurringPacketSite 1) pair upper
  have hRange : 173 < pc ∧ pc < 1901 ∧ pc ∉ registerHintSites := by
    fin_cases pair <;> cases upper <;> decide
  have hBody := roleBodyPcOfEvent hp hX he hRange.1 hRange.2.2
  change roleBodyPc (warpIndex l g) pc at hBody
  unfold roleBodyPc at hBody
  have body := hBody.resolve_left (by omega : pc ≠ 9205)
  by_contra! hWrong
  rw [ite_eq_right (by omega : ¬ 14 ≤ warpIndex l g)] at body
  split at body
  · omega
  split at body
  · omega
  split at body <;> omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g j : Nat}
include hp hX hFrame

/-- An actual warm V vector comes from an active CTA. -/
theorem WarmValueSite.active {sp : AsyncCopy.Spec} (h : WarmValueSite X (g, j) sp) :
    g / l.block < tilePrefix p p.batch * p.heads := by
  have hWarp := h.issuer hp hX
  obtain ⟨pair, upper, he⟩ := h
  let pc := packetPlanePc (recurringPacketSite 1) pair upper
  have hPc : 297 < pc ∧ pc < 1862 := by fin_cases pair <;> cases upper <;> decide
  exact loaderOwnPrefixEventRequiresActiveTile hp hX hWarp
    (hp.cuQ_protected (fun _ _ _ _ => loaderOutputWrites hFrame)) he hPc.1 hPc.2

omit hp hX hFrame in
set_option maxRecDepth 100000 in
private theorem warmValueTailCount (pair : Fin 16) (upper : Bool) :
    loaderShuffleTail 1348 (packetPlanePc (recurringPacketSite 1) pair upper) =
      32 - (2 * pair.val + 2) := by
  fin_cases pair <;> cases upper <;> kernel_rfl

/-- Every issued warm V copy determines its selected request, observed loop
round, and physical vector pair. -/
theorem WarmValueSite.vector {sp : AsyncCopy.Spec} (hWarp : 14 ≤ warpIndex l g)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) (h : WarmValueSite X (g, j) sp) :
    ∃ batch < p.batch, ∃ iteration pair upper,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      X.get (g, j) = some ⟨packetPlanePc (recurringPacketSite 1) pair upper, .copy sp⟩ ∧
      ((X.tr g).take j).countP Execution.isShfl =
        primingSearchShuffleCount batch + 64 + 64 * iteration + 32 + 2 * pair.val + 2 := by
  obtain ⟨pair, upper, he⟩ := h
  let src := laneOf l g
  have hSelf : warpLane l g src = g := by
    unfold warpLane src laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g % l.block) 32
    omega
  have hg : g < l.threads := event_thread_lt hX he
  have hSrc : src < 32 := Nat.mod_lt _ (by decide)
  let pc := packetPlanePc (recurringPacketSite 1) pair upper
  let e : Event := ⟨pc, .copy sp⟩
  have hObserve : X.get (warpLane l g src, j) = some e := by rw [hSelf]; exact he
  have hPc : 917 ≤ pc ∧ pc < 1348 := by fin_cases pair <;> cases upper <;> decide
  obtain ⟨batch, hb, hLo, hHi, iteration, _, hOrdinal⟩ :=
    actualWarmEventRound hp hX hg hWarp hSrc
      (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA hObserve hPc (by intro f h; cases h)
  change ((X.tr (warpLane l g src)).take j).countP Execution.isShfl + loaderShuffleTail 1348 pc =
    primingSearchShuffleCount batch + 64 + 64 * iteration + 64 at hOrdinal
  rw [hSelf, warmValueTailCount pair upper] at hOrdinal
  refine ⟨batch, hb, iteration, pair, upper, hLo, hHi, he, ?_⟩
  have hPair := pair.isLt
  omega

omit hp hX hFrame in
/-- An observed first logical vector pair in a warm V packet. -/
def WarmValueFirstPair (X : Execution) (i : EvId) (sp : AsyncCopy.Spec) : Prop :=
  ∃ upper : Bool, X.get i = some ⟨packetPlanePc (recurringPacketSite 1) 0 upper, .copy sp⟩

/-- All live bytes read by an actual first-pair warm V vector have launch backing. -/
theorem WarmValueFirstPair.backed {sp : AsyncCopy.Spec} (h : WarmValueFirstPair X (g, j) sp) :
    ∀ k < sp.src.size,
      (p.vLayout.region p.pages p.kvHeads).Contains (sp.src.loc.at k) ∧
      (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
      ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k) := by
  obtain ⟨upper, he⟩ := h
  have hSite : WarmValueSite X (g, j) sp := ⟨0, upper, he⟩
  have hWarp := hSite.issuer hp hX
  have hCTA := hSite.active hp hX hFrame
  let src := laneOf l g
  have hSelf : warpLane l g src = g := by
    unfold warpLane src laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g % l.block) 32
    omega
  have hg : g < l.threads := event_thread_lt hX he
  have hSrc : src < 32 := Nat.mod_lt _ (by decide)
  let pc := packetPlanePc (recurringPacketSite 1) 0 upper
  let e : Event := ⟨pc, .copy sp⟩
  have hObserve : X.get (warpLane l g src, j) = some e := by rw [hSelf]; exact he
  have hPc : 917 ≤ pc ∧ pc < 1348 := by cases upper <;> decide
  obtain ⟨batch, hb, hLo, hHi, iteration, _, hOrdinal⟩ :=
    actualWarmEventRound hp hX hg hWarp hSrc
      (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA hObserve hPc (by intro f h; cases h)
  have hCount : loaderShuffleTail 1348 pc = 30 := by cases upper <;> kernel_rfl
  change ((X.tr (warpLane l g src)).take j).countP Execution.isShfl + loaderShuffleTail 1348 pc =
    primingSearchShuffleCount batch + 64 + 64 * iteration + 64 at hOrdinal
  rw [hCount] at hOrdinal
  exact (warmRoundFirstValueCopyBacked hp hX hFrame hg hWarp hSrc hb hLo hHi hCTA
    (iteration := iteration) upper hObserve (by omega)).2

/-- All live bytes read by an actual warm V vector have launch backing. -/
theorem WarmValueSite.backing {sp : AsyncCopy.Spec} (h : WarmValueSite X (g, j) sp) :
    CacheWords m sp.src ∧
      (∀ k < sp.src.size,
        (p.vLayout.region p.pages p.kvHeads).Contains (sp.src.loc.at k) ∧
        (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
        ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k)) := by
  have hWarp := h.issuer hp hX
  have hCTA := h.active hp hX hFrame
  obtain ⟨batch, hb, iteration, pair, upper, hLo, hHi, he, hOrdinal⟩ :=
    h.vector hp hX hFrame hWarp hCTA
  let src := laneOf l g
  have hSelf : warpLane l g src = g := by
    unfold warpLane src laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g % l.block) 32
    omega
  have hg : g < l.threads := event_thread_lt hX he
  have hSrc : src < 32 := Nat.mod_lt _ (by decide)
  have hSource := warmValuePacketSource hp hX hFrame hg hWarp hSrc hb hLo hHi hCTA
    (iteration := iteration) pair upper (by rwa [hSelf]) (by rwa [hSelf])
  let co := assignedCoordinates p batch (g / l.block)
  have hHead : co.2 < p.heads := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by
    unfold Params.heads at hHead
    omega
  have hShape := actualCopyShape hX (show X.Copy (g, j) sp from ⟨_, he⟩)
  let sender := warpLane l g (warmVShuffleSender src pair)
  let row := warmVInputRow (Mma.trips p batch co.1 - 2 - iteration) (sender % l.block) pair
  refine ⟨cacheWordsOfLayout hp (lane := warpLane l g src % l.block)
    (primingScratchPageBound hp (row := row) hb)
    hh (Nat.mod_lt row (by decide)) true upper (hShape.srcSize.trans_eq hShape.widthEq) ?_,
    hSource.2⟩
  exact hSource.1

theorem WarmValueSite.backed {sp : AsyncCopy.Spec} (h : WarmValueSite X (g, j) sp) :
    ∀ k < sp.src.size,
      (p.vLayout.region p.pages p.kvHeads).Contains (sp.src.loc.at k) ∧
      (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
      ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k) :=
  (h.backing hp hX hFrame).2

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
