-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCacheWords
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyPacket
import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundEntry
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

/-- A copy at one of the warm K packet's two-plane vector positions. -/
def WarmKeySite (X : Execution) (i : EvId) (sp : AsyncCopy.Spec) : Prop :=
  ∃ (pair : Fin 16) (upper : Bool), X.get i =
    some ⟨packetPlanePc (recurringPacketSite 0) pair upper, .copy sp⟩

/-- The warm K copy was issued by one of the two loader warps. -/
theorem WarmKeySite.issuer {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {sp : AsyncCopy.Spec} (h : WarmKeySite X (g, j) sp) :
    14 ≤ warpIndex l g := by
  obtain ⟨pair, upper, he⟩ := h
  let pc := packetPlanePc (recurringPacketSite 0) pair upper
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
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hX hFrame

/-- An actual warm K vector comes from an active CTA. -/
theorem WarmKeySite.active {g j : Nat} {sp : AsyncCopy.Spec} (h : WarmKeySite X (g, j) sp) :
    g / l.block < tilePrefix p p.batch * p.heads := by
  have hWarp := h.issuer hp hX
  obtain ⟨pair, upper, he⟩ := h
  let pc := packetPlanePc (recurringPacketSite 0) pair upper
  have hPc : 297 < pc ∧ pc < 1862 := by fin_cases pair <;> cases upper <;> decide
  exact loaderOwnPrefixEventRequiresActiveTile hp hX hWarp
    (hp.cuQ_protected (fun _ _ _ _ => loaderOutputWrites hFrame)) he hPc.1 hPc.2

omit hp hX hFrame in
set_option maxRecDepth 100000 in
private theorem warmKeyTailCount (pair : Fin 16) (upper : Bool) :
    loaderShuffleTail 1348 (packetPlanePc (recurringPacketSite 0) pair upper) =
      64 - (2 * pair.val + 2) := by
  fin_cases pair <;> cases upper <;> kernel_rfl

/-- Every issued warm K copy determines its selected request, observed loop
round, and physical vector pair. -/
theorem WarmKeySite.vector {g j : Nat} {sp : AsyncCopy.Spec} (hWarp : 14 ≤ warpIndex l g)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) (h : WarmKeySite X (g, j) sp) :
    ∃ batch < p.batch, ∃ iteration pair upper,
      WarmKeyVector p l X (g, j) batch iteration pair upper sp := by
  obtain ⟨pair, upper, he⟩ := h
  let src := laneOf l g
  have hSelf : warpLane l g src = g := by
    unfold warpLane src laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g % l.block) 32
    omega
  have hg : g < l.threads := event_thread_lt hX he
  have hSrc : src < 32 := Nat.mod_lt _ (by decide)
  let pc := packetPlanePc (recurringPacketSite 0) pair upper
  let e : Event := ⟨pc, .copy sp⟩
  have hObserve : X.get (warpLane l g src, j) = some e := by rw [hSelf]; exact he
  have hPc : 917 ≤ pc ∧ pc < 1348 := by fin_cases pair <;> cases upper <;> decide
  obtain ⟨batch, hb, hLo, hHi, iteration, _, hOrdinal⟩ :=
    actualWarmEventRound hp hX hg hWarp hSrc
      (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA hObserve hPc (by intro f h; cases h)
  change ((X.tr (warpLane l g src)).take j).countP Execution.isShfl + loaderShuffleTail 1348 pc =
    primingSearchShuffleCount batch + 64 + 64 * iteration + 64 at hOrdinal
  rw [hSelf, warmKeyTailCount pair upper] at hOrdinal
  refine ⟨batch, hb, iteration, pair, upper, hLo, hHi, he, ?_⟩
  change ((X.tr g).take j).countP Execution.isShfl =
    primingSearchShuffleCount batch + 64 + 64 * iteration + 2 * pair.val + 2
  have hPair := pair.isLt
  omega

/-- All live bytes read by an actual warm K vector have launch backing. -/
theorem WarmKeySite.backing {g j : Nat} {sp : AsyncCopy.Spec} (h : WarmKeySite X (g, j) sp) :
    CacheWords m sp.src ∧
      (∀ k < sp.src.size,
        (p.kLayout.region p.pages p.kvHeads).Contains (sp.src.loc.at k) ∧
        (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
        ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k)) := by
  have hWarp := h.issuer hp hX
  have hCTA := h.active hp hX hFrame
  obtain ⟨batch, hb, iteration, pair, upper, hVector⟩ := h.vector hp hX hFrame hWarp hCTA
  have hLo := hVector.1
  have hHi := hVector.2.1
  have hSource := hVector.source hp hX hFrame hb hWarp hCTA
  let co := assignedCoordinates p batch (g / l.block)
  have hHead : co.2 < p.heads := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by
    unfold Params.heads at hHead
    omega
  have hShape := actualCopyShape hX (show X.Copy (g, j) sp from hVector.copy)
  let row := kvCopyRow (Mma.trips p batch co.1 - 2 - iteration) (g % l.block) pair.val
  refine ⟨cacheWordsOfLayout hp (lane := g % l.block)
    (primingScratchPageBound hp (row := row) hb)
    hh (Nat.mod_lt row (by decide)) false upper (hShape.srcSize.trans_eq hShape.widthEq) ?_,
    hSource.2⟩
  exact hSource.1

theorem WarmKeySite.backed {g j : Nat} {sp : AsyncCopy.Spec} (h : WarmKeySite X (g, j) sp) :
    ∀ k < sp.src.size,
      (p.kLayout.region p.pages p.kvHeads).Contains (sp.src.loc.at k) ∧
      (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
      ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k) :=
  (h.backing hp hX hFrame).2

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
