-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCacheWords
public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyPacketSource
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

/-- An observed K vector in a steady copy packet. -/
def SteadyKeySite (X : Execution) (i : EvId) (sp : AsyncCopy.Spec) : Prop :=
  ∃ (pair : Fin 16) (upper : Bool), X.get i =
    some ⟨packetPlanePc (recurringPacketSite (steadySpillSite false)) pair upper, .copy sp⟩

/-- An observed V vector in a steady copy packet. -/
def SteadyValueSite (X : Execution) (i : EvId) (sp : AsyncCopy.Spec) : Prop :=
  ∃ (pair : Fin 16) (upper : Bool), X.get i =
    some ⟨packetPlanePc (recurringPacketSite (steadySpillSite true)) pair upper, .copy sp⟩

/-- An observed first V vector pair in a steady copy packet. -/
def SteadyValueFirstPair (X : Execution) (i : EvId) (sp : AsyncCopy.Spec) : Prop :=
  ∃ upper : Bool, X.get i =
    some ⟨packetPlanePc (recurringPacketSite (steadySpillSite true)) 0 upper, .copy sp⟩

set_option maxRecDepth 100000 in
private theorem steadyPlaneTail (value : Bool) (pair : Fin 16) (upper : Bool) :
    loaderShuffleTail 1741
      (packetPlanePc (recurringPacketSite (steadySpillSite value)) pair upper) =
      64 - (steadyOperandRank value + 2 * pair.val + 2) := by
  cases value <;> fin_cases pair <;> cases upper <;> kernel_rfl

private theorem steadyPlaneIssuer {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (value : Bool) (pair : Fin 16) (upper : Bool) {sp : AsyncCopy.Spec}
    (he : X.get (g, j) =
      some ⟨packetPlanePc (recurringPacketSite (steadySpillSite value)) pair upper, .copy sp⟩) :
    14 ≤ warpIndex l g := by
  let pc := packetPlanePc (recurringPacketSite (steadySpillSite value)) pair upper
  have hRange : 173 < pc ∧ pc < 1901 ∧ pc ∉ registerHintSites := by
    cases value <;> fin_cases pair <;> cases upper <;> decide
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

set_option maxRecDepth 100000 in
private theorem steadyPlaneBacked (value : Bool) (pair : Fin 16) (upper : Bool)
    {sp : AsyncCopy.Spec}
    (he : X.get (g, j) =
      some ⟨packetPlanePc (recurringPacketSite (steadySpillSite value)) pair upper, .copy sp⟩) :
    CacheWords m sp.src ∧
      (∀ k < sp.src.size,
        ((recurringCache p (steadySpillSite value)).region p.pages p.kvHeads).Contains
          (sp.src.loc.at k) ∧
        (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
        ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k)) := by
  have hWarp := steadyPlaneIssuer hp hX value pair upper he
  let pc := packetPlanePc (recurringPacketSite (steadySpillSite value)) pair upper
  have hPc : 1396 ≤ pc ∧ pc < 1741 := by
    cases value <;> fin_cases pair <;> cases upper <;> decide
  have hCTA := loaderOwnPrefixEventRequiresActiveTile hp hX hWarp
    (hp.cuQ_protected (fun _ _ _ _ => loaderOutputWrites hFrame)) he
    (show 297 < pc by omega) (show pc < 1862 by omega)
  let src := laneOf l g
  have hSelf : warpLane l g src = g := by
    unfold warpLane src laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g % l.block) 32
    omega
  have hg : g < l.threads := event_thread_lt hX he
  have hSrc : src < 32 := Nat.mod_lt _ (by decide)
  let e : Event := ⟨pc, .copy sp⟩
  have hObserve : X.get (warpLane l g src, j) = some e := by rw [hSelf]; exact he
  obtain ⟨batch, hb, hLo, hHi, hMany, iteration, hMin, _, hOrdinal⟩ :=
    actualSteadyEventRound hp hX hg hWarp hSrc
      (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA hObserve hPc (by intro f h; cases h)
  change ((X.tr (warpLane l g src)).take j).countP Execution.isShfl +
    loaderShuffleTail 1741 pc =
      primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) + 64 at hOrdinal
  rw [steadyPlaneTail value pair upper] at hOrdinal
  have hBound : steadyOperandRank value ≤ 32 := by cases value <;> decide
  have hPair := pair.isLt
  have hSource := steadyPacketSource hp hX hFrame hg hWarp hSrc hb hLo hHi hCTA hMany hMin
    value pair upper hObserve (by omega)
  let co := assignedCoordinates p batch (g / l.block)
  have hHead : co.2 < p.heads := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by
    unfold Params.heads at hHead
    omega
  have hShape := actualCopyShape hX (show X.Copy (g, j) sp from ⟨_, he⟩)
  let sender := warpLane l g (steadyPairSender src pair)
  let row := steadyPairRow (Mma.trips p batch co.1 - 2 - iteration) (sender % l.block) pair
  refine ⟨cacheWordsOfLayout hp (lane := warpLane l g src % l.block)
    (primingScratchPageBound hp (row := row) hb)
    hh (Nat.mod_lt row (by decide)) value upper (hShape.srcSize.trans_eq hShape.widthEq) ?_,
    hSource.2⟩
  cases value <;> exact hSource.1

/-- Every live byte of an issued steady K vector has launch backing. -/
theorem SteadyKeySite.backed {sp : AsyncCopy.Spec} (h : SteadyKeySite X (g, j) sp) :
    ∀ k < sp.src.size,
      (p.kLayout.region p.pages p.kvHeads).Contains (sp.src.loc.at k) ∧
      (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
      ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k) := by
  obtain ⟨pair, upper, he⟩ := h
  exact (steadyPlaneBacked hp hX hFrame false pair upper he).2

/-- Every live byte of an issued steady V vector has launch backing. -/
theorem SteadyValueSite.backed {sp : AsyncCopy.Spec} (h : SteadyValueSite X (g, j) sp) :
    ∀ k < sp.src.size,
      (p.vLayout.region p.pages p.kvHeads).Contains (sp.src.loc.at k) ∧
      (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
      ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k) := by
  obtain ⟨pair, upper, he⟩ := h
  exact (steadyPlaneBacked hp hX hFrame true pair upper he).2

theorem SteadyKeySite.words {sp : AsyncCopy.Spec} (h : SteadyKeySite X (g, j) sp) :
    CacheWords m sp.src := by
  obtain ⟨pair, upper, he⟩ := h
  exact (steadyPlaneBacked hp hX hFrame false pair upper he).1

theorem SteadyValueSite.words {sp : AsyncCopy.Spec} (h : SteadyValueSite X (g, j) sp) :
    CacheWords m sp.src := by
  obtain ⟨pair, upper, he⟩ := h
  exact (steadyPlaneBacked hp hX hFrame true pair upper he).1

/-- Every live byte in the first pair of an issued steady V packet has launch backing. -/
theorem SteadyValueFirstPair.backed {sp : AsyncCopy.Spec} (h : SteadyValueFirstPair X (g, j) sp) :
    ∀ k < sp.src.size,
      (p.vLayout.region p.pages p.kvHeads).Contains (sp.src.loc.at k) ∧
      (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
      ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k) := by
  obtain ⟨upper, he⟩ := h
  exact SteadyValueSite.backed hp hX hFrame ⟨0, upper, he⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
