-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseCapacity
import Kernels.TmlFa4Fwd.Proof.MmaQkIssue
import Kernels.TmlFa4Fwd.Proof.MmaPvIssue
import Lemmas.Flow.NotTcMma
import Lemmas.Flow.OpPcsFast
import Kernels.TmlFa4Fwd.Flow.Sites.Part000

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof Prologue
open PTX.Kernels.TmlFa4Fwd.Mma
open Observation (readyObject emptyObject)

noncomputable section

private def gatedBy (site : Fin 4) (p : Nat) : Prop :=
  (slotWait site).pc + 3 ≤ p ∧ p ≤ (slotElect site).pc

private instance (site : Fin 4) (p : Nat) : Decidable (gatedBy site p) := by
  unfold gatedBy
  infer_instance

private def gateForm : Fin 4 → ReleaseForm
  | 0 => .firstKey
  | 1 => .loopValue
  | 2 => .loopKey
  | _ => .tailValue

private theorem gateFormIndex (site : Fin 4) : releaseIndex (gateForm site) = site := by
  decide +revert

private def qkBlock (block : Fin 4) : List Nat :=
  List.ofFn (fun (step : Fin 8) => qkPc block + step.val)

private def pvBlock (block : Fin 4) : List Nat := List.ofFn (pvPc block)

private def gateFragments : Fin 4 → List Nat
  | 0 => qkBlock 0 ++ qkBlock 1
  | 1 => pvBlock 0 ++ pvBlock 1
  | 2 => qkBlock 2 ++ qkBlock 3
  | _ => pvBlock 2 ++ pvBlock 3

private theorem gateReadyMarked (site : Fin 4) :
    (List.finRange 4).any (fun i => readyHead i == (slotWait site).pc) = true := by
  decide +revert

private theorem coveringGate (p : Nat) (hp : p ∈ Flow.mma.toList) :
    ∃ site : Fin 4, p ∈ gateFragments site ∧ gatedBy site p := by
  have hCovered : Flow.mma.toList.all (fun k =>
      (List.finRange 4).any (fun site =>
        decide (k ∈ gateFragments site ∧ gatedBy site k))) = true := by decide +kernel
  obtain ⟨site, _, hGate⟩ := List.any_eq_true.mp (List.all_eq_true.mp hCovered p hp)
  exact ⟨site, of_decide_eq_true hGate⟩

/-- Every actual MMA fragment follows the latest successful K/V-ready acquisition
of its release form on the issuing lane, even if that release is still unissued. -/
theorem actualMmaOperandReadyAndOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hMma : X.MmaIssue (g, index) d op accum mask) :
    ∃ (form : ReleaseForm) (wait : Nat) (slot : Fin 3) (parity : Nat),
      ReleaseReadyObservation X g wait form (readyObject l g slot) parity ∧
      ReadyPoll l X g wait slot parity true .cta ∧ Resumes kernel X (g, wait) (g, index) ∧
      readyOccurrence X g wait form = releaseElections X g index form ∧
      readyOccurrence X g index form = releaseElections X g index form + 1 := by
  obtain ⟨p, he⟩ := hMma
  obtain ⟨_, hFault⟩ | ⟨_, _, _, _, hCode, hFire⟩ := get_source hX he
  · cases hFault
  have hSites : OpPcsFast kernel.code tcMmaOp Flow.mma.toList = true := by
    decide +kernel
  have hpSite := OpPcsFast.mem hSites hCode (fires_tcMma_op hFire rfl)
  have hBounds : Flow.mma.toList.all (fun k =>
      decide (1908 ≤ k ∧ k < 2768 ∧ k ∉ registerHintSites)) = true := by decide
  obtain ⟨hLo, hHi, hHint⟩ := of_decide_eq_true (List.all_eq_true.mp hBounds p hpSite)
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < p by omega) hHint
  have hw : warpIndex l g = 12 := by
    rcases hRole with h | h
    · dsimp only at h
      omega
    · split_ifs at h <;> dsimp only at h <;> omega
  obtain ⟨site, _, hGate⟩ := coveringGate p hpSite
  obtain ⟨wait, hEarlier, loc, parity, acquire, scope, hWait, hOrdinal⟩ :=
    pendingReadyOrdinal hp hX site he hGate
  obtain ⟨rfl, rfl⟩ := readyGateAcquireFlags hX site hWait
  obtain ⟨exit, hSpin⟩ := actualCanonicalPoll hX hWait
  have hTrace : TraceBefore X (g, wait) (g, index) :=
    ⟨rfl, hEarlier, PTX.len_of_get he⟩
  have hResume : Resumes kernel X (g, wait) (g, index) := by
    refine ⟨hTrace, ?_⟩
    simp only [hWait, Option.map_some, Kind.resume]
    exact ⟨_, exit, loc, parity, true, .cta, hWait, hSpin, hTrace⟩
  have hMark : readyEvent
      ⟨(slotWait site).pc, .wait loc parity true true .cta⟩ = some (loc, parity) := by
    simp [readyEvent, gateReadyMarked site]
  obtain ⟨slot, rfl⟩ := readySlotOfProjection hp hX hw hWait hMark
  refine ⟨gateForm site, wait, slot, parity, ?_, ⟨_, hWait, rfl⟩, hResume, ?_, ?_⟩
  · simpa only [ReleaseReadyObservation, gateFormIndex] using hWait
  · simpa only [readyOccurrence, releaseElections, gateFormIndex] using hOrdinal
  · simpa only [readyOccurrence, releaseElections, gateFormIndex, Nat.add_comm] using
      pendingReadyBalance hp hX site he hGate

/-- Every actual MMA fragment follows the latest successful K/V-ready acquisition
of its release form on the issuing lane, even if that release is still unissued. -/
theorem actualMmaOperandReady {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hMma : X.MmaIssue (g, index) d op accum mask) :
    ∃ (form : ReleaseForm) (wait : Nat) (slot : Fin 3) (parity : Nat),
      ReleaseReadyObservation X g wait form (readyObject l g slot) parity ∧
      ReadyPoll l X g wait slot parity true .cta ∧ Resumes kernel X (g, wait) (g, index) ∧
      ∀ j, wait < j → j < index → ∀ loc q, ¬ ReleaseReadyObservation X g j form loc q := by
  obtain ⟨form, wait, slot, parity, hObs, hPoll, hOrder, hOrdinal, hBalance⟩ :=
    actualMmaOperandReadyAndOrdinal hp hX hMma
  refine ⟨form, wait, slot, parity, hObs, hPoll, hOrder, ?_⟩
  intro j hAfter hBefore loc q hLater
  let site := releaseIndex form
  let count := readyAtSite site
  have hBeforeCount (n : Nat) {e : Event} (he : X.get (g, n) = some e)
      (hm : count e = true) :
      ((X.tr g).take (n + 1)).countP count = ((X.tr g).take n).countP count + 1 := by
    change (X.tr g)[n]? = _ at he
    rw [List.take_add_one, he]
    simp [hm, List.countP_append]
  have hAdvance := hBeforeCount wait hObs (by simp [count, readyAtSite, site])
  have hExtra := hBeforeCount j hLater (by simp [count, readyAtSite, site])
  have hMono := (List.take_sublist_take_left (l := X.tr g)
    (show wait + 1 ≤ j by omega)).countP_le (p := count)
  have hLimit := (List.take_sublist_take_left (l := X.tr g)
    (show j + 1 ≤ index by omega)).countP_le (p := count)
  change ((X.tr g).take index).countP count = _ at hBalance
  change ((X.tr g).take wait).countP count = _ at hOrdinal
  omega

/-- A delivered release of the fragment's actual slot and generation follows the
fragment. Its ready acquisition is the one given by the actual fragment trace. -/
theorem EmptyReleaseAt.afterFragmentOfReady {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner g index k d wait parity : Nat} {slot : Fin 3} {form : ReleaseForm}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (release : EmptyReleaseAt l X (emptyObject l owner slot) g k)
    (hMma : X.MmaIssue (g, index) d op accum mask)
    (hReady : ReleaseReadyObservation X g wait form (readyObject l g slot) parity)
    (hOrdinal : readyOccurrence X g wait form = releaseElections X g index form)
    (hGeneration : (atPrefix l X g wait).kvAcquires slot = release.ordinal) :
    wait = release.matched.wait ∧ TraceBefore X (g, index) (g, release.index) := by
  have hMatched := release.matched.readyForm
  rw [release.matchedSlot] at hMatched
  have hRank := hGeneration
  simp only [EmptyReleaseAt.ordinal, release.matchedSlot, atPrefix, kvAcquireCount] at hRank
  have hWait := MbarRing.Poll.okPoll_index_unique
    (show X.get (g, wait) = some ⟨_, .wait (readyObject l g slot) parity true true .cta⟩
      from hReady)
    (show X.get (g, release.matched.wait) =
      some ⟨_, .wait (readyObject l g slot) release.matched.parity true true .cta⟩ from hMatched)
    hRank
  rw [hWait] at hReady hOrdinal
  have hForm := hReady.form_eq hMatched
  subst form
  exact ⟨hWait, release.issue.afterCacheFragment hp hX hMma
    (hOrdinal.symm.trans release.matched.ordinal)⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
