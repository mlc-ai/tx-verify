-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderWarmRoundBiasReady
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasRendezvous
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningBiasReturn
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.UnitReachBlocker

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Thread.Loader
open Prologue (warpIndex)

/-- The softmax Bias release of a stage, in the opening visit and in every repeated visit,
targets the stage's Bias-empty object of the lane's own CTA. -/
theorem biasReleaseLoc (l : Launch) (g : Nat) (stage : Fin 2) (repeated : Bool) :
    Softmax.signalLoc l g stage (Softmax.biasReleaseSite repeated) =
      biasEmptyObject l (g/l.block) stage := by
  cases repeated <;>
    change Loc.mk .shared (g/l.block) (l.sharedBase+8*stage.val+336) =
      Loc.mk .shared (g/l.block) (l.sharedBase+(336+8*stage.val)) <;>
    congr 1 <;> omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

private theorem biasEmptyInitialized (hX : Consistent l kernel Assumptions.all m X) {cta : Nat}
    (stage : Fin 2) {r : Record Ref} (hr : r ∈ X.objects (biasEmptyObject l cta stage)) :
    PairTmaRing.InitFirst X (biasEmptyObject l cta stage) 4 := by
  fin_cases stage
  · exact (activeObjectHistory hp hX (32 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (33 : Fin 34) hr).1

/-- Four distinct threads that have each issued at least `gen` arrivals on a stage's
Bias-empty object complete at least `gen` of its phases. The object expects four unit
arrivals per phase, every update is such a unit arrival and no record faults, so the
history's `4*gen` arrival units leave at most three pending units of the current phase. -/
theorem biasEmptyReleasedOfThreads (hX : Consistent l kernel Assumptions.all m X) {cta gen : Nat}
    (stage : Fin 2) (hGen : 0 < gen) (lanes : Fin 4 → Nat) (hDistinct : Function.Injective lanes)
    (hArrivals : ∀ w, gen ≤ (X.tr (lanes w)).countP (arrivesOn (biasEmptyObject l cta stage))) :
    BiasEmptyReleased l X cta stage gen := by
  classical
  let loc := biasEmptyObject l cta stage
  let log := X.objects loc
  have hChecked := X.objects_checked hX loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hClean (r : Record Ref) (hr : r ∈ log) : r.fault = none :=
    biasEmptyHistoryClean hp hX stage hr
  have hShape {r : Record Ref} (hr : r ∈ log) (hu : CounterUpdate r.action) :
      r.action = .arrive 1 0 :=
    (Thread.Softmax.biasEmptyUpdate hp hX stage hr hu).elim fun _ h => h.2.2.2.2.2
  have hRecorded (w : Fin 4) : gen ≤ log.countP (MbarRing.Unit.unitRec (lanes w)) :=
    (hArrivals w).trans (MbarRing.Unit.arrivals_le_unitRec hX hClean (lanes w))
  have hSum : ∑ w, log.countP (MbarRing.Unit.unitRec (lanes w)) ≤ arrivalUnits log :=
    MbarRing.Unit.sum_count_le_units hDistinct log (fun r hr _ c tx ha =>
      (Action.arrive.inj ((hShape hr (by rw [ha]; trivial)).symm.trans ha).symm).1)
  have hUnits : 4*gen ≤ arrivalUnits log := by
    have hLe : ∑ _w : Fin 4, gen ≤ ∑ w, log.countP (MbarRing.Unit.unitRec (lanes w)) :=
      Finset.sum_le_sum fun w _ => hRecorded w
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hLe
    omega
  have hNonempty : log ≠ [] := by
    intro h
    have h0 : arrivalUnits log = 0 := by rw [h]; rfl
    omega
  obtain ⟨sample, hSample⟩ := List.exists_mem_of_ne_nil log hNonempty
  have hInit := biasEmptyInitialized hp hX stage hSample
  obtain ⟨final, hFinal⟩ := MbarRing.Unit.final_of_init hX hInit hNo hNonempty
  have hNoInc : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr ha
    have h := hShape hr (by rw [ha]; trivial)
    rw [ha] at h
    cases h
  have hNoTx : final.tx = 0 := MbarRing.tx_zero_of hX hNo
    (fun r hr _ _ ha => (Action.arrive.inj ((hShape hr (by rw [ha]; trivial)).symm.trans
      ha)).2.symm)
    (fun r hr _ ha => by
      have h := hShape hr (by rw [ha]; trivial)
      rw [ha] at h
      cases h) le_rfl hFinal
  have hPending := stateBefore_pending_pos hChecked hFinal hNoTx
  have hBalance := ((hChecked.accounted hNo le_rfl).2 final hFinal).2
  have hExpected := PairTmaRing.expected_of_init hX hInit hNo hFinal
  rw [hExpected, hNoInc, Nat.add_zero] at hBalance
  change arrivalUnits (log.take log.length) + final.pending = _ at hBalance
  rw [List.take_length] at hBalance
  refine ⟨final, hFinal, ?_⟩
  by_contra! hLow
  have hMul := Nat.mul_le_mul_left 4 (show final.phase+1 ≤ gen by omega)
  omega

/-- Each of the four softmax warps of a stage has issued at least `gen` arrivals on the
stage's Bias-empty object from one of its lanes, so at least `gen` phases have completed. -/
theorem biasEmptyReleasedOfArrivals (hX : Consistent l kernel Assumptions.all m X) {cta gen : Nat}
    (stage : Fin 2) (hGen : 0 < gen)
    (arrivals : ∀ w : Fin 4, ∃ g, warpIndex l g = 4*stage.val+w.val ∧
      gen ≤ (X.tr g).countP (arrivesOn (biasEmptyObject l cta stage))) :
    BiasEmptyReleased l X cta stage gen := by
  choose lanes hWarp hCount using arrivals
  refine biasEmptyReleasedOfThreads hp hX stage hGen lanes (fun a b h => ?_) hCount
  have ha := hWarp a
  have hb := hWarp b
  rw [h] at ha
  exact Fin.ext (by omega)

/-- In every scheduled CTA of a maximal execution, the opening release of each softmax warp
of a stage completes the first phase of the stage's Bias-empty object. -/
theorem biasEmptyReleasedOpeningOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {cta batch : Nat} (hc : cta < l.grid) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1)*p.heads)
    (stage : Fin 2) :
    BiasEmptyReleased l X cta stage 1 :=
  Progress.openingBiasEmptyAdvancedOfMaximal hp hMax hFrame hc hb hLo hHi stage

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
