-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditBalance
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow

/-- A returned statistics wait on the named rendezvous indexes the associated credit. -/
theorem namedWaitForCredit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {credit : EvId} {stage : Fin 2} {e : Event}
    (he : X.get credit = some e) (hc : correctionAction e = some (.statsCredit stage)) :
    let id := Correction.statsBarrierId l credit.1 stage
    ∃ j, BarrierArrival X (credit.1,j) id (some 64) .sync ∧
      observedBarrierOrdinal X (credit.1,j) id =
        (correctionBefore X credit).count (.statsCredit stage) ∧
      j+1 < (X.tr credit.1).length ∧ Resumes kernel X (credit.1,j) credit := by
  obtain ⟨_, _, hKind⟩ := correctionStatsCreditKind hc
  have hSite := (correctionStatsCreditObservation stage hKind).mp hc
  have hm := (Correction.correctionStatsCreditMark_iff stage e).mpr hSite
  obtain ⟨j, hj, ⟨f, hf, hMode⟩, hCount⟩ :=
    Correction.correctionCreditAfterNamedWait hp hX stage he hm
  rw [correctionBarrierOrdinal, ← Correction.correctionCreditCursor hp hX stage he] at hCount
  have hLen : credit.2 < (X.tr credit.1).length := (List.getElem?_eq_some_iff.mp he).1
  have hLater : TraceBefore X (credit.1,j) credit := ⟨rfl, hj, hLen⟩
  have hReturn := Resumes.of_blocking (K := kernel) hf
    (show f.kind.resume = .blocking false by rw [hMode]; rfl) hLater
  exact ⟨j, ⟨f,hf,hMode⟩, hCount, by omega, hReturn⟩

end PTX.Kernels.TmlFa4Fwd.Thread
