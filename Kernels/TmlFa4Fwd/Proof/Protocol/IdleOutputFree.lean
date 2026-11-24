-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.IdleOutputFree
import Kernels.TmlFa4Fwd.Proof.StaticSafety
import Lemmas.Protocol.ObjectSource
import Lemmas.Protocol.PairTmaRing.ItemFacts
import Lemmas.Protocol.MbarPending

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.MBarrier PTX.AsyncCopy Prologue Epilogue Thread.Output

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {cta : Nat}
include hp hMax

/-- With no updates the initialized staging object retains its initial phase. -/
theorem freePhaseZeroOfNoUpdates (hc : cta < l.grid) (stage : Fin 2)
    (hNoUpdate : ∀ r ∈ X.objects (freeObject l cta stage), ¬ CounterUpdate r.action) :
    let log := X.objects (freeObject l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 := by
  dsimp only
  let loc := freeObject l cta stage
  let log := X.objects loc
  obtain ⟨r, hr, hInit⟩ := freeInitializedOfMaximal hp hMax hc stage
  have hUnits {xs : List (Record Ref)} (h : ∀ r ∈ xs, r ∈ log) : arrivalUnits xs = 0 := by
    induction xs with
    | nil => rfl
    | cons r xs ih =>
      have hTail := ih (fun q hq => h q (List.mem_cons_of_mem r hq))
      have hFirst := hNoUpdate r (h r List.mem_cons_self)
      cases hm : r.action <;> simp_all [CounterUpdate, arrivalUnits]
  have hNo := objects_noInval hMax.1.tma.2.2.1 (fun _ _ => noMbarInval hMax.1) loc
  have hChecked := X.objects_checked hMax.1 loc
  obtain ⟨s, hs⟩ := stateBefore_length_some hChecked hNo hr hInit (by decide)
  refine ⟨s, hs, ?_⟩
  have hExpected := PairTmaRing.expected_of_init hMax.1 (freeInitialized hp hMax.1 stage hr)
    hNo hs
  obtain ⟨hPend, hArr⟩ := (hChecked.accounted hNo (Nat.le_refl log.length)).2 s hs
  have hZero : unitsBefore log log.length = 0 := by
    rw [unitsBefore, List.take_length]
    exact hUnits (fun _ h => h)
  rw [hExpected] at hPend hArr
  change unitsBefore log log.length + s.pending = _ at hArr
  rw [hZero] at hArr
  omega

/-- The initialized output-free object stays at phase zero in any idle CTA. -/
theorem idleFreePhaseZeroOfAllGroups (hc : cta < l.grid) (stage : Fin 2)
    (hCuQ : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ cta) :
    let log := X.objects (freeObject l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 := by
  apply freePhaseZeroOfNoUpdates hp hMax hc stage
  intro r hr hUpdate
  obtain ⟨_,_,_,hCredit,_⟩ := freeUpdate hp hMax.1 stage hr hUpdate
  exact (Nat.not_lt_of_ge hIdle) (freeRequiresWork hp hMax.1 hCredit hCuQ)

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Output
