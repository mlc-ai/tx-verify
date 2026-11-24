-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.IdleLoaderObjects
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.MbarPending

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Loader
open PTX PTX.MBarrier PTX.AsyncCopy Prologue Epilogue Thread.Loader

noncomputable section

/-- A release object with a positive initial credit stays in phase zero until an update. -/
theorem releasePhaseZeroOfPositiveInit {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {loc : Loc} {credits : Nat}
    (hValid : validCount credits)
    (hFirst : PairTmaRing.InitFirst X loc credits)
    (hInit : ∃ r ∈ X.objects loc, r.action = .init credits)
    (hNoUpdate : ∀ r ∈ X.objects loc, ¬ CounterUpdate r.action) :
    let log := X.objects loc
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 := by
  dsimp only
  let log := X.objects loc
  obtain ⟨r,hr,hInit⟩ := hInit
  have hUnits {xs : List (Record Ref)} (h : ∀ r ∈ xs, r ∈ log) : arrivalUnits xs = 0 := by
    induction xs with
    | nil => rfl
    | cons r xs ih =>
      have hTail := ih (fun q hq => h q (List.mem_cons_of_mem r hq))
      have hHead := hNoUpdate r (h r List.mem_cons_self)
      cases hAction : r.action <;> simp_all [CounterUpdate,arrivalUnits]
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  obtain ⟨s,hs⟩ := stateBefore_length_some hChecked hNo hr hInit hValid
  have hExpected := PairTmaRing.expected_of_init hX hFirst hNo hs
  obtain ⟨hPend,hArr⟩ := (hChecked.accounted hNo (Nat.le_refl log.length)).2 s hs
  have hIncrements : incrementsBefore log log.length = 0 :=
    incrementsBefore_length_of _ (fun r hr hi => hNoUpdate r hr (by rw [hi]; trivial))
  have hZero : unitsBefore log log.length = 0 := by
    rw [unitsBefore,List.take_length]
    exact hUnits (fun _ h => h)
  rw [hExpected,hIncrements] at hPend
  rw [hExpected,hIncrements,hZero] at hArr
  have hPositive : 0 < credits := hValid.1
  refine ⟨s,hs,?_⟩
  by_contra! hPhase
  have hProduct := Nat.mul_pos hPositive (Nat.pos_of_ne_zero hPhase)
  rw [Nat.mul_add, Nat.mul_one] at hArr
  omega

/-- A release object with one initial credit remains in phase zero until an update arrives. -/
theorem releasePhaseZeroOfInitialized {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {loc : Loc}
    (hFirst : PairTmaRing.InitFirst X loc 1)
    (hInit : ∃ r ∈ X.objects loc, r.action = .init 1)
    (hNoUpdate : ∀ r ∈ X.objects loc, ¬ CounterUpdate r.action) :
    let log := X.objects loc
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 :=
  releasePhaseZeroOfPositiveInit hX (by decide) hFirst hInit hNoUpdate

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {cta : Nat} (hc : cta < l.grid)
include hp hMax hc

/-- A release object with no counter update remains in its initialized phase. -/
theorem releasePhaseZeroOfNoUpdates (obj : IdleReleaseObject)
    (hNoUpdate : ∀ r ∈ X.objects (obj.loc l cta), ¬ CounterUpdate r.action) :
    let log := X.objects (obj.loc l cta)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 := by
  obtain ⟨hFirst,hInit⟩ := idleReleaseInitialized hp hMax hc obj
  exact releasePhaseZeroOfInitialized hMax.1 hFirst hInit hNoUpdate

/-- For an idle CTA of any request count, all four loader drain objects stay in phase zero. -/
theorem idleReleasePhaseZeroForBatches (obj : IdleReleaseObject) (hCuQ : DrainCuQProtected p X)
    (hIdle : tilePrefix p p.batch * p.heads ≤ cta) :
    let log := X.objects (obj.loc l cta)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 :=
  releasePhaseZeroOfNoUpdates hp hMax hc obj
    (fun _ hr => idleReleaseNoUpdatesForBatches hp hMax obj hCuQ hIdle hr)

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Loader
