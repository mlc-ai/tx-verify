-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderDrainReady
import all Kernels.TmlFa4Fwd.Proof.Protocol.LoaderDrainReady

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Loader
open PTX PTX.MBarrier Prologue Thread.Loader
open Thread.Mma (emptyUpdateArrival)
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvEmptyPhase)

/-- Each cache barrier records the completed credits for the cursor's earlier ring uses. -/
def CacheReleaseCounts (l : Launch) (X : Execution) (g use : Nat) : Prop :=
  ∀ slot : Fin 3,
    let log := X.objects (Thread.Mma.Observation.emptyObject l g slot)
    unitsBefore log log.length = (use+(2-slot.val))/3

private theorem drainVisitCount (use : Nat) (i : Fin 3) :
    (use+(2-(kvUseStage (use+i.val)).val))/3 = (use+i.val)/3 := by
  have hIndex : (kvUseStage (use+i.val)).val = (use+i.val)%3 := rfl
  have hi := i.isLt
  rw [hIndex]
  omega

/-- The final count of completed MMA credits identifies each drained cache generation. -/
theorem cacheDrainReadyOfCreditCount {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use : Nat} (hg : g < l.threads)
    (hUnits : CacheReleaseCounts l X g use) :
    CacheDrainReady l X g use := by
  intro i
  let slot := kvUseStage (use+i.val)
  let loc := Thread.Mma.Observation.emptyObject l g slot
  obtain ⟨s,hs,hPhase⟩ := finalPhaseOfUnitUpdates hp hMax (NamedBar.cta_lt hg) (.cache slot)
    loc (IdleReleaseObject.cacheLoc l g slot) (by
      intro r hr h
      obtain ⟨_,_,_,_,ha⟩ := emptyUpdateArrival hp hMax.1 hr h
      exact ha)
  rw [hUnits slot,drainVisitCount use i] at hPhase
  refine ⟨s,hs,?_⟩
  rw [hPhase]
  change (use+i.val)/3%2 ≠ (if (use+i.val)/3%2 == 0 then 1 else 0)
  by_cases h : (use+i.val)/3%2 = 0 <;> simp [h]

end PTX.Kernels.TmlFa4Fwd.Protocol.Loader
