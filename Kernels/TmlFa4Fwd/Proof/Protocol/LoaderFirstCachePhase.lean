-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.IdleLoaderRelease
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstCacheOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseCapacity
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Loader
open PTX PTX.MBarrier PTX.AsyncCopy Prologue Thread.Loader
open Thread.Mma (emptyUpdateArrival emptyReleaseAt)

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

private theorem noEmptyUpdateBeforeSlotPublication (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hw : 14 ≤ warpIndex l g) (slot : Fin 3)
    (hQuiet : ∀ i, ¬ X.AsyncArrive (g,i) (readyObject l g slot) true) {r : Record Ref}
    (hr : r ∈ X.objects (Thread.Mma.Observation.emptyObject l g slot)) :
    ¬ CounterUpdate r.action := by
  intro hUpdate
  obtain ⟨_,_,_,_,hOne⟩ := emptyUpdateArrival hp hX hr hUpdate
  obtain ⟨k,hk⟩ := List.getElem?_of_mem hr
  obtain ⟨issuer,⟨release⟩⟩ := emptyReleaseAt hp hX hk hOne
  have hReady := release.matched.ready
  rw [release.matchedSlot] at hReady
  obtain ⟨complete⟩ := LoaderReady.actualCompletedForIssuer hp hX release.issue hReady
  obtain ⟨lane,hLane⟩ := producerOfLoaderWarp hp hw
  obtain ⟨issue,hIssue,hArrive,_,_,_⟩ := complete.actualPublicationOfLane hp hX lane
  rw [← release.issuerCta hp hX, ← hLane] at hIssue
  have hObject : readyObject l issuer slot = readyObject l g slot := by
    simp only [readyObject,← release.issuerCta hp hX]
  rw [hObject] at hArrive
  exact hQuiet issue.2 (show X.AsyncArrive (g,issue.2) _ true by
    obtain ⟨actor,j⟩ := issue
    change actor = g at hIssue
    subst actor
    exact hArrive)

/-- Without a lane publication to this slot, its empty object remains at phase zero. -/
theorem cacheEmptyPhaseBeforeSlotPublication (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (slot : Fin 3)
    (hQuiet : ∀ i, ¬ X.AsyncArrive (g,i) (readyObject l g slot) true) :
    let log := X.objects (Thread.Mma.Observation.emptyObject l g slot)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 :=
  releasePhaseZeroOfNoUpdates hp hMax (NamedBar.cta_lt hg) (.cache slot)
    (fun _ hr => noEmptyUpdateBeforeSlotPublication hp hMax.1 hw slot hQuiet hr)

/-- A loader lane with no cache publication still has its CTA's cache empty phase zero. -/
theorem cacheEmptyPhaseBeforePublication (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hQuiet : ∀ (i : Nat) (loc : Loc), ¬ X.AsyncArrive (g,i) loc true) (slot : Fin 3) :
    let log := X.objects (Thread.Mma.Observation.emptyObject l g slot)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 :=
  releasePhaseZeroOfNoUpdates hp hMax (NamedBar.cta_lt hg) (.cache slot)
    (fun _ hr => noEmptyUpdateBeforeSlotPublication hp hMax.1 hw slot (fun i => hQuiet i _) hr)

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Loader
