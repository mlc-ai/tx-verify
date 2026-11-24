-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPrimingProgress
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPrimingValueProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.PrimingLoaderPublication

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy Thread.Loader

/-- A pending priming publication can advance by finishing a tracked vector or by arriving. -/
theorem pendingPrimingPublication {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {i : EvId} {slot : Fin 2}
    (hPub : PrimingPublication l X i slot) (hPending : X.async.arrived i = false) :
    ∃ Y, Consistent l kernel Assumptions.all m Y ∧ X.le Y ∧ X.size l < Y.size l := by
  classical
  by_cases hw : ∀ copy, TracksCpAsync X copy i → (X.async.copies copy).writeBytes.isSome
  · exact pendingPublication hX hPub.arrive hPending hw
  · push Not at hw
    obtain ⟨⟨g, j⟩, hTrack, hm⟩ := hw
    have hWarp := hPub.loaderWarp hp hX
    have hOwner : g = i.1 := hTrack.1
    rw [← hOwner] at hWarp
    have hNone : (X.async.copies (g, j)).writeBytes = none := by
      cases hg : (X.async.copies (g, j)).writeBytes <;> simp_all
    obtain ⟨pair, upper, spec, hKey | hValue⟩ := hPub.trackedVector hp hX hTrack
    · exact pendingPrimingKeyVector hp hX hFrame hKey hWarp
        (hKey.active hp hX hFrame hWarp) hNone
    · exact pendingPrimingValueVector hp hX hFrame hValue hWarp
        (hValue.active hp hX hFrame hWarp) hNone

/-- Every issued priming publication has arrived in a maximal execution. -/
theorem drainedPrimingPublication {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {i : EvId} {slot : Fin 2}
    (hPub : PrimingPublication l X i slot) : X.async.arrived i = true := by
  cases h : X.async.arrived i
  · exact (hX.not_grows (pendingPrimingPublication hp hX.1 hFrame hPub h)).elim
  · rfl

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
