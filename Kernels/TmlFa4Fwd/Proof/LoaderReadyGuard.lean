-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyOrder
public import Kernels.TmlFa4Fwd.Proof.PollSafety
public import Lemmas.Order.WaitOrderEnables

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.AsyncCopy

noncomputable section

/-- A dependency through a guarded group copy reaches the performed arrive-on itself,
through the tracked copy's write stage. -/
theorem loaderEmptyAcquireBeforeArriveOn {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {wait copy arrival : EvId}
    (hGuard : Resumes kernel X wait copy) (hTracks : TracksCpAsync X copy arrival)
    (hDone : X.async.arrived arrival = true) :
    Relation.TransGen (DepStep l kernel X) (.thread wait, true)
      (.async arrival .arriveOn, false) := by
  obtain ⟨s, ⟨pc, hCopy⟩, _⟩ := hTracks.2.2.1
  have hWrite : X.AsyncPresent copy (.write .copy) :=
    (hX.tma.2.2.2 arrival hDone).2 copy hTracks
  have hIssue : DepStep l kernel X (.thread copy, false) (.async copy (.write .copy), false) :=
    DepStep.issue ⟨_, hCopy⟩ hWrite (by simp) (by simp) (by simp) (by simp)
  exact (((Relation.TransGen.single (DepStep.of_resumes l hGuard)).tail hIssue).tail
    (DepStep.node hWrite)).tail (DepStep.stage (.inr ⟨rfl, rfl, hTracks, hWrite, hDone⟩))

end
end PTX.Kernels.TmlFa4Fwd.Loader
