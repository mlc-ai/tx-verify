-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # An event is at its state's position -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **An event's position is the position of the state it is fired from.** -/
theorem ev_pc (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k pc : Nat}
    {kd : Kind} {σ : (thread p L g).D} (he : X.get (g, k) = some ⟨pc, kd⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) (hu : ∀ f, kd ≠ .ub f := by
      intro f h
      cases h) : pc = (thread p L g).pc σ :=
  Frame.event_pcU (fun _ hg => thread_sound hp hg) hX he hσ hu

end PTX.Kernels.TmlFa4Fwd.Proof
