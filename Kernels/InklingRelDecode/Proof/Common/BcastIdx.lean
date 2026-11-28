-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.ShuffleShape
import Kernels.InklingRelDecode.Proof.Common.Sound
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # The two warp broadcasts are index shuffles

A clean shuffle event of a data lane at the pc of a warp-index broadcast (1261 or 2603) has the
mode `idx`, the lane operand 0 and the clamp 31. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem bcast_idx (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {i : Nat} {pc : Nat} {mode a b c recv ok}
    (hev : X.get (g, i) = some ⟨pc, .shfl mode a b c recv ok⟩) (hpc : pc = 1261 ∨ pc = 2603) :
    mode = .idx ∧ b = 0 ∧ c = 31 := by
  have hg := Frame.lt_of_get hX hev
  have clean : ∀ f, (Kind.shfl mode a b c recv ok) ≠ .ub f := fun f h => by cases h
  obtain ⟨s, hs, -⟩ := Frame.good_stateU (C := thread Q L) (J := guardedTable Q L)
    (fun g hg => thread_sound hp hg) hX hev (fun pc f h => clean f (congrArg Event.kind h))
    (hf g hg i)
  have pos := Frame.event_pcU (fun g hg => thread_sound hp hg) hX hev hs clean
  exact bcast_shape hp hX hev hs (by rw [← pos]; exact hpc) rfl

end PTX.Kernels.InklingRelDecode.Proof
