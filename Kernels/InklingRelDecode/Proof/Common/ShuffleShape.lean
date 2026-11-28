-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Where
public import Lemmas.Kernel.Frame
import Lemmas.Kernel.FrameU
import Kernels.InklingRelDecode.Proof.Common.Sound
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Kernels.InklingRelDecode.Flow.Code.Part019
import Kernels.InklingRelDecode.Flow.Code.Part040

@[expose] public section

/-! # The warp-index broadcasts are index shuffles of lane zero

A data thread broadcasts its warp index twice: in each Softmax round before the S load (pc 1261)
and once in the epilogue before the O load (pc 2603). Both are `shfl.sync.idx` with source lane 0
and clamp 31. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

/-- A shuffle event at a state whose site is one of the two broadcasts has mode `idx`, lane
operand 0 and clamp 31. -/
theorem bcast_shape {Q L m X g k s ev mode a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k) = some ev)
    (hs : Frame.stateAt (thread Q L) X g k = some (some s))
    (pc : (thread Q L g).pc s = 1261 ∨ (thread Q L g).pc s = 2603)
    (kind : ev.kind = .shfl mode a b c recv ok) : mode = .idx ∧ b = 0 ∧ c = 31 := by
  obtain ⟨t,ins,o,ht,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX get hs
    (fun _ h => by rw [kind] at h; cases h)
  rcases pc with pc | pc
  · rw [pc] at hc fire
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1261)
    obtain ⟨-, mode', bval, cval⟩ := Lib.shfl_operand (n := 0) rfl rfl fire kind
    exact ⟨mode', bval, cval⟩
  · rw [pc] at hc fire
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2603)
    obtain ⟨-, mode', bval, cval⟩ := Lib.shfl_operand (n := 0) rfl rfl fire kind
    exact ⟨mode', bval, cval⟩

end PTX.Kernels.InklingRelDecode.Proof
