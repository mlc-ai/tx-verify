-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithBase

@[expose] public section

/-! # A loop tile's row sum, part 3

The move of the new reference maximum (`mov.b32 %r3597, %r177`), as an outcome run (`movM`): it
continues when the value has four bytes. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem sum1_d {L : Launch} {g : Nat} (d : D) (s' : Site) (i t : Nat) (w : Nat → Value)
    (l x : Value) :
    SegD kernel asms L g 1 3727
      (factsX L g 3727 ⟨s', i, t, w, mNV L d, l⟩ [(286, x), (3932, d.m), (512, mNV L d)]) 3728
      (factsX L g 3728 ⟨s', i, t, w, mNV L d, l⟩ [(286, x)]) ((mNV L d).bytes = 4) :=
  ((SegD.outs (pc := 3727) (liveT := Flow.live 3728) (items := movM) (by decide +kernel)
    (by decide +kernel) (by kernel_rfl) (by decide +kernel) (orules_asms _ _ (by decide +kernel))
    (by decide +kernel)).weaken_end fun _ h => holds_live_congr (by kernel_rfl) h).iff
    ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
