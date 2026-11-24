-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Mem
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.TmemTrace
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Open
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem

@[expose] public section

/-! # The write and the reads of the allocation word, by the allocation they follow

The store of the allocation word is lane 0's, the event after its allocation (`mma_alloc_wr`). Every
access of memory from the role's code follows the lane's allocation (`mma_alloc_rd`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The store of the allocation word.** -/
theorem mma_alloc_wr (hw : Prologue.warpIndex L g = 12) {pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) :
    laneOf L g = 0 ∧ ∃ k', k = k' + 1 ∧ AllocAt L X g k' := by
  have hg := Frame.lt_of_get hX he
  have hkl : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  rcases Mma.open_ev hp hX hFw hw he (fun f h => by cases h) with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨s, n, hσ, -, hi, hev⟩ | ⟨d, n, hσ, h0, hR, hi, hev1⟩
  · exact (start_mem hev hi.2 trivial).elim
  · obtain ⟨t, ins, o, hat, hi', hc, hf⟩ :=
      Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
    have hk3 := Mma.pre_kind hp hat hc hf
    cases s with
    | set => obtain ⟨_, h⟩ := hk3.1 rfl; cases h
    | alloc => cases hk3.2.1 rfl
    | wr => exact mma_trace hp hX hg hw k hkl _ hσ
    | enter => exact absurd hi.2 (by simp [Mma.Start.exit])
  · exfalso
    have epi : ∀ d, ¬ Epilogue.Ev p L g d ⟨pc, .wr a bs⟩ := by
      intro d h
      unfold Epilogue.Ev at h
      split at h <;> simp_all [Epilogue.isStore]
    unfold Mma.Ev at hev1
    split at hev1
    all_goals first
      | exact epi _ hev1
      | simp_all

/-- **A read by the MMA warp's role** follows its lane's allocation. -/
theorem mma_alloc_rd (hw : Prologue.warpIndex L g = 12) {pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) :
    ∃ k' < k, AllocAt L X g k' ∧ StoreAt L X g k' := by
  have hg := Frame.lt_of_get hX he
  have hkl : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  rcases Mma.open_ev hp hX hFw hw he (fun f h => by cases h) with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨s, n, hσ, -, hi, hev⟩ | ⟨d, n, hσ, h0, hR, hi, hev1⟩
  · exact (start_mem hev hi.2 trivial).elim
  · rcases hev with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
  · exact (mma_trace hp hX hg hw k hkl _ hσ).1

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
