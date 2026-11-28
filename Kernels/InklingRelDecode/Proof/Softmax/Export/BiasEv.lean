-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.BiasEv
import Kernels.InklingRelDecode.Proof.Softmax.Export.BiasVal

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Proof Control

private theorem token_eq : ∀ r < 64, r * 43 / 256 = r / 6 := by decide

private theorem bias_key {Q : Params} {L : Launch} {g R B j : Nat}
    (hz : Q.nBias ((L.ctaidOf (g / L.block)).get .z) ≤ B)
    (hB : B * 128 = 128 * (Q.splits * R + (L.ctaidOf (g / L.block)).get .x)) :
    Lib.laneBias Q L g R j = Q.rel (Q.qStart ((L.ctaidOf (g / L.block)).get .z) +
      token (g % L.block)) ((L.ctaidOf (g / L.block)).get .y * 6 + headInGroup (g % L.block))
      (B * 128 + 64 * (g % L.block / 16 % 2) + j + relPad -
        Q.blocks ((L.ctaidOf (g / L.block)).get .z) * 128) := by
  have hr : Control.row (g % L.block) < 64 := by unfold Control.row; omega
  have ht : token (g % L.block) = Control.row (g % L.block) / 6 := by
    unfold token; exact token_eq _ hr
  have hh : headInGroup (g % L.block) = Control.row (g % L.block) % 6 := by
    unfold headInGroup; rw [ht]; omega
  have key : Lib.laneKey Q L g R j = B * 128 + 64 * (g % L.block / 16 % 2) + j := by
    unfold Lib.laneKey; omega
  have en : Q.nBias ((L.ctaidOf (g / L.block)).get .z) * 128 ≤ Lib.laneKey Q L g R j := by
    rw [key]; omega
  have sr : Lib.softRow (g % L.block) = Control.row (g % L.block) := rfl
  unfold Lib.laneBias bias
  rw [ite_eq_left_iff.mpr (fun h => absurd en h)]
  simp only [Lib.laneHead, sr, ht, hh, key, relCol]
  congr 2
  omega

/-- **A bias load returns the specification's bias of its key** (the lane's thread, column and
round). -/
public theorem bias_ev {Q L m X g} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : Lib.BiasEv Q L g X := by
  intro k pc a bs j hj he
  constructor
  · intro hpc
    obtain ⟨z, x, y, j', B, rfl, rfl, rfl, hj', hn, hsel, hv⟩ :=
      bias_val hp hX hf he (.inl ⟨⟨j, hj⟩, hpc⟩)
    rcases hsel with ⟨h1, hB⟩ | ⟨h1, -⟩
    · have : j' = j := by omega
      subst this
      rw [hv, bias_key hn (by rw [hB]; ring)]
    · omega
  · intro hpc
    obtain ⟨z, x, y, j', B, rfl, rfl, rfl, hj', hn, hsel, hv⟩ :=
      bias_val hp hX hf he (.inr ⟨⟨j, hj⟩, hpc⟩)
    rcases hsel with ⟨h1, -⟩ | ⟨h1, hB⟩
    · omega
    · have : j' = j := by omega
      subst this
      rw [hv, bias_key hn (by rw [hB]; ring)]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
