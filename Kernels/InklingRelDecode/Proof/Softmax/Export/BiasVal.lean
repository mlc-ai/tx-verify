-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Softmax.BiasAt
import Kernels.InklingRelDecode.Proof.Softmax.Export.BiasAddress
import Lemmas.Kernel.Source.Launch

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Proof Control

private theorem bias_sites :
    (∀ j : Fin 64, Assumptions.inputReadSites.contains (680 + 2 * j.val) = true) ∧
      ∀ j : Fin 64, Assumptions.inputReadSites.contains (1124 + 2 * j.val) = true := by
  decide +kernel

/-- **A bias load returns the element of the relative logits it reads**: the one of the block
`x + R * splits` (preloads) or `x + (R + 1) * splits` (the loop's loads), `R` the polls of
`s_ready` before it, at the column `j` of the lane's half, as a `bf16` number. -/
public theorem bias_val {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (site : (∃ j : Fin 64, pc = 680 + 2 * j.val) ∨ ∃ j : Fin 64, pc = 1124 + 2 * j.val) :
    ∃ z x y j B : Nat, z = (L.ctaidOf (g / L.block)).get .z ∧ x = (L.ctaidOf (g / L.block)).get .x ∧
      y = (L.ctaidOf (g / L.block)).get .y ∧ j < 64 ∧ Q.nBias z ≤ B ∧
      ((pc = 680 + 2 * j ∧ B = x + pollRound 1257 ((X.tr g).take k) * Q.splits) ∨
        (pc = 1124 + 2 * j ∧ B = x + (pollRound 1257 ((X.tr g).take k) + 1) * Q.splits)) ∧
      rebuild 3 bs = .ok (Value.float .bf16 (Q.rel (Q.qStart z + token (g % L.block))
        (y * 6 + headInGroup (g % L.block))
        (B * 128 + 64 * (g % L.block / 16 % 2) + j + relPad - Q.blocks z * 128))) := by
  obtain ⟨z, x, y, j, B, hz, hx, hy, hzb, hj, hB, hn, ht, hh, hc, hsel, loc, size⟩ :=
    bias_at hp hX hf (.inl he) site
  have ro := Frame.LaunchReads.of_forall (hX.asm _ (show Assumptions.inputReadOnly ∈
    Assumptions.all by simp [Assumptions.all]))
  refine ⟨z, x, y, j, B, hz, hx, hy, hj, hn, hsel, Frame.LaunchReads.value hX ro he ?_
    (by rw [size]; rfl) (fun _ _ => trivial) (fun i hi => ?_) (by decide : 0 < 2) rfl⟩
  · rcases site with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact bias_sites.1 j
    · exact bias_sites.2 j
  · rw [loc]
    exact hp.relInput z hzb _ ht _ hh _ hc i hi
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
