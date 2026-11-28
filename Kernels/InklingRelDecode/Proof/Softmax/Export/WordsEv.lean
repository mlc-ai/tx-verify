-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.RecvHalf
public import Kernels.InklingRelDecode.Proof.Lib.LaneFold
import Kernels.InklingRelDecode.Proof.Softmax.Export.AlphaOperand

/-! # The words of a lane's rounds are exact

The words a valid lane sends and receives at pc 1838 are the maxima of the two halves of the
round's block, so they read as numbers whose maximum is the block's maximum. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow

variable {Q : Params} {L : Launch} {g : Nat}

/-- **The words of a shuffle of pc 1838 are exact**: their maximum is the block's. -/
public theorem words_ev {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hB : ∀ g, Lib.BiasEv Q L g X) (hS : ∀ g, Lib.ScoreEv Q L g X) (lane : g % L.block < 128)
    (hv : Lib.QRowValid Q L (g / L.block) (Lib.softRow (g % L.block))) :
    ∀ k mode sent b c recv ok, X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ →
      ∃ aE bE, Lib.Ev sent aE ∧ Lib.Ev recv bE ∧ max aE bE =
        Lib.SoftFold.blockMax (Lib.laneBlk Q L g (pollRound 1257 ((X.tr g).take k) - 1)) := by
  intro k mode sent b c recv ok get
  obtain ⟨rfl, rfl, rfl⟩ := shfl5_shape hp hX get
  obtain ⟨lt, h1⟩ := sent_half hp hX hf (hB g) (hS g) hv get
  have h2 := recv_half hp hX hf hB hS lane hv get
  have hb := Lib.blockMax_halves (d := 0) (h := Lib.laneHead L g)
    (tok := Lib.softRow (g % L.block) / 6) (hp.splitsPos) hp.scalePos lt
  refine ⟨_, _, h1, h2, ?_⟩
  unfold Lib.laneBlk
  rw [hb]
  rcases Nat.mod_two_eq_zero_or_one (g % L.block / 16) with h | h
  · rw [h]
  · rw [h]; exact max_comm _ _

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
