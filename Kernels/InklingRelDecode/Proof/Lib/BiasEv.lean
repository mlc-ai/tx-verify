-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.SoftLane
public import Lemmas.Flow.PollRounds

@[expose] public section

/-! # What the bias loads of a lane return

The bias load of column `j` of the preloads (pc `680 + 2 j`) returns the specification's bias of
the key of the round the polls of `s_ready` before it count, the loop's (pc `1124 + 2 j`) that of
the next round. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof

/-- **The bias loads of thread `g` return the specification's biases.** -/
def BiasEv (Q : Params) (L : Launch) (g : Nat) (X : Execution) : Prop :=
  ∀ k pc a bs j, j < 64 → X.get (g, k) = some ⟨pc, .rd a bs⟩ →
    (pc = 680 + 2 * j → rebuild 3 bs =
      .ok (Value.float .bf16 (laneBias Q L g (pollRound 1257 ((X.tr g).take k)) j))) ∧
    (pc = 1124 + 2 * j → rebuild 3 bs =
      .ok (Value.float .bf16 (laneBias Q L g (pollRound 1257 ((X.tr g).take k) + 1) j)))

end PTX.Kernels.InklingRelDecode.Proof.Lib
