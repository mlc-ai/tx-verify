-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Lib.SoftLane
public import Kernels.InklingRelDecode.Proof.Lib.QueryCoord
public import Lemmas.Flow.PollRounds

@[expose] public section

/-! # What the score loads of a lane return

The score load of the poll round `r + 1` returns, for a row that loads, the specification's scores
of the lane's row and the keys of its half of the block of round `r`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof

/-- **The score loads of thread `g` return the specification's scores.** -/
def ScoreEv (Q : Params) (L : Launch) (g : Nat) (X : Execution) : Prop :=
  ∀ k a vals sh, X.get (g, k) = some ⟨1265, .tc (.ld a vals sh)⟩ →
    QRowValid Q L (g / L.block) (softRow (g % L.block)) → ∀ j < 64,
      vals[j]? = some (.float .f32 (laneScore Q L g (pollRound 1257 ((X.tr g).take k) - 1) j))

end PTX.Kernels.InklingRelDecode.Proof.Lib
