-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsSelectPre
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsSelectTiles
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsSelectVote

@[expose] public section

/-! # The softmax warps' select: its three sites

`stepAt_select`: the first pass's ballot, the shuffles before the tiles and the tile choice, each
in its own file (`StepsSelectVote.lean` and friends), dispatched here. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_select (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .vote false ∨ d.site = .pre false ∨ d.site = .tiles false) :
    (codeD p L g).StepAt d := by
  rcases hs with h | h | h
  · exact stepAt_select_vote hp _hg d hk ha h
  · exact stepAt_select_pre hp _hg d hk ha h
  · exact stepAt_select_tiles hp _hg d hk ha h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
