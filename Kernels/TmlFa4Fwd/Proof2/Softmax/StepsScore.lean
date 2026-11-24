-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScoreFirst0
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScoreFirst1
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScoreFirst2
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScoreFirst3
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScoreBias0
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScoreBias1
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScoreBias2
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScoreBias3
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScoreSldw

@[expose] public section

/-! # The softmax warps' score loads

The eight score loads of the first and the biased rounds (one file per load, dispatched by
`stepAt_sld`); a plain round's implicit waits are `StepsScoreSldw.lean`'s `stepAt_sldw`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The score loads of the first and the biased rounds.** -/
theorem stepAt_sld (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = []) (hs : ∃ c, d.site = .sld .first c ∨ d.site = .sld .bias c) :
    (codeD p L g).StepAt d := by
  rcases hs with ⟨c, h | h⟩
  · fin_cases c
    · exact stepAt_sld_first_0 hp _hg d hk ha h
    · exact stepAt_sld_first_1 hp _hg d hk ha h
    · exact stepAt_sld_first_2 hp _hg d hk ha h
    · exact stepAt_sld_first_3 hp _hg d hk ha h
  · fin_cases c
    · exact stepAt_sld_bias_0 hp _hg d hk ha h
    · exact stepAt_sld_bias_1 hp _hg d hk ha h
    · exact stepAt_sld_bias_2 hp _hg d hk ha h
    · exact stepAt_sld_bias_3 hp _hg d hk ha h
