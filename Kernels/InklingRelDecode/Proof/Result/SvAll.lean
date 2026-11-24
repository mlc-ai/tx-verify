-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.SvVals

@[expose] public section

/-!
# The softmax region's iteration invariant: umbrella

`Interface/SvAlg` (a permutation of a block's scores leaves `Softmax.step`'s maximum and sum alone;
the running maximum is never `+inf`), `SvDef` (the specification's numbers of a row's half: keys,
logits, `halfScores`; `EntFull`), `SvScore` (the final score words are the masked logits),
`SvStage` (`StageOk`, `stage_pair`: the two shuffles make the update `Softmax.step`'s),
`SvInv` (the invariant `SvInv`), `SvStep` (frame lemmas), `SvSetup` (the loop test and the next
block's loads' guard), `SvPair` (the update `SvInv.toBar20` and the two shuffles `SvInv.pair`
with the exchange premise `ExchEv`), `SvSites` (the premises on the events `EvOk`), `SvRun`
(`SvInv.step`: one step at every site but the second shuffle) and `SvExit` (the region's last
state: `SvInv.exit_corr`), `SvBias` (a bias load returns the key's bias: `evOk_of`), `SvPred` (the
predecessor of a region state along a trace), `SvTrace` (`sv_inv_at`: the invariant along a thread
under `SvPrem`; `sm_exit_corr`), `Result/SvOut` (`blk_fst_halves`; `smExit_of`:
`Out.Inputs.smExit`), `Result/SvScoreLoad` (`SLoadSrc`, `ExchPrem`, `svPrem_of`: `SvPrem` from
the read source of the S load and the partner exchange), `Result/SvVals` (`alr_eq`, `pf_eq`,
`pstore_words`: the rescale factor, the stored probabilities and the words of the `P` store are
`Out.alphaRow`, `Out.pElemE` and their `bf16` pairs).
-/
