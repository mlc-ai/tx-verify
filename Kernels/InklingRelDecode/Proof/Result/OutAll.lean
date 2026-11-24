-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.OutRow
public import Kernels.InklingRelDecode.Proof.Result.OutProb
public import Kernels.InklingRelDecode.Proof.Result.OutEpi
public import Kernels.InklingRelDecode.Proof.Result.OutLoad
public import Kernels.InklingRelDecode.Proof.Result.OutPremises
public import Kernels.InklingRelDecode.Proof.Result.OutStore
public import Kernels.InklingRelDecode.Proof.Result.OutSm
public import Kernels.InklingRelDecode.Proof.Result.OutIssued
public import Kernels.InklingRelDecode.Proof.Result.OutOrigin
public import Kernels.InklingRelDecode.Proof.Result.OutPost

@[expose] public section

/-!
# From the data path to `Post` (result layer, part 2)

Design note and umbrella of the `Out*` files. They carry the MMA data path (`Mma*.lean`, part 1)
and the epilogue's stores to `Spec.Post`, and end in `Out.result_goal`, the framework's
`ResultGoal` for the kernel, from one premise structure `Out.Inputs`. They speak only of abstract
states (`Interface.St`, `Epi.D`, `Mma.D`), events, `Spec`'s quantities and Tensor Memory cells; no
program counter and no register number occurs.

## What is proved (default heartbeats, the three standard axioms)

* **(1) The online-softmax fold is the Spec** (`OutRow`). The blocks the CTA `(split, kv_head,
  request)` feeds `Softmax.run` for one output row are the visible keys `k ≤ past + tok` of the
  key blocks `split + b · num_splits`, `b < num_iters`, with the logit `S + bias · (1 /
  softmax_scale)` (`blocks`, `Vis`, `logit`; the bias is `Spec.bias`: zero before `n_bias`, the
  relative logit of column `relCol` after) and the cache's value. `sum_keys` shows the keys of the
  blocks are exactly `Spec.keys` once each (`mem_keys`, from `Geometry.numIters_spec`), so
  `rowSum_eq`, `numerator_eq`: the sums of `W` and `W · v` over the flattened blocks are
  `Spec.rowSum`, `Spec.numerator` (`weight_eq`: `Spec.weight` is `W (scale · 0f3FB8AA3B)` of the
  logit). `row_empty` and `row_nonempty` say what the run leaves, by `Softmax.fold_empty`,
  `fold_normalized`, `fold_lse`, `fold_invariant`: for `rowSum = 0` the initial state, `oPart = 0`;
  else `l > 0`, `m` finite, `o / l = Spec.oPart` and `m · sl + log2 l = Spec.lsePart`. The state's
  maximum and sum do not depend on the values (`run_ml_congr`), so `rowState` (value-free blocks)
  is what the softmax threads' registers hold for every column.
* **The O accumulator is the run's numerator** (`OutProb`). `pElemE` (`Softmax.step`'s `p_k` on a
  visible key, `0` on a masked one) and `alphaRow` (`Softmax.step`'s `alpha`), from the scores
  alone (`alpha_congr`, `mUse_congr`), are the functions `Mma.PTile` and `Mma.OAcc` are taken for;
  `oFull_last`: after block `num_iters - 1` the O cell is `colState`'s numerator
  (`MmaRun.oFull_eq_run`).
* **(2) The stored values** (`OutEpi`, `OutLoad`, `OutStore`). `RowIn`: the registers the
  softmax region leaves are `rowState`'s (the scale `scale_log2`, `l`, `m`). From it: the zero test
  holds exactly for an empty row (`eq0_iff`), the reciprocal is `1 / l` or `1` (`inv_eq`, A2),
  word `k` of `OPart` is the f32 float of `Spec.oPart` (`word_oPart`), the `LsePart` word is the f32
  float of `Spec.lsePart` (`lseWord_lsePart`, `Br.lse_fin`) or the `-inf` pattern (`eq0_of_empty`).
  The `tcgen05.ld` of the epilogue reads cell `(rowM tid, tm + 256 + 64 · half + j)` of the PV
  accumulator (`taddr_cell`), so register `j` is the numerator of `colState` (`load_word`,
  `Mma.o_load`). `write_spec` combines these: every global write of a complete execution is a
  store of word `dc` of `OPart[split, token, head]` of a valid row with the bytes of `oWord`, or
  of `LsePart[split, token, head]` with the bytes of `lseWordOf`.
* **Where the epilogue's state comes from** (`OutOrigin`). The epilogue keeps its registers and
  branch flag and is entered only from the softmax state that left the loop (`epi_origin`), so
  `smExit` gives `RowIn` (`rowIn_of_smExit`), `SmMeans.ent.r25 = Spec.numIters` gives the skip
  (`skip_of`), and a state past the load carries the words of an earlier `tcgen05.ld` (`ld_event`).
* **The stores exist** (`OutIssued`). The epilogue's sites have positions; a state past a store
  site had visited it (`visits`, from `Interface.stateAt_pred` and the successor relation
  `Epi.next`); in a complete execution every thread exits from the epilogue's return, so the thread
  of a valid row visits every store site of its words and fires the store event there
  (`exists_oStore`, `exists_lseStore`, with `thread_of_cta`, `tid_of_row` for the thread of a row).
* **(3) `Post`** (`OutPost`). The writers of a byte are among the events of the launch's threads
  (`allWrites`); distinct output words do not overlap and a token belongs to one request
  (`token_unique`), so every writer of a byte of an output word stores the same word, and the
  final memory holds its byte (`final_oByte`, `final_lseByte`, `IsFinal.of_agree`); the words
  read as `oPart` and `lsePart` or the `-inf` bytes (`post_of`); the last conjunct of `Post` is
  `ThreadFacts.post_frame`. `result_goal` is `ResultGoal kernel Assumptions.all L mem0 (Post Q
  mem0)` for every `Pre`-launch whose consistent complete executions have `Inputs`.

## What `Inputs` takes (rows of "thread-layer gaps" in the development notes)

`smOb`, `premises` (thread layer); the MMA premises `kvCopies`, `kvOrder`, `qTile`, `mmaWords`,
`qkChain`, and `pTile`, `oAcc` for exactly `pElemE`, `alphaRow` (MMA data path, softmax region);
`smExit` (softmax region: its last state holds the scale and `Sm.Corr` of the row's blocks);
`oSource` (protocol layer: the last PV MMA is the read source of the epilogue's `O` load). The file
`OutPremises.lean` states each and names the layer that supplies it. Proved here, not premises: the
epilogue's registers (`OutOrigin.rowIn_of_smExit`), the skipped load (`skip_of`), the load event
(`ld_event`), and the stores' existence (`OutIssued`).
-/
