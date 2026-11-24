-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.MmaBf16
public import Kernels.InklingRelDecode.Proof.Result.MmaCopy
public import Kernels.InklingRelDecode.Proof.Result.MmaEvents
public import Kernels.InklingRelDecode.Proof.Result.MmaLayout
public import Kernels.InklingRelDecode.Proof.Result.MmaPremises
public import Kernels.InklingRelDecode.Proof2.Lib.KvBox
public import Kernels.InklingRelDecode.Proof.Result.MmaO
public import Kernels.InklingRelDecode.Proof.Result.MmaOperand
public import Kernels.InklingRelDecode.Proof.Result.MmaPremises
public import Kernels.InklingRelDecode.Proof.Result.MmaQStore
public import Kernels.InklingRelDecode.Proof.Result.MmaRun
public import Kernels.InklingRelDecode.Proof.Result.MmaScore

@[expose] public section

/-!
# The MMA data path of the Inkling decode kernel (result layer, part 1)

Design note and umbrella of the `Mma*` files. They say what the MMA warp's QK and PV MMAs read
and what they leave in Tensor Memory, as exact reals, for a consistent complete execution. They
speak only of abstract states (`Interface.St`, `Mma.D`, `Loader.D`), events, `Spec`'s quantities
and Tensor Memory cells; no program counter and no register number occurs.

## What is proved (default heartbeats, the three standard axioms)

* **(a) The operands are the intended data** (`MmaOperand`).
  `qk_b_element`: element `(n, kk)` of the B operand of QK MMA `j` of iteration `i` is the bf16
  value `kVal r kvh (128 (split + i · num_splits) + n) (16 j + kk)` of the cache.
  `pv_b_element`: element `(n, kk)` of the B operand of PV MMA `j` of iteration `i` is the bf16
  value `vVal r kvh (128 (split + (i - 1) · num_splits) + 16 j + kk) n`.
  `qk_a_element`: element `(r, kk)` of the A operand of QK MMA `j`, for a valid tile row `r`, is
  the bf16 query `qElem` of the row's token `r / 6` and head `6 kvh + r % 6` at index `16 j + kk`.
  The proofs read the byte the MMA observes from the one write that precedes the read
  (`MmaEvents.read_byte_of_write`, from `Lemmas/Async/ReadReuse.lean`), and for K and V compute the
  byte the copy writes: the operand address of the decoded descriptor (`MmaLayout.qk_b_loc_eq`,
  `pv_b_loc_eq`, `qk_a_loc_eq`: K-major and MN-major 128-byte swizzle, the descriptor words of
  `EvW.QkIssue` / `PvIssue` decoded) is the address the tensor copy of the box holding the element
  writes (`copy_loc_kv`), and the copy writes the cache's bf16 element (`MmaCopy.kv_copy_written`:
  the tile semantics of the `kv_rows` map, the box inside the map, no write to an input byte,
  `Pre.kvInput`).
* **(b) The S tile** (`MmaScore`). `qk_writeCell`: the cells a QK MMA writes. `qk_eval`: the
  kernel's assumption evaluates it to the sum of 16 products plus the old accumulator
  (`MmaBf16.eval_all`: the `kind::f16` bf16 form of `Assumptions.idealArith`).
  `qk_result`: after step `j` of iteration `i` the cell `(r, c)` of score buffer `i % 2` holds,
  as a `TcMma.Result`, the f32 float of `Σ_{d < 16 (j + 1)} q(r, d) · K(c, d)`. `qk_score`: after
  step 7 it is `Spec.score` of token `r / 6`, head `6 kvh + r % 6` and key
  `128 (split + i · num_splits) + c`. `score_load`: a `tcgen05.ld` register that reads the cell
  with step 7 as its read source holds that float.
* **(c) The O accumulator** (`MmaO`, `MmaRun`). `pv_writeCell`, `pv_eval`: as for QK.
  `pv_result`: step `j` of block `b = i - 1` leaves `oBase b + Σ_{kk < 16 (j + 1)} P(b, kk) ·
  V(b, kk, n)`; `pv_final`: step 7 leaves `oFull b`, with `oFull 0 = Σ P · V` and `oFull (b + 1) =
  alpha (b + 1) · oFull b + Σ_{kk < 128} P(b + 1, kk) · V(b + 1, kk, n)`; `o_load`: a load of the
  cell with step 7 as its read source holds it. `MmaRun.oFull_eq_run`: with `Softmax.step`'s own
  `alpha` and `p_k` (`alphaOf`, `mUseOf`, `step_o`), `oFull b` is the numerator `o` of
  `Softmax.run` over the blocks `0 … b`.
* Small proved pieces the premises use: `MmaQStore.qstore_value` (a Q store of two bf16 values
  writes their four bytes), `MmaLoader.loader_copy_spec` (a loader copy state's event, in the shape
  `KvCopies` has, from `EvW.ldCol_spec` and `ldRow_spec`), `MmaEvents.mma_event_cases` and
  `mma_operands` (an MMA event is a QK or PV step of the MMA warp; a complete execution records its
  operands).

## What the proofs take as premises (`MmaPremises`, `MmaO`; "thread-layer gaps")

`KvCopies` (the copy events of every block and their specs), `KvOrder` (the order of a copy and
the MMA read, and that nothing else writes the byte), `QTile` (the stores of the Q tile, their
addresses and values, and their order before the QK reads), `MmaWords` (`d.n` is `num_iters`,
`d.tm` is 0), `QkChain` and `OAcc` (the accumulator read sources of the chains, and for step 0 of
a block after the first either the lazy skip or the rescale store), `PTile` (the probabilities in
Tensor Memory). Each field says which thread-layer fact or protocol order it stands for.

## What is not proved

* The premises themselves. `KvOrder` is the one the protocol layer is closest to
  (`Ring.Kv.copy_read_order` gives its first half under `Kv.Hyp`); the others wait for the
  thread-layer facts of the gap rows (prologue copy forms, Q store addresses and values, the
  `Sm` rescale sites and P stores, the state predecessors).
* Rows `r ≥ 60` and tokens `≥ q_len` of the S and O tiles (padding rows carry no stated value;
  that their evaluation does not fault is a safety fact).
* The value of the S tile for masked keys is stated like any other (the product is exact); the
  mask and the bias are the softmax's.
* The final step from `oFull_eq_run` to `Spec.oPart` and `lsePart` (the visibility, the bias and
  `Softmax.fold_invariant`, `fold_lse`) is the softmax side's.

## Generic lemmas for promotion to `Lemmas/`

`MmaBf16`: `idealMmaElement_of_bytes_bf16`, `idealMmaDot_sum_bf16`, `eval_sum_bf16` (the bf16 form
of `Lemmas/Tcgen05/TcMmaIdealSum.lean`). `MmaEvents`: `read_byte_of_write` (any writer) and
`element_bf16`. `MmaLayout`: `byteAddress_k_exact`, `byteAddress_mn_exact` (the exact swizzled
address of a 2-byte K-major / MN-major element), `copy_addr`. `MmaCopy`: `kv_readLoc` and
`kv_noOob` (the port of Fp16Gemm8192's `copy_readLoc` to a descriptor given as a record).
`MmaRun`: `step_o`, `run_snoc`, `sum_blockOf` belong with `Softmax.lean`.
-/
