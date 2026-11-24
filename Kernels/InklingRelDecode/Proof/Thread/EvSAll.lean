-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvSShape
public import Kernels.InklingRelDecode.Proof.Thread.EvSBiasSpec
public import Kernels.InklingRelDecode.Proof.Thread.EvSEnt

@[expose] public section

/-!
# Event shapes of the softmax region (warps 0-3, pc 574-2332): umbrella

The softmax region's machine (`Sm.code`) exports which state follows an event (`Sm.next`); the
files imported here prove what each event of the sites that already have step lemmas *is*, as
statements over the machine's abstract states: "if `Fired L g d e (some u)` and `d.site` is `s`,
the event `e` has the shape of `s`". The one place the program counter appears is `Sm.evPc`.

* `EvSBase`: the vocabulary (`Fired`, `evPc`, `fired_unpack`), the launch's shared window
  (`SharedOk`), a full-warp butterfly shuffle's operand, the footprint of a global access.
* `EvSSync`: `setmaxnreg`, `bar.sync 1`, the `s_ready` poll, the warp-index broadcast,
  `tcgen05.wait::ld`, the named barriers `bar.sync 0, 128`, `tcgen05.wait::st`, the rescale
  test's butterfly shuffle.
* `EvSTile`: the S tile's `tcgen05.ld` (64 words, `.16x32bx2`; the machine's `D.sv` holds the
  returned words), the P tile's `tcgen05.st` (32 words, the conversions `D.pwV`), the
  `p_ready` arrival (barrier `pReady (i % 2)`, count 1, thread 0).
* `EvSBias`: the 64 preloads and 64 loop loads (`ld.global.b16`, two bytes at `biasAddr`).
* `EvSBiasSpec`: the bias loads in `Spec`'s terms: address `relBase + 2 (token · stride_rel + head ·
  1280 + relCol)` of the key's column, from the documented fields of `SmEntry.entOf`
  (`EntMeans`).
* `EvSEnt`: the prologue's `SmEntry.entOf` satisfies `EntMeans`.
* `EvSShape`: `Sm.Shape` and `Sm.shape`, one statement for every site that has one.

What is not proved, and why, is in the development notes: the rows of "thread-layer gaps" added
with these files.
-/
