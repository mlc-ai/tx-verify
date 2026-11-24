-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDEpi
public import Kernels.InklingRelDecode.Proof.Thread.EvDProCopy

@[expose] public section

/-!
# Event shapes of the default partition's epilogue and prologue

The role machines export which state follows a fired event (`Epi.next`, `ProA.next`); the files
imported here prove what each event is, as statements over the machines' abstract states:
"if `Fired L g d e (some u)` and `d.site` is `s`, the event `e` has the shape of `s`".

* `EvDBar`: the twelve mbarriers by function (`kvReady slot`, `kvEmpty slot`, `sReady b`,
  `pReady b`, `oDone`, `oFinal`) and their offsets from the shared base.
* `EvDFires`: kernel-independent facts about `Fires` for the instruction forms the two roles use
  (global and shared stores, global loads, polls, arrivals, initializations, elections, tensor
  loads, barriers, fences, `tcgen05.ld`).
* Epilogue (`Epi`): `EvDEpiBase` (vocabulary), `EvDEpiSync` (poll, broadcast, load, barriers,
  register request, table write, release, return), `EvDEpiStore` (the 65 output stores),
  `EvDEpiMeans` (what `Prm` means for the launch; the store addresses are the output arrays of
  `Spec`), `EvDEpi` (`Shape` and `shape`: one statement for every site).
* Prologue (`ProA`): `EvDProBase` (vocabulary), `EvDProSites` (the site families),
  `EvDProSync` (elections, barrier initializations, `expect_tx`, barriers, fences, role table,
  `(num_pre, num_iters)`), `EvDProLoad` (the request words and the block-table and query loads),
  `EvDProStore` (the Q stores), `EvDProCopy` (the K/V tensor copies).

What is not proved, and why, is in the development notes: the rows of "thread-layer gaps" added
with these files.
-/
