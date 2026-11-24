-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.LpRun
public import Kernels.InklingRelDecode.Proof.Protocol.LpReach

@[expose] public section

/-!
# The loader and the KV ring from the thread's states (umbrella)

* `LpRun`: the loader's anchored run (`Lp.loader_anchor`) from the thread's states: the entry of
  the role is unique (`loader_entry_unique`), the loop's anchor `bar0` is unique
  (`loader_bar0_unique`), and no ring event precedes it (`loader_fresh_ev`);
* `LpReach`: progress backward from the exit: a thread of warp 6 that led its elections reaches
  every copy site of every block it loads (`loader_reaches`), and warp 6 has such a thread
  (`exists_lead`).
-/
