-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SxOrder
public import Kernels.InklingRelDecode.Proof.Safety.PlNoNc
public import Kernels.InklingRelDecode.Proof.Interface.FootCopy
public import Kernels.InklingRelDecode.Proof.Interface.SxGRead
public import Kernels.InklingRelDecode.Proof.Interface.ClassCopyPage
public import Kernels.InklingRelDecode.Proof2.Safety.Box
public import Kernels.InklingRelDecode.Proof.Interface.SxAll

@[expose] public section

/-!
# The shared regions' orders and the global placement (umbrella)

* `SxOrder`: `Sx.order_of : SharedOrder L X` from the second tree's role table (base word, K
  and V rings, query tile, role word: `Proof2/Safety/BaseRace`, `KvSame`, `Race`), `SxTCount`,
  `SxTScratch` (the words above the tile);
* `globalReads`, `globalPlaced`: `Proof2.global_reads`, `global_placed` (`Proof2/Safety/GlobalW`).
-/
