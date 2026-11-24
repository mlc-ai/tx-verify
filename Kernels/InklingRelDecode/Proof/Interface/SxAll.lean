-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SxBaseFence
public import Kernels.InklingRelDecode.Proof.Interface.ClassCopyPage
public import Kernels.InklingRelDecode.Proof2.Safety.Box
public import Kernels.InklingRelDecode.Proof.Interface.SxGRead
public import Kernels.InklingRelDecode.Proof.Interface.SxQStore

@[expose] public section

/-!
# Interface facts of the shared orders and the global placement (umbrella)

* `SxBaseFence`: an early event of the common start before every copy and every worker event past
  barrier 1, through a `fence.proxy.async`;
* `SxGCopy`, `SxGRead`: the tensor copies' spec form and global sources, the thread reads and
  writes outside shared memory;
* `SxQStore`: the query stores before the MMAs' reads of the tile.
-/
