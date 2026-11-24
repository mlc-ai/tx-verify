-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.IpMmaNext
public import Kernels.InklingRelDecode.Proof.Protocol.IpMmaThread
public import Kernels.InklingRelDecode.Proof.Protocol.IpMmaPoll

/-!
# The MMA warp's election, its last commit, and the epilogue's poll: umbrella

* `IpMmaNext` (with `Thread/IpMmaNext`, `Interface/IpMmaTrace`): `IpMma.nextCommit`,
  `Life.NextCommit`: a commit at pc 2546 or 2548 is followed by the thread's `o_final` commit;
* `IpMmaThread`: `IpMma.mmaThread`, the thread-layer conjuncts of `Tmem1.OFinalFacts` (one MMA
  thread per CTA, its `o_final` commit is its first, every MMA of the CTA is before it);
* `IpMmaPoll`: `IpMma.dealloc_poll`, the `hpoll` premise of `Tmem1.mmaDoneDealloc_of`.
-/
