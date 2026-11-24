-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Lib.BarLanePhase
public import Kernels.InklingRelDecode.Proof2.Lib.BarLaneKeys
public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneLoop
public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneFault
public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneCta
public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneLate
public import Kernels.InklingRelDecode.Proof.Protocol.BarLanePub

@[expose] public section

/-!
# Umbrella of the named-barrier lane and loop-group files

* `BarLanePhase`: the generation ledger of a barrier with a loop group;
* `BarLaneKeys`: the keys of loop arrivals;
* `BarLaneLoop`: `bar128Witness`, `bar128Causal`;
* `BarLaneFault`: pending arrivals (`no_dup_pending`, `pending_ordinal`, `no_fault_of_mismatch`);
* `BarLaneCta`: `bar_no_mismatch` and the premises `AlphaAgree`, `WorkerLate`;
* `BarLaneLate`: `workerLate_of_roleReads`, `ctaBar_of_roleReads`;
* `BarLanePub`: `pub_bar1`, the barrier-1 half of the publication of the initializations.
-/
