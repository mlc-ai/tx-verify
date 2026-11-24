-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RdSmCount
public import Kernels.InklingRelDecode.Proof.Protocol.RdMmaRun
public import Kernels.InklingRelDecode.Proof.Protocol.RdMmaUniq

@[expose] public section

/-!
# The softmax thread's and the MMA lane's anchored runs, from the thread's states: umbrella

* `RdSmCount`: the softmax thread's successful polls of `s_ready` and `o_done` before each of its
  states (`Rd.sm_cnt`), by induction over the thread's states with no anchor premise;
* `RdMmaRun`: the MMA lane's anchored run (`Rd.mma_anchor`), no commit before the entry of the role
  (`RoleReads`), the numbering of the lane's QK and `o_done` commits (`Rd.qk_commit_block`,
  `Rd.o_commit_block`);
* `RdMmaUniq`: two states of the lane at one site and iteration are one (`Rd.pv7_unique`).

Not imported by `Protocol/All.lean`, `Result/OutAll.lean`.
-/
