-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame

@[expose] public section

/-! # The tensor stores are the output warp's -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A tensor store is warp 13's.** -/
theorem store_warp (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i : EvId} {addr : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue i addr s) : Prologue.warpIndex L i.1 = 13 := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  rcases mem_event hp hX hFw he trivial with ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ | ⟨_, hk, -⟩ |
    ⟨_, _, hk, -⟩ | ⟨_, _, -, hw⟩ | ⟨_, _, _, _, hk, -⟩
  · cases hk
  · cases hk
  · cases hk
  · cases hk
  · exact hw
  · cases hk

end PTX.Kernels.TmlFa4Fwd.Proof
