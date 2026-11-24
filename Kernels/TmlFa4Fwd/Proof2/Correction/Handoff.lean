-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Correction.Machine

@[expose] public section

/-! # The correction warps' first state, for the startup's hand-off

The facts of the machine's first state (`setmax`, pc 7746) as an explicit list over the
registers live there (`facts_init`): the warp index, the shared base and five shared-memory
barrier addresses, the batch, and the LSE and request pointers. The startup's hand-off to this
role (lane T1's `Common/Sound.lean`, `handoff`) compares them with the startup's facts at
`enter correction`: the shared base `x1` and the warp index `x3` that the role's gate fixes
(`x1 = sharedBase`, `x3 = g % L.block / 32`), the addresses `addi x1 n`, the batch word and the
ABI registers. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

theorem live_7746 :
    Flow.live 7746 = [1062, 1069, 2390, 2535, 6495, 6497, 7277, 7500, 7501, 7502, 7503, 7506] :=
  by rfl

/-- **The facts of the correction machine's first state.** -/
theorem facts_init (p : Params) (L : Launch) (g : Nat) :
    (code p L g).facts (code p L g).init =
      [(1062, b32 (g % L.block / 32)), (1069, b32 (L.sharedBase + 192)),
       (2390, b32 (L.sharedBase + 208)), (2535, b32 L.sharedBase),
       (6495, b32 (L.sharedBase + 144)), (6497, b32 (L.sharedBase + 224)), (7277, b32 p.batch),
       (7500, b64 p.lseBase), (7501, b64 p.lseStride), (7502, b64 p.cuQBase),
       (7503, b64 p.usedKBase), (7506, b64 p.cuQBase)] := by
  show Flow.factsFrom (Flow.live 7746) _ = _
  rw [live_7746]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Correction
