-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.TmemPairHistory

@[expose] public section

namespace PTX.Tmem.Pair
noncomputable section

/-! ## OBJ-TMEM-COMPLETION-PREFIX — synchronous resource completion prefixes
Statement: An allocation-management operation is complete only when every earlier request, in
  program order, of each of its warps belongs to a complete operation.

Defs: Tmem.Pair.CompletionReady, Tmem.Pair.CompletionClosed

Source:
- §9.7.18.6.1 (synchronous allocation management)
- §9.7.18.5 and §9.7.18.7.1 (collective resource effects and optional peer blocking)

Direction: reading

Applies: Actual full warp requests: the completion of an operation (a cta_group::1 record or a
  pairing).

Premises: Every earlier request has valid actual participants; WarpRequest.Before orders every lane
  of the same warp.

Effect: CompletionClosed is a Consistent field enforcing resource completion prefixes. Peer-wait
  choices and MustWait remain unchanged; source advancement alone is not completion. No memory
  visibility, access-completion or final drain conclusion is asserted.

Review: The per-warp order of performed requests is `recorded_of_before` in
  `Lemmas/Tmem/TmemPairHistory.lean`. That a CTA's allocator performs a request of a warp only after
  the earlier requests of that warp is not a separate rule: an earlier request has returned, so
  DEP-TMEM-ALLOC-WAIT requires it to be performed. Completion is not implied the same way: a
  cta_group::2 request that did not wait for its peer may return before its pairing.
-/

/-- Every earlier actual request of a warp of an operation is covered. -/
def CompletionReady (L : Launch) (X : Execution) (ws : List WarpRequest) : Prop :=
  ∀ w ∈ ws, ∀ w' group, w'.Valid L X group → w'.Before w → ∀ i, Participates L w' i → Covered L X i

/-- Every complete operation of the execution satisfies `CompletionReady`. -/
def CompletionClosed (L : Launch) (X : Execution) : Prop :=
  ∀ ws, Completed X ws → CompletionReady L X ws

end
end PTX.Tmem.Pair
