-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings

@[expose] public section

/-! # What the thread layer exports for the barrier initializations

Each table barrier is initialized in the prologue by the elected lane of one warp
(`FBar.initWarp`): warp 12's for the handshake barrier, warp 0's for the others. The fields are
facts of single threads (`InitFacts`), from the prologue's run invariant (`Prologue.Run`) and the
commit sites:

* an initialization follows a full-mask election that returned the thread's lane, and is the
  thread's only one of its barrier (`init`);
* a thread that reaches its cluster arrival initialized, before it, every barrier of its warp,
  unless a full-mask election before it returned another lane (`init_done`);
* every target of a Tensor Core commit is a barrier of the issuer's cluster (`commit_cluster`:
  the commit's specification resolves over the issuer's cluster of two, THREAD-TC-COMMIT-TARGETS).

Which barrier an initialization names, with which count, and that it is fenced before the
cluster arrival, are `ClusterFacts.init_site` and `ClusterFacts.fence`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The warp whose elected lane initializes the barrier. -/
def FBar.initWarp (b : FBar) : Nat := if b = .dealloc then 12 else 0

/-- The thread layer's facts for the barrier initializations. -/
structure InitFacts (L : Launch) (X : Execution) : Prop where
  /-- An initialization is an elected lane's, its thread's only one of the barrier. -/
  init : ∀ {g k pc n : Nat} {m : Loc}, g < L.threads → X.get (g, k) = some ⟨pc, .mbInit m n⟩ →
    LeadAt L X g k ∧ ∀ k' pc' n', X.get (g, k') = some ⟨pc', .mbInit m n'⟩ → k' = k
  /-- A thread that reaches its cluster arrival initialized every barrier of its warp before it,
  unless a full-mask election before it returned another lane. -/
  init_done : ∀ {g : Nat}, g < L.threads → clFirst X g < (X.tr g).length →
    (∀ b : FBar, b.initWarp = warpOf L g → ∃ k < clFirst X g, ∃ pc n,
      X.get (g, k) = some ⟨pc, .mbInit (b.loc L (ctaOf L g)) n⟩) ∨
    ∃ k < clFirst X g, ∃ pc inst l, X.Elect (g, k) pc 4294967295 inst l ∧ l ≠ laneOf L g
  /-- Every target of a commit is a barrier of the issuer's cluster. -/
  commit_cluster : ∀ {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {r : Fin 16} {m : Loc},
    X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some m →
      m.cta / 2 = ctaOf L i.1 / 2

end
end PTX.Kernels.FlashAttn4Fwd.Proof
