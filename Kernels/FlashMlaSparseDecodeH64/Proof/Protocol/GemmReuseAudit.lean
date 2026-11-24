-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Memory.CommitOperandOrder

@[expose] public section

/-! # Query-copy byte reuse -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX AsyncCopy

/-- The forward byte order needed when dequantization reuses the query copy's source. -/
def QueryTileReuseOrdered (L : Launch) (X : Execution) (read write : EvId)
    (index : Nat) (byte : Loc) : Prop :=
  ByteCausality L X byte (.async read (.mmaRead false index)) (.thread write)

/-- The actual copy and first tile write access a common byte. The acquire observes the
copy's read, and the write is later than the acquire in base causality. -/
def QueryTileReuseObserved (L : Launch) (X : Execution) (read wait write : EvId)
    (index : Nat) (byte : Loc) : Prop :=
  (∃ sp, X.CpIssue read sp) ∧ X.MmaFootprint read false index byte ∧
    (∃ a bs, X.Writes write a bs ∧ a.Covers byte ∧ a.size = 16) ∧
    AsyncFinished L X read (.mmaRead false index) wait ∧ baseCausality L X wait write

/-- The forward order from the read is through an observed completion. Its continuation
can use the proxy path or the tensor-memory copy's shared source reuse rule. -/
theorem query_reuse_order_iff_completion (L : Launch) (X : Execution) (read write : EvId)
    (index : Nat) (byte : Loc) :
    QueryTileReuseOrdered L X read write index byte ↔
      AsyncCovers X read (.mmaRead false index) byte ∧
        ∃ wait, AsyncFinished L X read (.mmaRead false index) wait ∧
          ObservedCompletionBefore L X byte read (.mmaRead false index) wait write := by
  apply ByteCausality.direct_iff_of_not_write
  intro a hi
  exact Bool.noConfusion hi.1

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
