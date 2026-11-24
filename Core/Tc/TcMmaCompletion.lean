-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaSafety

@[expose] public section

namespace PTX.TcMma
noncomputable section

/-! ## DEP-TC-COMPLETION-CLOSURE — identical-footprint D-write completion closure
Statement: When two MMAs issued in program order by one thread form a pipelined pair on the same
  accumulator and write the same nonempty set of cells, the later one has completed its Tensor
  Memory writes only if the earlier one has.

Defs: TcMma.SameWrites, TcMma.CompletionPrecedes, TcMma.CompletionClosed

Source:
- §9.7.18.6.2: "The asynchronous tcgen05 operations may execute and complete in a different order
    than they were issued. However, some specific pairs of the asynchronous tcgen05 instructions
    from the same warp form tcgen05 pipelines, where in the two asynchronous operations are
    guaranteed to access certain operands in tensor memory in the same order as the instructions
    that issued them."
- §9.7.18.6.2: "tcgen05.mma.cta_group::N (D writes) -> tcgen05.mma.cta_group::N (D writes) (same N
    and accumulator address and shape)"
- §9.7.18.6.4.1 (pipelined instructions, same thread)
- DEP-TC-PIPELINE

Direction: reading

Applies: Pairs of the D→D pipeline (`Pipelined … .dWrite … .dWrite`) issued by one thread in program
  order whose Tensor Memory write footprints are the same nonempty set of cells.

Premises: `Pipelined L X .dWrite i .dWrite j` (same warp, `TcBefore`, equal accumulator address, M,
  N and physical CTAs); `i` and `j` are the same thread with `i` earlier; `SameWrites`: the two
  `writeCell` mappings agree on every row and column and write at least one cell.

Effect: CompletionClosed constrains asynchronous completion effects in Consistent. The completion of
  an operation extends a closed execution when all its qualifying predecessors are done. The text
  orders the D writes of the pair. With one footprint, the later operation writes every cell that
  the earlier one writes, after it, and this is the reading. `mmaDone` means that all Tensor Memory
  writes of the MMA have completed.
-/

/-- The D-write footprints of MMAs `i` and `j` are the same nonempty set of cells. -/
def SameWrites (X : Execution) (i j : EvId) : Prop :=
  ∃ d s a mask d' s' a' mask', X.MmaIssue i d s a mask ∧ X.MmaIssue j d' s' a' mask' ∧
    (∀ row col, writeCell s d mask row col = writeCell s' d' mask' row col) ∧
    ∃ row col cell, writeCell s d mask row col = some cell

/-- A D→D pipelined pair of one thread, in program order, with one write footprint. -/
def CompletionPrecedes (L : Launch) (X : Execution) (i j : EvId) : Prop :=
  i.1 = j.1 ∧ i.2 < j.2 ∧ Pipelined L X .dWrite i .dWrite j ∧ SameWrites X i j

/-- A later completed D write cannot precede a missing identical earlier D write.
No implication about mmaStarted is asserted. -/
def CompletionClosed (L : Launch) (X : Execution) : Prop :=
  ∀i j,CompletionPrecedes L X i j → X.async.mmaDone j=true → X.async.mmaDone i=true

end
end PTX.TcMma
