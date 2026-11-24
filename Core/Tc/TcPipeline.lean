-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcFence

@[expose] public section

namespace PTX.TcMma
noncomputable section

/-! ## DEP-TC-PIPELINE — the pipelined pairs of tcgen05 operations
Statement: Two asynchronous tcgen05 operations of one warp access Tensor Memory in issue order
  without a completion wait only when they form one of the pipelined pairs of §9.7.18.6.2, and then
  only for the operands that the pair names. The represented pairs are the MMA and copy rows of the
  table and its three rows of `tcgen05.st` and `tcgen05.ld`.

Defs: TcMma.SameAccumulator, TcMma.PipeAccess, TcMma.Pipelined, TcMma.pipelined_cRead_dWrite,
  TcMma.pipelined_dWrite_cRead

Source:
- §9.7.18.6.2: "However, some specific pairs of the asynchronous tcgen05 instructions from the same
    warp form tcgen05 pipelines, where in the two asynchronous operations are guaranteed to access
    certain operands in tensor memory in the same order as the instructions that issued them."
- §9.7.18.6.2: "tcgen05.mma.cta_group::N (A and metadata reads) -> tcgen05.mma.cta_group::N (D
    writes) (same N)"
- §9.7.18.6.2: "tcgen05.mma.cta_group::N (A and metadata reads) -> tcgen05.cp.cta_group::N (writes)
    (same N)"
- §9.7.18.6.2: "tcgen05.mma.cta_group::N (C reads) -> tcgen05.mma.cta_group::N (D writes) (same N
    and accumulator address and shape)"
- §9.7.18.6.2: "tcgen05.mma.cta_group::N (D writes) -> tcgen05.mma.cta_group::N (C reads) (same N
    and accumulator address and shape)"
- §9.7.18.6.2: "tcgen05.mma.cta_group::N (D writes) -> tcgen05.mma.cta_group::N (D writes) (same N
    and accumulator address and shape)"
- §9.7.18.6.2: "tcgen05.cp.<not .4x256b>.cta_group::N (writes) -> tcgen05.mma.cta_group::N (A and
    metadata reads) (same N and address)"
- §9.7.18.6.2: "tcgen05.st.sync.aligned -> tcgen05.ld.sync.aligned tcgen05.st.sync.aligned ->
    tcgen05.st.sync.aligned tcgen05.ld.sync.aligned -> tcgen05.st.sync.aligned"
- §9.7.18.6.2: "Instructions issued by different warps are always non-pipelined."
- §9.7.18.6.3: "The asynchronous tcgen05 instructions that are ordered across threads in the same
    warp also form a tcgen05 pipeline."
- DEP-TC-FENCE
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER

Direction: reading

Applies: Represented MMAs of either CTA group and kind, `tcgen05.cp`, `tcgen05.ld` and
  `tcgen05.st`

Premises: Each pair requires the same warp, issue ordered by `TcBefore` (program order, a fenced
  chain, or EXT-TCACQUIRE) and the row's condition. The C/D rows require an equal accumulator
  address and shape (M, N) on the same physical CTAs. The A-read rows require an A operand in Tensor
  Memory. The copy→A-read row requires the copy's address as the A operand, and it excludes
  `.4x256b` copies. The rows of `tcgen05.st` and `tcgen05.ld` have no further condition. The table's
  same-N condition (the CTA group) holds by PROG-TC-CTA-GROUP.

Effect: `Pipelined` is the only statement of the table in the model. The write order
  (DEP-TC-READ-SOURCE, DEP-TMEM-STORE-VALUE), the read sources (DEP-TC-READ-SOURCE), the conflict
  check (ERR-TMEM-RACE) and the completion order (DEP-TC-COMPLETION-CLOSURE) use it. The direction
  is `reading` because the issue order rests on named readings: EXT-TCACQUIRE and, through the
  fenced chains of DEP-TC-FENCE, EXT-TC-EXEC-ORDER.

Review: The rows with `tcgen05.shift`, and the row of a `.4x256b` copy before an A read, are not
  represented. Such a pair is ordered only by completion (DEP-TMEM-SHIFT-VALUE), which only rejects
  programs. Metadata is not decoded.
-/

/-- Two MMAs use the same accumulator: equal D address, M and N, on the same CTAs. -/
def SameAccumulator (d : Nat) (s : OperandSpec) (d' : Nat) (s' : OperandSpec) : Prop :=
  d = d' ∧ s.descriptor.m = s'.descriptor.m ∧ s.descriptor.n = s'.descriptor.n ∧
    s.lowCta = s'.lowCta ∧ s.highCta = s'.highCta

/-- The Tensor Memory accesses that the rows of the pipeline table name: the A, C reads and D
writes of an MMA, the writes of a copy, and the writes of a store and reads of a load. -/
inductive PipeAccess where
  | aRead | cRead | dWrite | cpWrite | stWrite | ldRead
  deriving DecidableEq, Repr

/-- The pipelined pairs of §9.7.18.6.2: the access `cx` of the operation issued at `x` precedes
the access `cy` of the one issued at `y`. Each arm is one row of the table; a pipeline orders only
these Tensor Memory accesses, not the shared operands. -/
def Pipelined (L : Launch) (X : Execution) : PipeAccess → EvId → PipeAccess → EvId → Prop
  | .aRead, x, .dWrite, y => SameWarp L x.1 y.1 ∧ TcBefore L X x y ∧
    (∃ d s accum mask, X.MmaIssue x d s accum mask ∧ s.aTmem.isSome) ∧
    ∃ d s accum mask, X.MmaIssue y d s accum mask
  | .aRead, x, .cpWrite, y => SameWarp L x.1 y.1 ∧ TcBefore L X x y ∧
    (∃ d s accum mask, X.MmaIssue x d s accum mask ∧ s.aTmem.isSome) ∧
    ∃ c, X.CpIssue y c
  | .cRead, x, .dWrite, y | .dWrite, x, .cRead, y | .dWrite, x, .dWrite, y =>
    SameWarp L x.1 y.1 ∧ TcBefore L X x y ∧ ∃ d s accum mask d' s' accum' mask',
      X.MmaIssue x d s accum mask ∧ X.MmaIssue y d' s' accum' mask' ∧ SameAccumulator d s d' s'
  | .cpWrite, x, .aRead, y => SameWarp L x.1 y.1 ∧ TcBefore L X x y ∧
    ∃ c d s accum mask, X.CpIssue x c ∧ c.shape ≠ .s4x256b ∧
      X.MmaIssue y d s accum mask ∧ s.aTmem = some c.address
  | .stWrite, x, .ldRead, y => SameWarp L x.1 y.1 ∧ TcBefore L X x y ∧
    (∃ address vals shape, X.TSt x address vals shape) ∧
      ∃ address vals shape, X.TLd y address vals shape
  | .stWrite, x, .stWrite, y => SameWarp L x.1 y.1 ∧ TcBefore L X x y ∧
    (∃ address vals shape, X.TSt x address vals shape) ∧
      ∃ address vals shape, X.TSt y address vals shape
  | .ldRead, x, .stWrite, y => SameWarp L x.1 y.1 ∧ TcBefore L X x y ∧
    (∃ address vals shape, X.TLd x address vals shape) ∧
      ∃ address vals shape, X.TSt y address vals shape
  | _, _, _, _ => False

/-- The C-read→D-write row has the condition of the D-write→D-write row. -/
theorem pipelined_cRead_dWrite (L : Launch) (X : Execution) (x y : EvId) :
    Pipelined L X .cRead x .dWrite y = Pipelined L X .dWrite x .dWrite y := rfl

/-- The D-write→C-read row has the condition of the D-write→D-write row. -/
theorem pipelined_dWrite_cRead (L : Launch) (X : Execution) (x y : EvId) :
    Pipelined L X .dWrite x .cRead y = Pipelined L X .dWrite x .dWrite y := rfl

end
end PTX.TcMma
