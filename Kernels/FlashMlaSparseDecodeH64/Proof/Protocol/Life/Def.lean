-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Core.Assembly.SharedLifetime
public import Lemmas.Kernel.ExitChain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma

@[expose] public section

/-! # The asynchronous uses of shared memory whose end is the protocols'

Each statement is about the trace of one execution: an operation issued by a lane of CTA `c`
finishes before an exit of `c` once `c` has exited (`SharedFinished`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX

/-- **A tensor load's arrival finishes before its CTA exits** (a gather: the dequant lanes' polls
of `rawReady`; the query load: the poll of `qTma`). -/
def LoadNotified (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i a (s : TensorCopy.Spec), X.TensorIssue i a s → CtaExited L X (i.1 / L.block) →
    SharedFinished L K A X (.async i (.notify .load)) (i.1 / L.block)

/-- **A query load's arrival finishes before its CTA exits** (the MMA lane's tensor loads of the
query tile: the poll of `qTma` at pc 1931 observes them). -/
def QueryNotified (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ g k pc a (s : TensorCopy.Spec), X.get (g, k) = some ⟨pc, .tensorIssue a s⟩ →
    MbarRow.MmaAt L g pc → CtaExited L X (g / L.block) →
    SharedFinished L K A X (.async (g, k) (.notify .load)) (g / L.block)

/-- **A Tensor Core MMA or copy finishes before its CTA exits** (the last `svDone` commit that
warpgroup 0's poll at pc 1184 observes tracks it). -/
def MmaFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i, ((∃ d s acc mask, X.MmaIssue i d s acc mask) ∨ ∃ cp, X.CpIssue i cp) →
    CtaExited L X (i.1 / L.block) → SharedFinished L K A X (.async i .mmaDone) (i.1 / L.block)

/-- **A commit's arrival finishes before its CTA exits.** -/
def CommitFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i s rank m, X.Commit i s → TcCommit.target s rank = some m → CtaExited L X (i.1 / L.block) →
    SharedFinished L K A X (.async i (.tcNotify rank)) (i.1 / L.block)

/-- **A tensor store's source reads finish before its CTA exits.** -/
def StoreFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i a (s : TensorStore.Spec), X.TensorStoreIssue i a s → CtaExited L X (i.1 / L.block) →
    SharedFinished L K A X (.async i .readsDone) (i.1 / L.block)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
