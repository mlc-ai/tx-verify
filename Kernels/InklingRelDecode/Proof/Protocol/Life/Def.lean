-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Core.Assembly.SharedLifetime
public import Lemmas.Kernel.ExitChain
public import Kernels.InklingRelDecode.Spec

@[expose] public section

/-! # The asynchronous uses of shared memory whose end is the protocols'

Each statement is about the trace of one execution: an operation issued by a lane of CTA `c`
finishes before an exit of `c` once `c` has exited (`SharedFinished`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
open PTX

/-- **A tensor load's arrival finishes before its CTA exits** (observed by a poll of `kv_ready`). -/
def LoadNotified (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i a (s : TensorCopy.Spec), X.TensorIssue i a s → CtaExited L X (i.1 / L.block) →
    SharedFinished L K A X (.async i (.notify .load)) (i.1 / L.block)

/-- **A Tensor Core MMA finishes before its CTA exits** (the final commit tracks it and the
epilogue's poll of `o_final` observes it). -/
def MmaFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i d s acc mask, X.MmaIssue i d s acc mask → CtaExited L X (i.1 / L.block) →
    SharedFinished L K A X (.async i .mmaDone) (i.1 / L.block)

/-- **A commit's arrive-on finishes before its CTA exits.** -/
def CommitFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i s rank m, X.Commit i s → TcCommit.target s rank = some m → CtaExited L X (i.1 / L.block) →
    SharedFinished L K A X (.async i (.tcNotify rank)) (i.1 / L.block)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
