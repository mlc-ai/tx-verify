-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.SharedLifetime

@[expose] public section

/-! # The asynchronous uses of shared memory whose end is the channels' -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Life
open PTX

/-- **A CTA's tensor loads (Q and Bias) end before its exit**: the writes of each and its arrival
on the mbarrier of its ring. -/
def LoadsFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i a (s : TensorCopy.Spec), X.TensorIssue i a s → CtaExited L X (i.1 / L.block) →
    (∀ x y k, (TensorTransfer.slotAt s.descriptor x y k).isSome →
      SharedFinished L K A X (.async i (.write (.load x y k))) (i.1 / L.block)) ∧
    SharedFinished L K A X (.async i (.notify .load)) (i.1 / L.block)

/-- **A CTA's bias loads end before its exit**: the arrival on the bias full barrier of each tensor
load that names one (the loads of shared offsets `320`, `328`). -/
def BiasLoadsFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i a (s : TensorCopy.Spec), X.TensorIssue i a s →
    (∃ st < 2, s.mbar = ⟨.shared, i.1 / L.block, L.sharedBase + (320 + 8 * st)⟩) →
    CtaExited L X (i.1 / L.block) →
    SharedFinished L K A X (.async i (.notify .load)) (i.1 / L.block)

/-- **A CTA's row copies (K/V) end before its exit.** -/
def RowsFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i s, X.Copy i s → CtaExited L X (i.1 / L.block) →
    SharedFinished L K A X (.async i (.write .copy)) (i.1 / L.block)

/-- **The arrive-ons of a CTA's row-copy groups (K/V) that have arrived end before its exit.** -/
def ArrivesFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i m noinc, X.AsyncArrive i m noinc → X.AsyncPresent i .arriveOn →
    CtaExited L X (i.1 / L.block) → SharedFinished L K A X (.async i .arriveOn) (i.1 / L.block)

/-- **The arrive-ons of a CTA's commits to the empty barriers (K/V and Q) end before its exit**: the
commits to the barriers at shared offsets other than S-full (`80`, `88`) and final O (`144`,
`152`). -/
def EmptiesFinished (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ i s rank m, X.Commit i s → TcCommit.target s rank = some m →
    (∀ st < 2, m ≠ ⟨.shared, i.1 / L.block, L.sharedBase + (80 + 8 * st)⟩ ∧
      m ≠ ⟨.shared, i.1 / L.block, L.sharedBase + (144 + 8 * st)⟩) →
    CtaExited L X (i.1 / L.block) →
    SharedFinished L K A X (.async i (.tcNotify rank)) (i.1 / L.block)

end PTX.Kernels.TmlFa4Fwd.Proof.Life
