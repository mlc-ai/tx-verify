-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.SharedLifetime
public import Core.MBarrier.InitPublication

@[expose] public section

namespace PTX
noncomputable section

/-! ## ERR-TC-COMMIT-GROUP — the issuing CTA group exists
Statement: An execution is unsafe when a CTA of the CTA group that issues a `tcgen05.commit` does
  not exist in the cluster.

Defs: TcCommitIssueSafe, TcCommitUnsafe

Source:
- §9.7.18.5 (issue granularity)

Direction: stricter

Applies: Every `tcgen05.commit`, either cta_group, whatever its target mask

Premises: Every CTA of the issuer's CTA group exists.

Effect: Safety rejection. The issuing CTA group must exist whatever the target mask. The lifetimes
  of the target CTAs (each arrival is a use of its mbarrier's CTA) and of the CTA group (the issue
  is a use of each of its CTAs) are ERR-SHARED-LIFETIME. Every target is an mbarrier operand of the
  commit (`UsesMbar`): its initialization is ERR-MBAR-UNINITIALIZED and its storage
  ERR-UNALLOCATED-ACCESS. Once delivered, ObjectPublished and the checked object history select the
  exact initialized lifetime and phase.
-/
/-- The issuing CTA group is independent of the target set: even an empty mask or a
mask targeting another group must satisfy the cta_group issue granularity. -/
def TcCommitIssueSafe (L : Launch) (issue : EvId) (s : TcCommit.Spec) : Prop :=
  issue.1 < L.threads ∧ TcCommit.resolve L s.group (issue.1 / L.block) s.mbar s.mask = some s ∧
    L.ctaGroup (issue.1 / L.block) s.group ≠ none

/-- A commit has an issuing CTA group that does not exist in the cluster. -/
def TcCommitUnsafe (L : Launch) (X : Execution) : Prop :=
  ∃ i s, X.Commit i s ∧ ¬ TcCommitIssueSafe L i s

end
end PTX
