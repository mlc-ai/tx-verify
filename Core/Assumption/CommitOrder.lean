-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.ClusterScopeMbar
public import Core.Data.Events

@[expose] public section

/-!
# Assumption constructor `commitOrderAt`

A kernel declares the commit-order assumption with `Assumption.commitOrderAt`, naming exactly the
`tcgen05.commit` sites whose mbarrier arrive-on its proof treats as performed before the
arrive-on of the issuing thread's next commit. This file is not itself an assumption.
-/

namespace PTX.Assumption

/-! ## ASM-COMMIT-ORDER — a commit's arrive-on precedes the next commit's, at named sites
Statement: At the `tcgen05.commit` sites a kernel names, the model trusts that the commit's mbarrier
  arrive-on at each target CTA completes before the arrive-on of the issuing thread's next commit at
  that CTA starts. A kernel that waits for the mbarrier signal of each such commit does not need
  this assumption.

Defs: Assumption.commitPerformedAt, Assumption.commitOrderAt

Source:
- §9.7.18.12.1: "Makes the mbarrier object track the completion of all prior async-tcgen05
    operations initiated by the executing thread."
- ERR-SHARED-LIFETIME

Direction: trust

Effect: `commitOrderAt name sites why` selects, at exactly the sites (`pc`) in `sites`, the hook
  `commitInOrder` (ASM-INTERFACE). The arrive-on of a commit at a selected site, at each target
  rank, completes before the arrive-on at the same rank of the issuing thread's next commit starts.
  The edge is part of the lifetime order only (ERR-SHARED-LIFETIME `LifetimeStep`): a proof that the
  next arrive-on completes before an exit then shows the same of this one. The same hardware order
  makes a selected commit's arrive-on performed at a rank whenever the next commit's arrive-on at
  that rank is. The assumption's `wf` is that constraint (`commitPerformedAt`), and it removes
  the executions in which the next commit's arrive-on is performed while the selected one's never
  is. A kernel whose proof of progress builds executions must show the constraint of the
  executions it builds. The constructor sets no `ub`. The statement is generated from the sites
  and lists every site it covers.

Review: A `tcgen05.commit` signals its mbarrier once the operations it tracks have completed. The
  text orders nothing between the arrive-ons of two commits of one thread, since a commit is not
  one of the operations a later commit tracks. Code that drains only its last commit relies on the
  hardware performing one thread's commits in issue order: CUTLASS's producer tail, and
  FlashAttention-4's last Q-empty commit, which no thread observes.
-/

/-- At the commit sites `sites`: when the arrive-on at rank `r` of the issuing thread's next
commit is performed, so is the selected commit's at rank `r`. -/
def commitPerformedAt (sites : List Nat) (X : Execution) : Prop :=
  ∀ (g j j' pc : Nat) (sp : TcCommit.Spec) (r : Fin 16),
    X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → sites.contains pc = true →
    j < j' → (∃ s, X.Commit (g, j') s) → (∀ k, j < k → k < j' → ¬ ∃ s, X.Commit (g, k) s) →
    r ∈ X.tcNotified (g, j') → r ∈ X.tcNotified (g, j)

/-- The arrive-on of the commits at exactly `sites` precedes the arrive-on, at the same rank,
of the issuing thread's next commit; `why` says why the kernel needs it. -/
def commitOrderAt (name : String) (sites : List Nat) (why : String) : Assumption where
  name := name
  statement := s!"The mbarrier arrive-on of a tcgen05.commit, at each target rank, is performed \
    before the arrive-on at the same rank of the issuing thread's next tcgen05.commit (one \
    thread's commits signal in issue order), and is performed whenever that next arrive-on is, \
    at exactly these sites: {siteText sites}. {why}"
  commitInOrder pc := sites.contains pc
  wf _ _ X := commitPerformedAt sites X

end PTX.Assumption
