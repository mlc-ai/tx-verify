-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Memory.CommitOperandOrder

@[expose] public section

namespace PTX

open AsyncCopy

variable {L : Launch} {X Y : Execution} {loc : Loc}

/-- An operand handoff preserves the originating write of its base path. -/
theorem ByteCausality.starts {src dst : Ref} (h : ByteCausality L X loc src dst) :
    ∃ first, modelCausality L X loc src first := by
  induction h with
  | direct h => exact ⟨_, h⟩
  | commitOperand _ _ _ _ _ _ _ _ ih => exact ih

/-- Transport byte causality by preserving the base paths and the operands and observers of
every handoff. The destination predicate identifies the endpoints retained by the frame. -/
theorem ByteCausality.map {src dst : Ref} (h : ByteCausality L X loc src dst)
    {retained : Ref → Prop} (hdst : retained dst)
    (hbase : ∀ {f}, retained f → modelCausality L X loc src f → modelCausality L Y loc src f)
    (hwrite : ∀ {e a}, (∃ first, modelCausality L Y loc e first) →
      X.Intent e a true → a.Covers loc → Y.Intent e a true)
    (htouch : ∀ {f a}, retained f → X.MemTouches f a → a.Covers loc → Y.MemTouches f a)
    (htrack : ∀ {f mma wait b k acq sc}, retained f → po X wait f.issuer →
      CommitOperandIssue X loc mma b acq f →
      (∃ value, X.MmaRead mma b k loc value) → AsyncObserved X mma .mmaDone wait acq sc →
      retained (.async mma (.mmaRead b k)) ∧ po Y wait f.issuer ∧
      CommitOperandIssue Y loc mma b acq f ∧
      (∃ value, Y.MmaRead mma b k loc value) ∧ AsyncObserved Y mma .mmaDone wait acq sc) :
    ByteCausality L Y loc src dst := by
  revert hbase
  revert hdst
  induction h with
  | direct h => exact fun hdst hbase => .direct (hbase hdst h)
  | commitOperand shared written issued read _ observed next covers ih =>
    intro hdst hbase
    obtain ⟨sc, obs, scope⟩ := observed
    obtain ⟨keepRead, next', issued', read', obs'⟩ := htrack hdst next issued read obs
    obtain ⟨a, intent, hcov⟩ := written
    obtain ⟨b, touch, hcov'⟩ := covers
    have prior := ih keepRead hbase
    exact .commitOperand shared ⟨a, hwrite prior.starts intent hcov, hcov⟩ issued' read' prior
      ⟨sc, obs', scope⟩ next' ⟨b, htouch hdst touch hcov', hcov'⟩

end PTX
