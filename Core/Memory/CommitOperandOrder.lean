-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Memory.Order

@[expose] public section

namespace PTX

open AsyncCopy

/-! ## MEM-BYTE-CAUSALITY — byte order used by memory checks
Statement: Byte causality consists of the base proxy and completion paths and the observed
  handoff of a shared operand byte of an MMA or a Tensor Memory copy.

Defs:
  ByteCausality, ByteCausality.direct_iff_of_global, ByteCausality.direct_iff_of_no_operand,
  ByteCausality.direct_iff_of_not_write, CommitOperandIssue, CommitOperandIssue.congr

Source:
- §8.9.5 (base proxy order)
- EXT-TC-COMMIT-OPERAND-ORDER (observed operand handoff)
- EXT-TC-SOURCE-REUSE (observed copy-source overwrite)

Direction: reading

Applies: The memory checks for two accesses to one byte.

Premises: A direct `modelCausality` edge or all premises of the observed operand handoff.

Effect: Supplies the byte order used in read consistency, coherence and safety.
-/

/-!
### EXT-TC-COMMIT-OPERAND-ORDER — an observed commit orders prior writes to its operand bytes
Statement: Observing the completion of an MMA through a tracked commit carries the order of
  writes that precede a shared operand read to the waiting thread's subsequent accesses to the
  same byte.

Source:
- PTX ISA 9.5 §9.7.18.6.4.2, Example 2: "tcgen05.mma [d], ... tcgen05.commit.mbarrier::arrive::one
  mbarrier.try_wait.relaxed.cluster (loop until successful)"
- PTX ISA 9.5 §9.7.18.6.4.2: "For the completion of the asynchronous tcgen05.mma , tcgen05.commit
  is used."
- PTX ISA 9.5 §9.7.18.12.1: "Upon the completion of the tracked asynchronous tcgen05 operations,
  the signal specified by the .completion_mechanism is triggered by the system on the mbarrier
  object."

Why it is not spec text: The example establishes how a thread observes completion. It does not
  give an order across proxies from a writer of an operand through the MMA to a later access
  of that shared byte. The reading lets that access reuse the byte once the read is complete.
  Disclosed by every kernel whose statement names `Op.tcMma` and `Op.tcCommit`: FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.

Direction: reading

Applies: Writes to a shared byte read by an actual MMA, and later ordinary or asynchronous
  accesses to that byte issued by the thread observing the corresponding commit notification.

Premises: The write precedes the actual operand read at this byte. A successful wait in scope
  observes the notification of a commit that tracks the MMA. The wait precedes the later
  access's issue in program order. The two conflicting accesses both cover the byte.

Effect: The write precedes the later access in byte causality for the race, mixed access,
  read source and coherence checks. The rule gives no order to accesses of other bytes and
  does not turn the commit notification into a release.
-/

/-- An MMA qualifies through its actual issue. A copy qualifies for a source overwrite
only when the read is from its shared operand and the completion observation is acquire. -/
def CommitOperandIssue (X : Execution) (loc : Loc) (i : EvId) (isB acquire : Bool)
    (dst : Ref) : Prop :=
  (∃ d operands accum mask, X.MmaIssue i d operands accum mask) ∨
    isB = false ∧ acquire = true ∧ (∃ c, X.CpIssue i c) ∧
      match dst with
      | .thread e => ∃ a bs, X.Writes e a bs ∧ a.Covers loc
      | .async .. => False

theorem CommitOperandIssue.congr {X Y : Execution} {loc : Loc} {i : EvId}
    {isB acquire : Bool} {dst : Ref} (hi : X.get i = Y.get i)
    (hd : X.get dst.issuer = Y.get dst.issuer) :
    CommitOperandIssue X loc i isB acquire dst ↔ CommitOperandIssue Y loc i isB acquire dst := by
  cases dst with
  | thread e =>
    change X.get e = Y.get e at hd
    simp only [CommitOperandIssue, Execution.MmaIssue, Execution.CpIssue, Execution.Writes, hi, hd]
  | async e p =>
    simp only [CommitOperandIssue, Execution.MmaIssue, Execution.CpIssue, hi]

/-- Byte causality consists of the base proxy and completion paths and the observed shared
operand handoff. The handoff may use a preceding handoff to reach the operand read. -/
inductive ByteCausality (L : Launch) (X : Execution) (loc : Loc) : Ref → Ref → Prop
  | direct {src dst : Ref} : modelCausality L X loc src dst → ByteCausality L X loc src dst
  | commitOperand {src dst : Ref} {mma wait : EvId} {isB acquire : Bool} {index : Nat}
      (shared : loc.space = .shared)
      (written : ∃ a, X.Intent src a true ∧ a.Covers loc)
      (issued : CommitOperandIssue X loc mma isB acquire dst)
      (read : ∃ value, X.MmaRead mma isB index loc value)
      (prior : ByteCausality L X loc src (.async mma (.mmaRead isB index)))
      (observed : ∃ scope, AsyncObserved X mma .mmaDone wait acquire scope ∧
        ScopesMeet L .cluster mma.1 scope wait.1)
      (next : po X wait dst.issuer)
      (covers : ∃ a, X.MemTouches dst a ∧ a.Covers loc) :
      ByteCausality L X loc src dst

/-- The extra handoff is confined to shared operand bytes. -/
theorem ByteCausality.direct_iff_of_global {L : Launch} {X : Execution} {loc : Loc}
    {src dst : Ref} (h : loc.space = .global) :
    ByteCausality L X loc src dst ↔ modelCausality L X loc src dst := by
  refine ⟨?_, .direct⟩
  intro order
  cases order with
  | direct order => exact order
  | commitOperand shared => cases h.symm.trans shared

/-- With no MMA or copy issue, only the base proxy and completion paths apply. -/
theorem ByteCausality.direct_iff_of_no_operand {L : Launch} {X : Execution} {loc : Loc}
    {src dst : Ref} (h : ∀ i d s accum mask, ¬ X.MmaIssue i d s accum mask)
    (hc : ∀ i c, ¬ X.CpIssue i c) :
    ByteCausality L X loc src dst ↔ modelCausality L X loc src dst := by
  refine ⟨?_, .direct⟩
  intro order
  cases order with
  | direct order => exact order
  | commitOperand _ _ issued =>
    rcases issued with ⟨d, s, accum, mask, issue⟩ | ⟨_, _, ⟨c, issue⟩, _⟩
    · exact (h _ d s accum mask issue).elim
    · exact (hc _ c issue).elim

/-- An access with no write intent at this byte cannot start an operand handoff. -/
theorem ByteCausality.direct_iff_of_not_write {L : Launch} {X : Execution} {loc : Loc}
    {src dst : Ref} (h : ∀ a, X.Intent src a true → ¬ a.Covers loc) :
    ByteCausality L X loc src dst ↔ modelCausality L X loc src dst := by
  refine ⟨?_, .direct⟩
  intro order
  cases order with
  | direct order => exact order
  | commitOperand _ written =>
    obtain ⟨a, intent, covers⟩ := written
    exact (h a intent covers).elim

end PTX
