-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.QueryCorrectionStaging
import Kernels.TmlFa4Fwd.Proof.Thread.WaitMode
import Lemmas.Order.GuardObserver

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy

private def AsyncSourcePath (l : Launch) (X : Execution) (loc : Loc)
    (input : EvId) (part : Part) : Ref → Prop
  | .thread writer => ∀ {issue nextPart}, baseCausality l X writer issue →
      AsyncCovers X issue nextPart loc → AsyncChain l X loc (input, part) (issue, nextPart)
  | .async issue nextPart => AsyncChain l X loc (input, part) (issue, nextPart)

private theorem asyncSourcePath {l : Launch} {m : Mem0} {X : Execution} {loc : Loc}
    (hX : Consistent l kernel Assumptions.all m X) {src dst : Ref}
    (hOrder : ByteCausality l X loc src dst) :
    ∀ {input slot}, src = .async input (.write slot) →
      AsyncSourcePath l X loc input (.write slot) dst := by
  induction hOrder with
  | @direct dst order =>
    rintro input slot rfl
    cases dst with
    | thread writer =>
      intro issue nextPart hLater hCovers
      obtain ⟨hInput, wait, hWait, hEarlier⟩ := order
      have hBase := observedCompletionBefore_baseCausality hEarlier
      exact .direct ⟨hInput, hCovers, .inl ⟨wait, hWait, hBase.trans hLater⟩⟩
    | async issue part => exact order.2
  | @commitOperand dst mma wait isB acq index _ _ _ read _ obs hNext hTouches ih =>
    intro input slot hSrc
    obtain ⟨value, hRead⟩ := read
    obtain ⟨scope, hObserved, hScope⟩ := obs
    have hAcq := Thread.completionObservationAcquires hX hObserved
    subst acq
    let access : Acc := {loc, size := 1}
    have hOperand : AsyncCovers X mma (.mmaRead isB index) loc :=
      ⟨access, false, ⟨rfl, rfl, hRead.1⟩, rfl, rfl, le_rfl, Nat.lt_succ_self _⟩
    have hPresent : X.AsyncPresent mma (.mmaRead isB index) := ⟨loc, value, hRead⟩
    have hFinished : AsyncFinished l X mma (.mmaRead isB index) wait :=
      .inr ⟨scope, hObserved, hScope⟩
    have hChain : AsyncChain l X loc (input, .write slot) (mma, .mmaRead isB index) :=
      ih hSrc
    cases dst with
    | thread writer =>
      intro issue nextPart hLater hCovers
      exact hChain.tail hPresent ⟨hOperand, hCovers,
        .inl ⟨wait, hFinished, (Relation.TransGen.single (.inl hNext)).trans hLater⟩⟩
    | async issue part =>
      obtain ⟨footprint, ⟨writes, hIntent⟩ | ⟨_, _, hBad, _⟩, hCovers⟩ := hTouches
      · exact hChain.tail hPresent ⟨hOperand, ⟨footprint, writes, hIntent, hCovers⟩,
          .inl ⟨wait, hFinished, .single (.inl hNext)⟩⟩
      · cases hBad

/-- An asynchronous write ordered to a correction write also precedes the published O
read. Operand handoffs extend the asynchronous chain through the actual tracked read. -/
theorem asyncSourceBeforePublishedRead {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {src writer issue : EvId}
    {slot : Slot} {loc : Loc} {column row byte : Nat}
    (hCta : SameCta l src.1 issue.1)
    (hBefore : ByteCausality l X loc (.async src (.write slot)) (.thread writer))
    (hOutput : modelCausality l X loc (.thread writer)
      (.async issue (.read (.store column row byte)))) :
    modelCausality l X loc (.async src (.write slot))
      (.async issue (.read (.store column row byte))) := by
  obtain ⟨covers, hProxy | ⟨_, hBase⟩⟩ := hOutput
  · obtain ⟨_, _, _, _, _, _, _, hToFence, hToIssue⟩ := hProxy
    exact ⟨.inl hCta, asyncSourcePath hX hBefore rfl (hToFence.trans hToIssue) covers⟩
  · exact ⟨.inl hCta, asyncSourcePath hX hBefore rfl hBase covers⟩

end PTX.Kernels.TmlFa4Fwd.Protocol
