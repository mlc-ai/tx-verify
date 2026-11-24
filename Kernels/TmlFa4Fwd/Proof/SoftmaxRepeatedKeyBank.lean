-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedQkBank
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringKeyFrame
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringKeyReadyWords
import Kernels.TmlFa4Fwd.Proof.Protocol.CacheSourceBytes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma PTX.AsyncCopy Thread Thread.Scores Thread.Loader
open Protocol.LoaderReady
open Loader (kvUseStage)
open Mma (qkPc qkFragment kvStart sharedDescriptor recurringKeyBlock qkByteIndex)

/-- The ready-use cursor is constant across the consecutive fragments of a score bank. -/
def ScoreQkBank.keyUse {l : Launch} {X : Execution} {load : EvId} {cell : Cell}
    {stage : Fin 2} (bank : ScoreQkBank l X load cell stage) : Nat :=
  let d := Thread.Mma.atPrefix l X bank.seen.commit.1 bank.start
  d.kvAcquires 0+d.kvAcquires 1+d.kvAcquires 2-1

theorem ScoreQkBank.keyUseAtFragment {l : Launch} {X : Execution}
    {load : EvId} {cell : Cell} {stage : Fin 2} (bank : ScoreQkBank l X load cell stage)
    (j : Nat) (hj : j ≤ 8) :
    let d := Thread.Mma.atPrefix l X bank.seen.commit.1 (bank.start+j)
    d.kvAcquires 0+d.kvAcquires 1+d.kvAcquires 2-1 = bank.keyUse := by
  induction j with
  | zero => rfl
  | succ j ih =>
    obtain ⟨_,_,_,_,hIssue,_⟩ := bank.fragments ⟨j,by omega⟩
    dsimp only
    rw [← Nat.add_assoc, Thread.Mma.prefixStep hIssue.decoded]
    exact ih (by omega)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

theorem ScoreQkBank.recurringBlock (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {load : EvId} {cell : Cell} {stage : Fin 2} (bank : ScoreQkBank l X load cell stage)
    (hPositive : 0 < scoreCommitOrdinal l X (load.1/l.block) stage bank.seen.commit) (step : Fin 8)
    {d : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : QkInstruction X (bank.seen.commit.1,bank.start+step.val) bank.block
      step d op accum mask) :
    bank.block = recurringKeyBlock stage := by
  have hScore : ScoreCommit l X (bank.seen.commit.1,bank.seen.commit.2)
      (load.1/l.block) stage bank.seen.spec bank.seen.rank := bank.seen.score
  obtain ⟨start,hIndex,hBank⟩ := hScore.recurringCacheBankOccurrence hp hX hPositive
  have hStart : start = bank.start := by have := bank.position; omega
  subst start
  obtain ⟨_,_,_,_,hOther,_⟩ := hBank step
  have hPc := congrArg Event.pc (Option.some.inj (hIssue.decoded.symm.trans hOther.decoded))
  change qkPc bank.block+step.val = qkPc (recurringKeyBlock stage)+step.val at hPc
  have hInject : Function.Injective qkPc := by
    intro a b he
    fin_cases a <;> fin_cases b <;> first | rfl | cases he
  exact hInject (Nat.add_right_cancel hPc)

/-- The repeatedly observed score bank has the key descriptor of one actual ring use
on every fragment. Its logical key row can then be recovered from that ready generation. -/
theorem ScoreQkBank.recurringKeyDescriptors (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {load : EvId} {cell : Cell} {stage : Fin 2}
    (bank : ScoreQkBank l X load cell stage)
    (hPositive : 0 < scoreCommitOrdinal l X (load.1/l.block) stage bank.seen.commit) (step : Fin 8)
    {d : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : QkInstruction X (bank.seen.commit.1,bank.start+step.val) bank.block
      step d op accum mask) :
    op.b = sharedDescriptor (kvStart l bank.keyUse+qkFragment step) 16 := by
  have hBlock := bank.recurringBlock hp hX hPositive step hIssue
  rw [hBlock] at hIssue
  have hDesc := hIssue.recurringKeyOperandOfReadyUse hp hX stage
  dsimp only at hDesc
  rw [bank.keyUseAtFragment step.val (by have := step.isLt; omega)] at hDesc
  exact hDesc

end PTX.Kernels.TmlFa4Fwd.Softmax
