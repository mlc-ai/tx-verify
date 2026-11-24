-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section

/-!
# Rule identifiers

The contract entries that give an instruction family its semantics.
-/

namespace PTX

/-! ## PROG-RULE-ID — the contract ID of the rule of an instruction
Statement: Each instruction family has a function that names the contract entry whose rule gives an
  instruction its semantics, or none when the model has no rule for it, and `Op.rule`
  (PROG-INSTR-RULE) extends it to every instruction. The semantic functions are defined through it
  or proved equal to its case split, so an instruction without a named rule has no semantics.

Defs: RuleId, RuleId.id

Source:
- none (dispatch)

Direction: representation

Applies: Every decoded instruction

Premises: None.

Effect: Selects the rule that `execLocal` (THREAD-LOCAL) or `eventTmpl` (THREAD-RUN) applies; no
  rule selected means `noRule`.
-/

/-- A contract entry that gives instructions their semantics. -/
inductive RuleId where
  | threadInt
  | threadMove
  | threadCvt
  | threadFloat
  | threadCvta
  | threadSharedPointer
  | threadAccess
  | threadAtomic
  | threadPrefetch
  | threadCachePolicy
  | threadNoEffect
  | threadShfl
  | threadVote
  | threadElect
  | threadWarpBar
  | threadRedux
  | threadMatch
  | threadActivemask
  | threadBranch
  | threadTensorMapPrefetch
  | threadBar
  | clusterBarrier
  | threadSetMaxNReg
  | threadTensorIssue
  | threadTensorPrefetch
  | threadTensorStore
  | threadClc
  | threadTma
  | threadCpAsync
  | threadAsyncStore
  | threadTcCommit
  | threadTc
  | threadRun
  | threadSreg
  | threadMatrix
  | threadMma
  | threadFence
  deriving DecidableEq, Repr

/-- The contract ID of a rule. -/
def RuleId.id : RuleId → String
  | .threadInt => "THREAD-INT"
  | .threadMove => "THREAD-MOVE"
  | .threadCvt => "THREAD-CVT"
  | .threadFloat => "THREAD-FLOAT"
  | .threadCvta => "THREAD-CVTA"
  | .threadSharedPointer => "THREAD-SHARED-POINTER"
  | .threadAccess => "THREAD-ACCESS"
  | .threadAtomic => "THREAD-ATOMIC"
  | .threadPrefetch => "THREAD-PREFETCH"
  | .threadCachePolicy => "THREAD-CACHE-POLICY"
  | .threadNoEffect => "THREAD-NO-EFFECT"
  | .threadShfl => "THREAD-SHFL"
  | .threadVote => "THREAD-VOTE"
  | .threadElect => "THREAD-ELECT"
  | .threadWarpBar => "THREAD-WARP-BAR"
  | .threadRedux => "THREAD-REDUX"
  | .threadMatch => "THREAD-MATCH"
  | .threadActivemask => "THREAD-ACTIVEMASK"
  | .threadBranch => "THREAD-BRANCH"
  | .threadTensorMapPrefetch => "THREAD-TENSORMAP-PREFETCH"
  | .threadBar => "THREAD-BAR"
  | .clusterBarrier => "OBJ-CLUSTER-BARRIER-SYNC"
  | .threadSetMaxNReg => "THREAD-SETMAXNREG"
  | .threadTensorIssue => "THREAD-TENSOR-ISSUE"
  | .threadTensorPrefetch => "THREAD-TENSOR-PREFETCH"
  | .threadTensorStore => "THREAD-TENSOR-STORE"
  | .threadClc => "THREAD-CLC-QUERY"
  | .threadTma => "THREAD-TMA"
  | .threadCpAsync => "THREAD-CP-ASYNC"
  | .threadAsyncStore => "THREAD-ASYNC-STORE"
  | .threadTcCommit => "THREAD-TC-COMMIT"
  | .threadTc => "THREAD-TC"
  | .threadRun => "THREAD-RUN"
  | .threadSreg => "THREAD-SREG"
  | .threadMatrix => "THREAD-MATRIX"
  | .threadMma => "THREAD-MMA-SYNC"
  | .threadFence => "THREAD-FENCE"

end PTX
