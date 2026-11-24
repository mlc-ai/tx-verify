-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution

@[expose] public section

/-!
# The progress contract for runs

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## CORRECT-FAIR — fair runs
Statement: A run is a sequence of possible executions, each extending the previous one. A run is
  fair when, whenever its current execution can be extended by a counted event (any event except a
  failed poll), a later execution of the run has more counted events.

Defs: FairRun

Source:
- CUDA C++ Programming Guide (forward progress)
- EXT-FAIR

Direction: reading

Applies: Sequences of consistent executions

Premises: Prefixes and existing read sources are preserved; whenever a counted extension exists, a
  later member has more counted events.

Effect: Assumption on runs; failed polls are uncounted. A run is a sequence of possible executions,
  each extending the previous one. It is fair if, whenever its current execution can be extended by
  a counted event (any event except a failed `try_wait`), the run later has more counted events than
  it has now. A thread that can make progress eventually does, and a thread does not poll forever
  while a completed phase could be observed. This is the Lean form of EXT-FAIR;
  `Correct.exits` proves that every fair run of a correct kernel reaches an execution where launched
  threads have exited, canceled clusters are accounted for, and async work is drained.

### EXT-FAIR — fair scheduling, including asynchronous completion and observation

Statement: The model assumes that every real run is fair in the sense of CORRECT-FAIR: when the
  current execution can be extended by a counted event, the run later gains counted events. The
  counted events include the completion of an asynchronous operation and a successful observation
  (`FairRun` does not distinguish a thread's event from an asynchronous stage), so when only the
  completion of an asynchronous copy or a successful observation remains available, it eventually
  happens. Failed polls may repeat any number of times, and the run still gains counted events.

Evidence: CUDA C++ Programming Guide, CUDA C++ Execution Model (forward progress). PTX ISA
  §9.7.10.28.4.1 and §9.7.15.16 describe completion and waiting; the eventual-progress condition for
  asynchronous operations is an accepted external contract.

Review: `Correct.exits` in `Lemmas/Kernel/Correct.lean` derives completion from this contract and
  Correct.

Direction: reading

Effect: The accepted scheduling contract is CORRECT-FAIR: a run with an available counted extension
  eventually gains counted events. It is a progress condition on the whole sequence of consistent
  executions, and it promises nothing to any single thread. For the supported bulk-copy protocol,
  the hardware contract must justify eventual counted progress when only copy completion or
  successful observation remains available. `FairRun` excludes staying at the same counted size
  forever when an extension exists. The model's `Consistent` executions are unaffected; if a real
  run is not a `FairRun`, because a thread that can progress never does or because a copy
  completion or a successful observation stays unavailable forever, the completion and termination
  results (`Correct.exits`) do not transfer to it, while the safety results still hold. Disclosed by
  every kernel: AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd, FlashMlaSparseDecodeH64,
  Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.
-/


/-- The run `Xs` is fair (CORRECT-FAIR): every member is possible, each extends the previous one,
and whenever a member can be extended by a counted event, a later member has more counted
events. -/
def FairRun (K : Kernel) (A : List Assumption) (mem0 : Mem0) (Xs : Nat → Execution) : Prop :=
  (∀ n, Consistent L K A mem0 (Xs n)) ∧ (∀ n, (Xs n).le (Xs (n + 1))) ∧
  ∀ n, (∃ Y, Consistent L K A mem0 Y ∧ (Xs n).le Y ∧ (Xs n).size L < Y.size L) →
    ∃ k, (Xs n).size L < (Xs k).size L

end

end PTX
