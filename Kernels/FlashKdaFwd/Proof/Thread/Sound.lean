-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Thread.Start
public import Kernels.FlashKdaFwd.Proof.Thread.StepAt

@[expose] public section

/-! # The thread machine is sound

Every state of the thread machine meets its step obligation (`StepAt.lean`: all 836 sites, 901
states with the second events of `ldmatrix`/`stmatrix` and the elements of the vector load), and
a launched thread reaches the machine's first state (`Start.lean`). Both need the launch facts
`Launched L` only (five scalar parameters and the two parameter objects the code reads), which
the specification's precondition gives (`Launched.of_pre`).

Nothing else of the precondition is used, and nothing about the thread: where an instruction
asks more (a `cvta.shared.u64` of a thread that is not launched, a shared pointer moved out of
its range, bytes that do not rebuild), the machine's transition says that the thread is dead,
which is what Core does. The bound `g < L.threads` is a hypothesis of `start` that its proof
does not use; it is kept in the statements so that they do not change if it becomes needed. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

/-- **Soundness from the launch facts.** -/
theorem sound_of_launched (hL : Launched L) (hg : g < L.threads) : (code L g).Sound where
  start := start hL hg
  steps := fun d => stepAt hL d

/-- **The thread machine of every thread of a launch that meets the specification's
precondition is sound.** -/
theorem sound {P : Params} {mem0 : Mem0} (hpre : Pre P L mem0) (hg : g < L.threads) :
    (code L g).Sound :=
  sound_of_launched (Launched.of_pre hpre) hg

end PTX.Kernels.FlashKdaFwd.Proof.Thread
