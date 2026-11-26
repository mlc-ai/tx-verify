-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Top.Safety
public import Lemmas.Order.Order

@[expose] public section

/-! # The conflicts at the bytes that are read are ordered

A premise of the progress proof (`Progress.lean`, `reads`): it follows from the safety facts,
which order every conflicting pair of accesses. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The conflicts at the bytes that are read are ordered.** -/
theorem readsOrdered (F : SafetyFacts P L mem0 X) : ReadsOrdered L X :=
  let h := conflictsOrdered F
  ReadsOrdered.of_safe h.no_mixed h.no_race h.strongOrdered

end PTX.Kernels.FlashKdaFwd.Proof.Top
