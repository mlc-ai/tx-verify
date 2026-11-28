-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Softmax.PollStep

/-! # An event that is not a score poll keeps the lane's round -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow

/-- **An event of another pc leaves the count of successful score polls unchanged.** -/
public theorem poll_keep {X : Execution} {g k : Nat} {ev : Event} (he : X.get (g, k) = some ev)
    (ne : ev.pc ≠ 1257) :
    pollRound 1257 ((X.tr g).take (k + 1)) = pollRound 1257 ((X.tr g).take k) :=
  poll_same he ne

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
