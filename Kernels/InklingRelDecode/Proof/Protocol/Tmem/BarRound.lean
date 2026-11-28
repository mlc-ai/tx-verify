-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.BarRounds
public import Lemmas.Flow.PollRounds
public import Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow

export Softmax.Export (barPos bar_round_facts)

/-- **A rendezvous is not a poll.** -/
public theorem poll_keeps {X : Execution} {g u pc c} {md : BarMode} (key : Nat)
    (get : X.get (g,u) = some ⟨pc,.bar 0 c md⟩) :
    pollRound key ((X.tr g).take (u+1)) = pollRound key ((X.tr g).take u) := by
  have : (X.tr g)[u]? = some ⟨pc,.bar 0 c md⟩ := get
  unfold pollRound
  rw [List.take_add_one, this, List.countP_append]
  simp [okPollAt]

end PTX.Kernels.InklingRelDecode.Proof.Tmem
