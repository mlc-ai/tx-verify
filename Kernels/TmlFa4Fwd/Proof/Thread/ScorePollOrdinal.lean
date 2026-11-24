-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxProbabilityGate
import Kernels.TmlFa4Fwd.Proof.PollSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy Prologue

/-- A softmax probability credit depends on every score return through the
credit's local ordinal, including the earliest one. -/
theorem scorePollResumesCreditOfLe {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j cta n : Nat} (stage packet : Fin 2) (hw : warpIndex l g < 8)
    (hCredit : ProbabilityCredit l X (g,j) cta stage packet)
    (hn : n ≤ probabilityOrdinal l X cta stage packet (g,j)) :
    Resumes kernel X (g,MbarRing.Poll.nth X (scoreReadyObject l cta stage) g n) (g,j) := by
  obtain ⟨k,⟨pc,kind⟩,q,acq,scope,he,hKind,hOrdinal,hResume⟩ :=
    softmaxProbabilityCreditScorePoll hp hX stage packet hw hCredit
  change kind = _ at hKind
  subst kind
  have hOne := MbarRing.Poll.okPoll_get he
  have hMono := MbarRing.Poll.okPolls_mono (scoreReadyObject l cta stage) (X.tr g)
    (show k+1 ≤ j from hResume.1.2.1)
  obtain ⟨_,hGet⟩ := hCredit
  exact MbarRing.Poll.guard (fun _ _ _ _ _ _ h => actualCanonicalPoll hX h)
    (len_of_get hGet) (by omega)

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
