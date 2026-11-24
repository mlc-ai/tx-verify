-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Faults
public import Lemmas.Protocol.PairTmaRing.Order

@[expose] public section

/-! # A tensor load of the input ring is visible to the MMA reads that follow its phase's poll

The loads of a slot complete on its full barrier, each as a notification of its own copy. An MMA
thread's successful poll for use `n` observes every item of use `n`, among them the completion of
each copy of production `n`: an `AsyncObserved` of that copy by the poll
(`PairTmaRing.copy_observed`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A copy is observed by its production's poll.** The successful full poll of MMA thread
`b` with `n` earlier ones observes the completion of a tensor issue on the slot's full barrier of
production `n` (its loader's earlier issues there over three). -/
theorem copy_observed (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {s : Fin 4} {b : Fin 2} {g k pc al : Nat}
    {sp : TensorCopy.Spec} (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩)
    (hm : sp.mbar = (slot L c s).full 0) {j pcw p : Nat} {acq : Bool} {sc : MbarScope}
    (hew : X.get (consumerOf L X c s b, j) = some ⟨pcw, .wait ((slot L c s).full 0) p true acq sc⟩)
    (hj : okPolls ((slot L c s).full 0) ((X.tr (consumerOf L X c s b)).take j) =
      ((X.tr g).take k).countP (issuesTo ((slot L c s).full 0)) / 3) :
    AsyncObserved X (g, k) (.notify .load) (consumerOf L X c s b, j) true sc :=
  PairTmaRing.copy_observed hX (hyp hpre hX ht c s) he hm hew hj

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
