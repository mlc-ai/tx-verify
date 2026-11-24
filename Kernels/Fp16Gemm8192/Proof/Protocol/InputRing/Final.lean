-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Faults
public import Lemmas.Protocol.PairTmaRing.Final

@[expose] public section

/-! # An input ring slot's barriers at the end of an execution

A selector's thread that polls a slot's barrier has the successful polls of the selector's
poller (`producer_okPolls`, `consumer_okPolls`). The final phase of producer `a`'s empty barrier
is its poller's successful polls or one less (`empty_final_phase`): its poll for use `N - 1`
found phase `N - 1`, and the barrier's notifications are of uses below `N`, two per use. The
final phase of the full barrier is a consumer's successful polls or one more
(`full_final_phase`): its last poll found that phase, and the barrier's arrivals are of uses at
most that count. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread of producer `a`'s selector that polls its empty barrier has the producer's
successful polls. -/
theorem producer_okPolls (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {s : Fin 4} {a : Fin 2} {g j : Nat} {e : Event}
    (hprod : producerThread L c a g = true) (he : X.get (g, j) = some e) {p : Nat}
    {ok acq : Bool} {sc : MbarScope} (hk : e.kind = .wait ((slot L c s).empty a) p ok acq sc) :
    okPolls ((slot L c s).empty a) (X.tr g) =
      okPolls ((slot L c s).empty a) (X.tr (producerOf L X c s a)) := by
  by_cases hpos : 0 < okPolls ((slot L c s).empty a) (X.tr g)
  · obtain ⟨j', pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X) (g := g)
      (k := (X.tr g).length) (m := (slot L c s).empty a) (by rw [List.take_length]; exact hpos)
    rw [← producerOf_eq hX ht hprod he']
  · by_cases hpos' : 0 < okPolls ((slot L c s).empty a) (X.tr (producerOf L X c s a))
    · obtain ⟨j', pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X)
        (g := producerOf L X c s a) (k := (X.tr (producerOf L X c s a)).length)
        (m := (slot L c s).empty a) (by rw [List.take_length]; exact hpos')
      have := producer_unique hX ht (producerOf_thread hpre c s a) hprod he' he rfl hk
      rw [← this]
    · omega

/-- A thread of consumer `b`'s selector that polls the full barrier has the consumer's
successful polls. -/
theorem consumer_okPolls (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {s : Fin 4} {b : Fin 2} {g j : Nat} {e : Event}
    (hcons : consumerThread L c b g = true) (he : X.get (g, j) = some e) {p : Nat}
    {ok acq : Bool} {sc : MbarScope} (hk : e.kind = .wait ((slot L c s).full 0) p ok acq sc) :
    okPolls ((slot L c s).full 0) (X.tr g) =
      okPolls ((slot L c s).full 0) (X.tr (consumerOf L X c s b)) := by
  by_cases hpos : 0 < okPolls ((slot L c s).full 0) (X.tr g)
  · obtain ⟨j', pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X) (g := g)
      (k := (X.tr g).length) (m := (slot L c s).full 0) (by rw [List.take_length]; exact hpos)
    rw [← consumerOf_eq hX ht hcons he']
  · by_cases hpos' : 0 < okPolls ((slot L c s).full 0) (X.tr (consumerOf L X c s b))
    · obtain ⟨j', pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X)
        (g := consumerOf L X c s b) (k := (X.tr (consumerOf L X c s b)).length)
        (m := (slot L c s).full 0) (by rw [List.take_length]; exact hpos')
      have := consumer_unique hX ht (consumerOf_thread hpre c s b) hcons he' he rfl hk
      rw [← this]
    · omega

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
