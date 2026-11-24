-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarriers
public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsReuseClosure
import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierTerminal
public import Lemmas.Protocol.NamedBarArrive

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX Thread

/-- An arriving thread may reuse a rendezvous once its prior generation has released. -/
def ArriveReleaseBeforeReuse (l : Launch) (X : Execution) : Prop :=
  ∀ i key, CtaBarArrivalK l X i key → ∀ count,
    BarrierArrival X i (key % 16) count .arrive →
    ∀ j > i.2, ∀ nextCount mode, BarrierArrival X (i.1, j) (key % 16) nextCount mode →
      CtaBarDone l X (i.1 / l.block) key

/-- Count agreement and release before reuse exclude the named barrier arrival faults. -/
theorem noNamedBarrierFault {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hReuse : ArriveReleaseBeforeReuse l X) : ¬ CtaBarFault l X := by
  apply NamedBar.no_duplicate_arrival hX
  · intro i j id count count' _ _ mode mode' _ he hf
    exact barrierCountAgrees hp hX
      (i := i) (j := j) (id := id) (mode := mode) (mode' := mode') ⟨_, he, rfl⟩ ⟨_, hf, rfl⟩
  · intro i key _ count j event hk hi hj he hId
    obtain ⟨_, nextCount, mode, rfl⟩ := NamedBar.isBarId_form hId
    exact hReuse i key hk count ⟨_, hi, rfl⟩ j hj nextCount mode ⟨_, he, rfl⟩

/-- All actual asymmetric arrivals obey release before reuse. -/
theorem arriveReleaseBeforeReuse {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) (hUsedK : UsedKProtected p X) :
    ArriveReleaseBeforeReuse l X := by
  rintro ⟨g,i⟩ key hk count hi j hj nextCount mode hn
  rcases asymmetricArrivalId hp hX hi with hTerminal | hStatistics
  · exact (noBarrierAfterFinalArrival hp hX (hTerminal ▸ hi) hj (hTerminal ▸ hn)).elim
  · exact Statistics.actualStatsArrivalReleaseBeforeReuse hp hX hCuQ hUsedK
      hStatistics hk hi hn hj

/-- The actual named-barrier count and release protocols rule out arrival faults. -/
theorem noActualNamedBarrierFault {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) : ¬ CtaBarFault l X :=
  noNamedBarrierFault hp hX
    (arriveReleaseBeforeReuse hp hX hCuQ (usedKProtected hp hX))

end PTX.Kernels.TmlFa4Fwd.Protocol
