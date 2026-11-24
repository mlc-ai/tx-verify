-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemReadConflicts
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorSources
import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Lemmas.Tcgen05.TmemLatestSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread

/-- The actual C read of each accumulating MMA has a stable latest write into
the same allocation. This applies to current and carried accumulators. -/
theorem mmaAccumulatorReadSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {i : EvId} {cell : Cell} (hRead : X.MmaReadCell i cell) :
    ∃ source, ReadSource l X .acc source i cell := by
  have hWrites := tensorWritesSafeOfCuQ hp hX hCuQ
  have hReads := (readsSafe_iff.mp (tensorReadsSafeOfCuQ hp hX hCuQ)).1
  have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
  obtain ⟨prior,_,_,hWrite,hBefore⟩ := mmaAccumulatorCandidate hp hX hRead
  obtain ⟨_,hLifetime⟩ := mmaAccessLifetime hp hX hCuQ (.inr (.inl hRead))
  apply readSourceOfCandidate hX hGuard hWrites (candidate := prior) _ _ (.inl hWrite) hBefore
  · intro other hOther
    rcases hReads _ _ _ hRead hOther with h | h | h
    · exact .inr (.inl h.symm)
    · exact .inl h
    · exact .inr h
  · intro _ _ _ cta r hr hCover release hRelease
    exact .inl (hLifetime cta r hr hCover release hRelease)

end PTX.Kernels.TmlFa4Fwd.Safety
