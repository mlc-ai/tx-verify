-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingValuePrefix
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderCopyBytes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX Thread.Loader Epilogue Prologue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Every priming value pair of an active loader can finish in any consistent
prefix, including a prefix in which the issuing lane stopped at the vector issue. -/
theorem pendingPrimingValueVector (hFrame : OutputFootprint p X) {g j : Nat} {pair : Fin 16}
    {upper : Bool} {spec : AsyncCopy.Spec} (hVector : PrimingValueVector X (g, j) pair upper spec)
    (hWarp : 14 ≤ warpIndex l g) (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hPending : (X.async.copies (g, j)).writeBytes = none) :
    ∃ Y, Consistent l kernel Assumptions.all m Y ∧ X.le Y ∧ X.size l < Y.size l := by
  obtain ⟨batch, hb, _, _, hHead, hSize, hLoc⟩ := hVector.source hp hX hFrame hWarp hCTA
  refine pendingCacheVector hp hX hFrame hVector.copy hPending .value (lane := g % l.block)
    hb hHead upper (fun hLive => ?_) hSize
  rw [hLoc]
  simp [cacheVector, cacheLayout, Loader.primingScratchPage, hLive]

end
end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
