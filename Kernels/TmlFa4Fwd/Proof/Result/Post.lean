-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Result.Lse
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
public import Kernels.TmlFa4Fwd.Proof.Protocol.OutputBytes
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputCoordinates
import Kernels.TmlFa4Fwd.Proof.Thread.GlobalWrites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Result
open PTX Epilogue

/-- The values carried by all completed, covering O writes. -/
def OutputValues (p : Params) (X : Execution) : Prop :=
  ∀ b < p.batch, ∀ h < p.heads, ∀ row < p.qLength b, ∀ d < 128, ∀ k < 4,
    ∀ w a bytes, X.MemWrites w a bytes → a.Covers ((p.oLoc (p.qOffset b + row) h d).at k) →
      wbyte a bytes ((p.oLoc (p.qOffset b + row) h d).at k) =
        some ((Value.float .f32 (attention p b h row d)).byteAt k)

/-- A complete execution supplies every output byte and leaves the other global bytes unchanged,
given its proved dataflow values. -/
theorem postOfValues {p : Params} {l : Launch} {m : Mem0} {X : Execution} {out : FinalMem}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hComplete : Complete l X) (hFinal : IsFinal l m X out)
    (hOut : OutputValues p X) (hLse : Correction.LseWriteValues p X) : Post p m out := by
  have hFrame := (outputIntentFootprint hp hX).performed
  apply postOfOutputBytes hX hFinal hFrame
  · intro b hb h hh row hr d hd k hk
    exact ⟨outputHasWriter hp hX hComplete hFrame hb hh hr hd hk, hOut b hb h hh row hr d hd k hk⟩
  · intro b hb h hh row hr k hk
    exact lseOutputByte hp hX hComplete
      (usedKProtected hp hX) hLse hb hh hr hk

end PTX.Kernels.TmlFa4Fwd.Result
