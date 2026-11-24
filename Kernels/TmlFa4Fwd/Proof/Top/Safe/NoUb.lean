-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoTmemInstruction
import Kernels.TmlFa4Fwd.Proof.Correction.Export.NoUb
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Elements
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.StatReadsAll
import Kernels.TmlFa4Fwd.Proof.Top.Safe.SmScores

@[expose] public section

/-! # The data reads of the softmax and correction lanes

The score loads of the softmax lanes and the data reads of the correction lanes return what their
data machines follow (`Values.softFacts`; the order of the induction is in
`Protocol/Values/Elements.lean`). Nothing of the class is open. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0}

/-- **A softmax or correction lane makes no undefined behaviour.** -/
theorem Safe.dataNoUb (hp : Pre p l m)
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X) {g k : Nat} {e : Event}
    (hw : Prologue.warpIndex l g < 12) (he : X.get (g, k) = some e) (f : Fault) :
    e.kind ≠ .ub f := by
  have hFw := launchFollow hp hX
  have hE := Values.softFacts hp hX hFw
  by_cases h8 : Prologue.warpIndex l g < 8
  · exact softNoUb hp hX hFw (Values.scorePayloads hp hX hFw hE) h8 he f
  · exact CorrWarp.noUb_of_data hp hX ⟨by omega, by omega⟩ (Frame.lt_of_get hX he) rfl
      (Values.dataTo hp hX hFw hE (Frame.lt_of_get hX he) (by omega) (by omega)) he f

end PTX.Kernels.TmlFa4Fwd.Proof.Top
