-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.LateDecl
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Top.Safe.LateLd
import Kernels.InklingRelDecode.Proof.Top.Safe.LateOWord
import Kernels.InklingRelDecode.Proof.Top.Safe.LateBfly
import Kernels.InklingRelDecode.Proof.Top.Safe.LateExp2
import Kernels.InklingRelDecode.Proof.Top.Safe.LatePack
import Kernels.InklingRelDecode.Proof.Top.Safe.LateHalf
import Kernels.InklingRelDecode.Proof.Top.Safe.LateRcpField
import Kernels.InklingRelDecode.Proof.Softmax.Export.EpiDecl
import Kernels.InklingRelDecode.Proof.Softmax.Export.RcpLate

@[expose] public section

/-! # The value facts of the softmax and epilogue data lanes

The products of the epilogue (pcs 2642 to 2673) multiply the pair of the reciprocal by the pairs of
the accumulator words: the words are numbers (`Safe.ldOFloat`) and the reciprocal is one
(`Softmax.Export.rcp_word`). With them the arithmetic is not declined (`Safe.noDecline`) and every
field of `Iface.LateValues` is proved. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Assumptions

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **The epilogue's products of pcs 2642 to 2673 are not declined.** -/
theorem Safe.declEpi (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ∀ g t, g % L.block < 128 → Iface.LaneState L X g t → 2642 ≤ t.pc → t.pc ≤ 2673 →
      ∀ i, kernel.code[t.pc]? = some i → execIdealFloat L g t i.op ≠ none := by
  intro g t _ hl h1 h2 i hc
  exact Softmax.Export.epi_decl
    (fun k a vals sh he x hx => by
      obtain ⟨r, rfl⟩ := Safe.ldOFloat hp hX hf hou safe rows init nub he (Or.inr rfl) x hx
      exact Flow.has_float_fl r)
    (fun _ hs hpc => Softmax.Export.rcp_word hs hpc) hl h1 h2 hc

/-- **The ideal-real rule does not decline `add`, `sub` and `mul`**
(`Iface.LateValues.noDecline`). -/
theorem Safe.noDecline (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ∀ g t, g % L.block < 128 → Iface.LaneState L X g t → Iface.declinePc t.pc = true →
      ∀ i, kernel.code[t.pc]? = some i → execIdealFloat L g t i.op ≠ none :=
  Safe.noDeclineOf hp hX hf hou safe rows init nub (Safe.declEpi hp hX hf hou safe rows init nub)

/-- **The value facts of the softmax and epilogue data lanes** (`Iface.LateValues`). -/
theorem Safe.lateValues (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) : Iface.LateValues L X where
  exp2 := Safe.exp2 hp hX hf hou safe rows init nub
  rcp := Safe.rcp
  tcLd := fun he _ hpc => Safe.tcLd hp hX hf hou safe rows init nub he hpc
  noDecline := Safe.noDecline hp hX hf hou safe rows init nub
  pack := Safe.pack hp hX hf hou safe rows init nub
  half := Safe.half hp hX hf hou safe rows init nub
  bfly := fun he lane hpc => Safe.bfly hp hX hf hou safe rows init nub he lane hpc
  ld := fun he lane => Safe.ldWord hp hX hf hou safe rows init nub he lane

end PTX.Kernels.InklingRelDecode.Proof.Top
