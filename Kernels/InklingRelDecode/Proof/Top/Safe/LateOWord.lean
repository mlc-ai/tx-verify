-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.Rescale
import Kernels.InklingRelDecode.Proof.Protocol.Values.LdoWord
import Kernels.InklingRelDecode.Proof.Protocol.Values.StoreElement
import Kernels.InklingRelDecode.Proof.Top.Safe.ValEnv

@[expose] public section

/-! # The words the accumulator loads return are numbers

The loads of pcs 2260 and 2607 return PV results and rescale words (`ld_o_word` with
`Safe.rescaleFloat`): `.float .f32` numbers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol.Values

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **The words of the accumulator loads are `.f32` numbers.** -/
theorem Safe.ldOFloat (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) {g k pc a vals sh}
    (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (hpc : pc = 2260 ∨ pc = 2607) :
    ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r := by
  obtain ⟨base, words, hG, hws, ht, hmd, form⟩ := Safe.valEnv hp hX hf safe rows init
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  obtain ⟨r, hr⟩ := ld_o_word hp hX hf hou safe base rows init hG hws ht hmd he hpc hj
    (Safe.elementsOf hp hX hf hou safe rows init nub fun {i src cell old} hd hrd hs hv =>
      store_element hp hX hf hou hG safe base rows init hrd hs hv fun hst =>
        Safe.rescaleFloat hp hX hf hou safe rows init nub hst)
    fun src _ _ _ _ hst => Safe.rescaleFloat hp hX hf hou safe rows init nub hst
  rw [List.getElem?_eq_getElem hj] at hr
  exact ⟨r, Option.some.inj hr⟩

end PTX.Kernels.InklingRelDecode.Proof.Top
