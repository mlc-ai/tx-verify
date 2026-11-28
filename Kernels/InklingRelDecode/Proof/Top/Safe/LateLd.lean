-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.Rescale
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Protocol.Values.LdsWord
import Kernels.InklingRelDecode.Proof.Top.Safe.ValEnv
import Kernels.InklingRelDecode.Proof.Top.Safe.LateBfly
import Kernels.InklingRelDecode.Proof.Top.Safe.LateExp2
import Kernels.InklingRelDecode.Proof.Top.Safe.LatePack
import Kernels.InklingRelDecode.Proof.Top.Safe.LateHalf
import Kernels.InklingRelDecode.Proof.Top.Safe.LateRcpField
import Kernels.InklingRelDecode.Proof.Top.Safe.LateDecl
import Kernels.InklingRelDecode.Proof.Top.Safe.LateOWord

@[expose] public section

/-! # The words the three `tcgen05.ld` return are `.f32` data of four bytes

The score load returns the results of QK MMAs (`ld_s_word`), the accumulator loads return PV results
and rescale words (`ld_o_word` with `Safe.rescaleFloat`): all are `.float .f32` numbers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol.Values

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **The words of the `tcgen05.ld` are `.f32` data of four bytes**
(`Iface.LateValues.tcLd`). -/
theorem Safe.tcLd (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) {g k pc a vals sh}
    (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (hpc : pc ∈ Iface.tcLdPcs) :
    ∀ v ∈ vals, Flow.TyG.Dat32 v := by
  obtain ⟨base, words, hG, hws, ht, hmd, form⟩ := Safe.valEnv hp hX hf safe rows init
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  simp only [Iface.tcLdPcs, List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | h
  · obtain ⟨r, hr⟩ := ld_s_word hp hX hf hou safe base rows init hG hws ht hmd words nub form
      he hj
    rw [List.getElem?_eq_getElem hj] at hr
    rw [Option.some.inj hr]
    exact ⟨Flow.f32Dat_float r, rfl, nofun⟩
  · obtain ⟨r, hr⟩ := Safe.ldOFloat hp hX hf hou safe rows init nub he h _ hv
    rw [hr]
    exact ⟨Flow.f32Dat_float r, rfl, nofun⟩

end PTX.Kernels.InklingRelDecode.Proof.Top
