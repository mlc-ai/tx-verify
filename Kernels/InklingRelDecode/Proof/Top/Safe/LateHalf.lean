-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.PWords
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Top.Safe.NoRace
import Kernels.InklingRelDecode.Proof.Protocol.Alpha.RoundNi
import Kernels.InklingRelDecode.Proof.Softmax.Export.HalfLate

@[expose] public section

/-! # The registers of the bias path hold halves -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Assumptions

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **The registers a pack, unpack or widening of the bias path reads hold halves**
(`Iface.LateValues.half`). -/
theorem Safe.half (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ∀ g t, g % L.block < 128 → Iface.LaneState L X g t → Iface.halfPc t.pc = true →
      ∀ i, kernel.code[t.pc]? = some i → ∀ srcs, Iface.halfSrcs i.op = some srcs →
        ∀ r, .reg r ∈ srcs → ∃ v, t.regs r = some v ∧ TyG.halfSrcOk i.op v := by
  have hS := Safe.scoreWords hp hX hf hou safe rows init nub
  intro g t lane hl
  exact Softmax.Export.half_late hp hX hf (hS g)
    (fun lane k mode sent b c recv ok g1 => Protocol.Shared.shfl5_ni hp hX hf (hS) lane g1)
    lane hl

end PTX.Kernels.InklingRelDecode.Proof.Top
