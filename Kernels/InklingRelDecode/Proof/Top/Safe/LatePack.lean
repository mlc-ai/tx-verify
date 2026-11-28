-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.PWords
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Top.Safe.NoRace
import Kernels.InklingRelDecode.Proof.Protocol.Alpha.RoundNi
import Kernels.InklingRelDecode.Proof.Softmax.Export.PackLate

@[expose] public section

/-! # The packs of the probabilities read numbers

Both sources of each `cvt.rn.bf16x2.f32` of the probability pack read as extended reals at the
states a lane reaches (`Softmax.Export.pack_late`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Assumptions

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **Both operands of a pack `cvt.rn.bf16x2.f32` read as extended reals**
(`Iface.LateValues.pack`). -/
theorem Safe.pack (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ∀ g t, g % L.block < 128 → Iface.LaneState L X g t → Iface.packPc t.pc = true →
      ∀ c, kernel.code[t.pc]? = some ⟨none, .cvt c⟩ → ∀ r ∈ c.srcs, ∀ a, r = .reg a →
        ∃ x : EReal, readERealOpnd t .f32 r = some (.ok x) := by
  have hS := Safe.scoreWords hp hX hf hou safe rows init nub
  intro g t lane hl hpc c hc
  exact Softmax.Export.pack_late hp hX hf (hS g)
    (fun lane k mode sent b c recv ok g1 => Protocol.Shared.shfl5_ni hp hX hf (hS) lane g1)
    lane hl hpc c hc

end PTX.Kernels.InklingRelDecode.Proof.Top
