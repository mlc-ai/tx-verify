-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Flow.Code.Part039
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof

/-- The second PV issue checks the low column field even for a well-typed address.
In the first P buffer register 565 carries the recorded base unchanged. -/
theorem pvOffsetFault {L : Launch} {g : Nat} {t : TState} (hg : g < L.threads)
    (hpc : t.pc = 2533) (hf : t.fault = none)
    (hguard : guardHolds t (some (15, false)) = .ok true)
    (hd : t.regs 564 = some (b32 65791)) (ha : t.regs 565 = some (b32 65535)) :
    out kernel Assumptions.all L g t = .ev (.ub .badValue) := by
  simp only [out, hf, hpc, Flow.code_2533, hguard]
  change Out.ev (mmaTmemTmpl L g t .one false .f16 564 565 8 (.reg 2045) (.reg 566)
    [.imm 0, .imm 0, .imm 0, .imm 0] (.reg 16) none _) = _
  have hoff : tmemOffset 65535 8 = .error .badValue := rfl
  simp [mmaTmemTmpl, hg, readBits_b32 hd (by decide), readBits_b32 ha (by decide), hoff,
    bind, Except.bind, ofExec]

end PTX.Kernels.InklingRelDecode.Proof.Mma
