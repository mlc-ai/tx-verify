-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CoreNumeric
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part042

@[expose] public section

/-! # Core's packed conversion and product at FlashMLA's dequantizer

The instructions of FlashMLA's dequantizer at pcs 2740 (`cvt.rn.bf16x2.ue8m0x2`) and 2742
(`mul.bf16x2`) are `cvtPair8I` and `mulBf16x2I` (`Lemmas/Flow/CoreNumeric.lean`), so Core reads
them as `coreCvtPair8` and `coreFloat` of the registers' values. -/

namespace PTX.Tests.CoreNumeric
open PTX PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

variable {L : Launch} {g : Nat}

theorem code_2740 : kernel.code[2740]? = some ⟨none, .cvt (cvtPair8I .ue8m0 191 2465)⟩ :=
  Flow.code_2740

theorem code_2742 : kernel.code[2742]? = some ⟨none, .float (mulBf16x2I 2464 2465 2463)⟩ :=
  Flow.code_2742

theorem core_2740 {t : TState} {v : Value} (h : t.regs 191 = some v) :
    execLocal L g t (.cvt (cvtPair8I .ue8m0 191 2465)) =
      (coreCvtPair8 .ue8m0 v).map fun w => PTX.next (setReg t 2465 w) :=
  execLocal_cvtPair8 (.inr rfl) h

theorem core_2742 {t : TState} {va vb : Value} (ha : t.regs 2464 = some va)
    (hb : t.regs 2465 = some vb) :
    execLocal L g t (.float (mulBf16x2I 2464 2465 2463)) =
      (coreFloat (mulBf16x2I 0 0 0) [va, vb]).map fun v => PTX.next (setReg t 2463 v) :=
  execLocal_mulBf16x2 ha hb

end PTX.Tests.CoreNumeric
