-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSize
import Kernels.TmlFa4Fwd.Flow.Code.Part015
import Kernels.TmlFa4Fwd.Flow.Code.Part016
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part019
import Kernels.TmlFa4Fwd.Flow.Code.Part020
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpOk

@[expose] public section

/-! # The source sizes of the warm block's row copies (`cp_size_warm`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {g w : Nat} {ent : Nat → Value}

size_site size_warm_f_0_0 .warm false 0 0
size_site size_warm_f_0_1 .warm false 0 1
size_site size_warm_f_1_0 .warm false 1 0
size_site size_warm_f_1_1 .warm false 1 1
size_site size_warm_f_2_0 .warm false 2 0
size_site size_warm_f_2_1 .warm false 2 1
size_site size_warm_f_3_0 .warm false 3 0
size_site size_warm_f_3_1 .warm false 3 1
size_site size_warm_f_4_0 .warm false 4 0
size_site size_warm_f_4_1 .warm false 4 1
size_site size_warm_f_5_0 .warm false 5 0
size_site size_warm_f_5_1 .warm false 5 1
size_site size_warm_f_6_0 .warm false 6 0
size_site size_warm_f_6_1 .warm false 6 1
size_site size_warm_f_7_0 .warm false 7 0
size_site size_warm_f_7_1 .warm false 7 1
size_site size_warm_f_8_0 .warm false 8 0
size_site size_warm_f_8_1 .warm false 8 1
size_site size_warm_f_9_0 .warm false 9 0
size_site size_warm_f_9_1 .warm false 9 1
size_site size_warm_f_10_0 .warm false 10 0
size_site size_warm_f_10_1 .warm false 10 1
size_site size_warm_f_11_0 .warm false 11 0
size_site size_warm_f_11_1 .warm false 11 1
size_site size_warm_f_12_0 .warm false 12 0
size_site size_warm_f_12_1 .warm false 12 1
size_site size_warm_f_13_0 .warm false 13 0
size_site size_warm_f_13_1 .warm false 13 1
size_site size_warm_f_14_0 .warm false 14 0
size_site size_warm_f_14_1 .warm false 14 1
size_site size_warm_f_15_0 .warm false 15 0
size_site size_warm_f_15_1 .warm false 15 1
size_site size_warm_t_0_0 .warm true 0 0
size_site size_warm_t_0_1 .warm true 0 1
size_site size_warm_t_1_0 .warm true 1 0
size_site size_warm_t_1_1 .warm true 1 1
size_site size_warm_t_2_0 .warm true 2 0
size_site size_warm_t_2_1 .warm true 2 1
size_site size_warm_t_3_0 .warm true 3 0
size_site size_warm_t_3_1 .warm true 3 1
size_site size_warm_t_4_0 .warm true 4 0
size_site size_warm_t_4_1 .warm true 4 1
size_site size_warm_t_5_0 .warm true 5 0
size_site size_warm_t_5_1 .warm true 5 1
size_site size_warm_t_6_0 .warm true 6 0
size_site size_warm_t_6_1 .warm true 6 1
size_site size_warm_t_7_0 .warm true 7 0
size_site size_warm_t_7_1 .warm true 7 1
size_site size_warm_t_8_0 .warm true 8 0
size_site size_warm_t_8_1 .warm true 8 1
size_site size_warm_t_9_0 .warm true 9 0
size_site size_warm_t_9_1 .warm true 9 1
size_site size_warm_t_10_0 .warm true 10 0
size_site size_warm_t_10_1 .warm true 10 1
size_site size_warm_t_11_0 .warm true 11 0
size_site size_warm_t_11_1 .warm true 11 1
size_site size_warm_t_12_0 .warm true 12 0
size_site size_warm_t_12_1 .warm true 12 1
size_site size_warm_t_13_0 .warm true 13 0
size_site size_warm_t_13_1 .warm true 13 1
size_site size_warm_t_14_0 .warm true 14 0
size_site size_warm_t_14_1 .warm true 14 1
size_site size_warm_t_15_0 .warm true 15 0
size_site size_warm_t_15_1 .warm true 15 1

/-- **The source size of a warm block's row copy.** -/
theorem cp_size_warm {b : Bool} {i : Fin 16} {c : Fin 2} {v : V} {kk : Fin 2} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (h : (code p L g w ent).AtD ⟨.cp .warm b i c, v, kk⟩ t)
    (hc : kernel.code[(Site.cp .warm b i c).pc]? = some ins)
    (hf : Fires (Site.cp .warm b i c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {sp : AsyncCopy.Spec} (hk : e.kind = .copy sp) :
    sp.src.size = cpSize L g v .warm i := by
  cases b <;> fin_cases i <;> fin_cases c
  · exact size_warm_f_0_0 h hc hf hk
  · exact size_warm_f_0_1 h hc hf hk
  · exact size_warm_f_1_0 h hc hf hk
  · exact size_warm_f_1_1 h hc hf hk
  · exact size_warm_f_2_0 h hc hf hk
  · exact size_warm_f_2_1 h hc hf hk
  · exact size_warm_f_3_0 h hc hf hk
  · exact size_warm_f_3_1 h hc hf hk
  · exact size_warm_f_4_0 h hc hf hk
  · exact size_warm_f_4_1 h hc hf hk
  · exact size_warm_f_5_0 h hc hf hk
  · exact size_warm_f_5_1 h hc hf hk
  · exact size_warm_f_6_0 h hc hf hk
  · exact size_warm_f_6_1 h hc hf hk
  · exact size_warm_f_7_0 h hc hf hk
  · exact size_warm_f_7_1 h hc hf hk
  · exact size_warm_f_8_0 h hc hf hk
  · exact size_warm_f_8_1 h hc hf hk
  · exact size_warm_f_9_0 h hc hf hk
  · exact size_warm_f_9_1 h hc hf hk
  · exact size_warm_f_10_0 h hc hf hk
  · exact size_warm_f_10_1 h hc hf hk
  · exact size_warm_f_11_0 h hc hf hk
  · exact size_warm_f_11_1 h hc hf hk
  · exact size_warm_f_12_0 h hc hf hk
  · exact size_warm_f_12_1 h hc hf hk
  · exact size_warm_f_13_0 h hc hf hk
  · exact size_warm_f_13_1 h hc hf hk
  · exact size_warm_f_14_0 h hc hf hk
  · exact size_warm_f_14_1 h hc hf hk
  · exact size_warm_f_15_0 h hc hf hk
  · exact size_warm_f_15_1 h hc hf hk
  · exact size_warm_t_0_0 h hc hf hk
  · exact size_warm_t_0_1 h hc hf hk
  · exact size_warm_t_1_0 h hc hf hk
  · exact size_warm_t_1_1 h hc hf hk
  · exact size_warm_t_2_0 h hc hf hk
  · exact size_warm_t_2_1 h hc hf hk
  · exact size_warm_t_3_0 h hc hf hk
  · exact size_warm_t_3_1 h hc hf hk
  · exact size_warm_t_4_0 h hc hf hk
  · exact size_warm_t_4_1 h hc hf hk
  · exact size_warm_t_5_0 h hc hf hk
  · exact size_warm_t_5_1 h hc hf hk
  · exact size_warm_t_6_0 h hc hf hk
  · exact size_warm_t_6_1 h hc hf hk
  · exact size_warm_t_7_0 h hc hf hk
  · exact size_warm_t_7_1 h hc hf hk
  · exact size_warm_t_8_0 h hc hf hk
  · exact size_warm_t_8_1 h hc hf hk
  · exact size_warm_t_9_0 h hc hf hk
  · exact size_warm_t_9_1 h hc hf hk
  · exact size_warm_t_10_0 h hc hf hk
  · exact size_warm_t_10_1 h hc hf hk
  · exact size_warm_t_11_0 h hc hf hk
  · exact size_warm_t_11_1 h hc hf hk
  · exact size_warm_t_12_0 h hc hf hk
  · exact size_warm_t_12_1 h hc hf hk
  · exact size_warm_t_13_0 h hc hf hk
  · exact size_warm_t_13_1 h hc hf hk
  · exact size_warm_t_14_0 h hc hf hk
  · exact size_warm_t_14_1 h hc hf hk
  · exact size_warm_t_15_0 h hc hf hk
  · exact size_warm_t_15_1 h hc hf hk

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
