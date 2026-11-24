-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSize
import Kernels.TmlFa4Fwd.Flow.Code.Part023
import Kernels.TmlFa4Fwd.Flow.Code.Part024
import Kernels.TmlFa4Fwd.Flow.Code.Part025
import Kernels.TmlFa4Fwd.Flow.Code.Part026
import Kernels.TmlFa4Fwd.Flow.Code.Part027
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpOk

@[expose] public section

/-! # The source sizes of the steady block's row copies (`cp_size_steady`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {g w : Nat} {ent : Nat → Value}

size_site size_steady_f_0_0 .steady false 0 0
size_site size_steady_f_0_1 .steady false 0 1
size_site size_steady_f_1_0 .steady false 1 0
size_site size_steady_f_1_1 .steady false 1 1
size_site size_steady_f_2_0 .steady false 2 0
size_site size_steady_f_2_1 .steady false 2 1
size_site size_steady_f_3_0 .steady false 3 0
size_site size_steady_f_3_1 .steady false 3 1
size_site size_steady_f_4_0 .steady false 4 0
size_site size_steady_f_4_1 .steady false 4 1
size_site size_steady_f_5_0 .steady false 5 0
size_site size_steady_f_5_1 .steady false 5 1
size_site size_steady_f_6_0 .steady false 6 0
size_site size_steady_f_6_1 .steady false 6 1
size_site size_steady_f_7_0 .steady false 7 0
size_site size_steady_f_7_1 .steady false 7 1
size_site size_steady_f_8_0 .steady false 8 0
size_site size_steady_f_8_1 .steady false 8 1
size_site size_steady_f_9_0 .steady false 9 0
size_site size_steady_f_9_1 .steady false 9 1
size_site size_steady_f_10_0 .steady false 10 0
size_site size_steady_f_10_1 .steady false 10 1
size_site size_steady_f_11_0 .steady false 11 0
size_site size_steady_f_11_1 .steady false 11 1
size_site size_steady_f_12_0 .steady false 12 0
size_site size_steady_f_12_1 .steady false 12 1
size_site size_steady_f_13_0 .steady false 13 0
size_site size_steady_f_13_1 .steady false 13 1
size_site size_steady_f_14_0 .steady false 14 0
size_site size_steady_f_14_1 .steady false 14 1
size_site size_steady_f_15_0 .steady false 15 0
size_site size_steady_f_15_1 .steady false 15 1
size_site size_steady_t_0_0 .steady true 0 0
size_site size_steady_t_0_1 .steady true 0 1
size_site size_steady_t_1_0 .steady true 1 0
size_site size_steady_t_1_1 .steady true 1 1
size_site size_steady_t_2_0 .steady true 2 0
size_site size_steady_t_2_1 .steady true 2 1
size_site size_steady_t_3_0 .steady true 3 0
size_site size_steady_t_3_1 .steady true 3 1
size_site size_steady_t_4_0 .steady true 4 0
size_site size_steady_t_4_1 .steady true 4 1
size_site size_steady_t_5_0 .steady true 5 0
size_site size_steady_t_5_1 .steady true 5 1
size_site size_steady_t_6_0 .steady true 6 0
size_site size_steady_t_6_1 .steady true 6 1
size_site size_steady_t_7_0 .steady true 7 0
size_site size_steady_t_7_1 .steady true 7 1
size_site size_steady_t_8_0 .steady true 8 0
size_site size_steady_t_8_1 .steady true 8 1
size_site size_steady_t_9_0 .steady true 9 0
size_site size_steady_t_9_1 .steady true 9 1
size_site size_steady_t_10_0 .steady true 10 0
size_site size_steady_t_10_1 .steady true 10 1
size_site size_steady_t_11_0 .steady true 11 0
size_site size_steady_t_11_1 .steady true 11 1
size_site size_steady_t_12_0 .steady true 12 0
size_site size_steady_t_12_1 .steady true 12 1
size_site size_steady_t_13_0 .steady true 13 0
size_site size_steady_t_13_1 .steady true 13 1
size_site size_steady_t_14_0 .steady true 14 0
size_site size_steady_t_14_1 .steady true 14 1
size_site size_steady_t_15_0 .steady true 15 0
size_site size_steady_t_15_1 .steady true 15 1

/-- **The source size of a steady block's row copy.** -/
theorem cp_size_steady {b : Bool} {i : Fin 16} {c : Fin 2} {v : V} {kk : Fin 2} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (h : (code p L g w ent).AtD ⟨.cp .steady b i c, v, kk⟩ t)
    (hc : kernel.code[(Site.cp .steady b i c).pc]? = some ins)
    (hf : Fires (Site.cp .steady b i c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {sp : AsyncCopy.Spec} (hk : e.kind = .copy sp) :
    sp.src.size = cpSize L g v .steady i := by
  cases b <;> fin_cases i <;> fin_cases c
  · exact size_steady_f_0_0 h hc hf hk
  · exact size_steady_f_0_1 h hc hf hk
  · exact size_steady_f_1_0 h hc hf hk
  · exact size_steady_f_1_1 h hc hf hk
  · exact size_steady_f_2_0 h hc hf hk
  · exact size_steady_f_2_1 h hc hf hk
  · exact size_steady_f_3_0 h hc hf hk
  · exact size_steady_f_3_1 h hc hf hk
  · exact size_steady_f_4_0 h hc hf hk
  · exact size_steady_f_4_1 h hc hf hk
  · exact size_steady_f_5_0 h hc hf hk
  · exact size_steady_f_5_1 h hc hf hk
  · exact size_steady_f_6_0 h hc hf hk
  · exact size_steady_f_6_1 h hc hf hk
  · exact size_steady_f_7_0 h hc hf hk
  · exact size_steady_f_7_1 h hc hf hk
  · exact size_steady_f_8_0 h hc hf hk
  · exact size_steady_f_8_1 h hc hf hk
  · exact size_steady_f_9_0 h hc hf hk
  · exact size_steady_f_9_1 h hc hf hk
  · exact size_steady_f_10_0 h hc hf hk
  · exact size_steady_f_10_1 h hc hf hk
  · exact size_steady_f_11_0 h hc hf hk
  · exact size_steady_f_11_1 h hc hf hk
  · exact size_steady_f_12_0 h hc hf hk
  · exact size_steady_f_12_1 h hc hf hk
  · exact size_steady_f_13_0 h hc hf hk
  · exact size_steady_f_13_1 h hc hf hk
  · exact size_steady_f_14_0 h hc hf hk
  · exact size_steady_f_14_1 h hc hf hk
  · exact size_steady_f_15_0 h hc hf hk
  · exact size_steady_f_15_1 h hc hf hk
  · exact size_steady_t_0_0 h hc hf hk
  · exact size_steady_t_0_1 h hc hf hk
  · exact size_steady_t_1_0 h hc hf hk
  · exact size_steady_t_1_1 h hc hf hk
  · exact size_steady_t_2_0 h hc hf hk
  · exact size_steady_t_2_1 h hc hf hk
  · exact size_steady_t_3_0 h hc hf hk
  · exact size_steady_t_3_1 h hc hf hk
  · exact size_steady_t_4_0 h hc hf hk
  · exact size_steady_t_4_1 h hc hf hk
  · exact size_steady_t_5_0 h hc hf hk
  · exact size_steady_t_5_1 h hc hf hk
  · exact size_steady_t_6_0 h hc hf hk
  · exact size_steady_t_6_1 h hc hf hk
  · exact size_steady_t_7_0 h hc hf hk
  · exact size_steady_t_7_1 h hc hf hk
  · exact size_steady_t_8_0 h hc hf hk
  · exact size_steady_t_8_1 h hc hf hk
  · exact size_steady_t_9_0 h hc hf hk
  · exact size_steady_t_9_1 h hc hf hk
  · exact size_steady_t_10_0 h hc hf hk
  · exact size_steady_t_10_1 h hc hf hk
  · exact size_steady_t_11_0 h hc hf hk
  · exact size_steady_t_11_1 h hc hf hk
  · exact size_steady_t_12_0 h hc hf hk
  · exact size_steady_t_12_1 h hc hf hk
  · exact size_steady_t_13_0 h hc hf hk
  · exact size_steady_t_13_1 h hc hf hk
  · exact size_steady_t_14_0 h hc hf hk
  · exact size_steady_t_14_1 h hc hf hk
  · exact size_steady_t_15_0 h hc hf hk
  · exact size_steady_t_15_1 h hc hf hk

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
