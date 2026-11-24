-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Addr
import Kernels.TmlFa4Fwd.Flow.Code.Part023
import Kernels.TmlFa4Fwd.Flow.Code.Part024
import Kernels.TmlFa4Fwd.Flow.Code.Part025
import Kernels.TmlFa4Fwd.Flow.Code.Part026
import Kernels.TmlFa4Fwd.Flow.Code.Part027
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpOk
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSite
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Local

@[expose] public section

/-! # The steady block's row copies are no undefined behaviour

The 64 row copies of the steady block's two packets, one theorem each (`cp_site`), and their
dispatcher (`cp_safe_steady`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

cp_site cp_steady_f_0_0 .steady false 0 0
cp_site cp_steady_f_0_1 .steady false 0 1
cp_site cp_steady_f_1_0 .steady false 1 0
cp_site cp_steady_f_1_1 .steady false 1 1
cp_site cp_steady_f_2_0 .steady false 2 0
cp_site cp_steady_f_2_1 .steady false 2 1
cp_site cp_steady_f_3_0 .steady false 3 0
cp_site cp_steady_f_3_1 .steady false 3 1
cp_site cp_steady_f_4_0 .steady false 4 0
cp_site cp_steady_f_4_1 .steady false 4 1
cp_site cp_steady_f_5_0 .steady false 5 0
cp_site cp_steady_f_5_1 .steady false 5 1
cp_site cp_steady_f_6_0 .steady false 6 0
cp_site cp_steady_f_6_1 .steady false 6 1
cp_site cp_steady_f_7_0 .steady false 7 0
cp_site cp_steady_f_7_1 .steady false 7 1
cp_site cp_steady_f_8_0 .steady false 8 0
cp_site cp_steady_f_8_1 .steady false 8 1
cp_site cp_steady_f_9_0 .steady false 9 0
cp_site cp_steady_f_9_1 .steady false 9 1
cp_site cp_steady_f_10_0 .steady false 10 0
cp_site cp_steady_f_10_1 .steady false 10 1
cp_site cp_steady_f_11_0 .steady false 11 0
cp_site cp_steady_f_11_1 .steady false 11 1
cp_site cp_steady_f_12_0 .steady false 12 0
cp_site cp_steady_f_12_1 .steady false 12 1
cp_site cp_steady_f_13_0 .steady false 13 0
cp_site cp_steady_f_13_1 .steady false 13 1
cp_site cp_steady_f_14_0 .steady false 14 0
cp_site cp_steady_f_14_1 .steady false 14 1
cp_site cp_steady_f_15_0 .steady false 15 0
cp_site cp_steady_f_15_1 .steady false 15 1
cp_site cp_steady_t_0_0 .steady true 0 0
cp_site cp_steady_t_0_1 .steady true 0 1
cp_site cp_steady_t_1_0 .steady true 1 0
cp_site cp_steady_t_1_1 .steady true 1 1
cp_site cp_steady_t_2_0 .steady true 2 0
cp_site cp_steady_t_2_1 .steady true 2 1
cp_site cp_steady_t_3_0 .steady true 3 0
cp_site cp_steady_t_3_1 .steady true 3 1
cp_site cp_steady_t_4_0 .steady true 4 0
cp_site cp_steady_t_4_1 .steady true 4 1
cp_site cp_steady_t_5_0 .steady true 5 0
cp_site cp_steady_t_5_1 .steady true 5 1
cp_site cp_steady_t_6_0 .steady true 6 0
cp_site cp_steady_t_6_1 .steady true 6 1
cp_site cp_steady_t_7_0 .steady true 7 0
cp_site cp_steady_t_7_1 .steady true 7 1
cp_site cp_steady_t_8_0 .steady true 8 0
cp_site cp_steady_t_8_1 .steady true 8 1
cp_site cp_steady_t_9_0 .steady true 9 0
cp_site cp_steady_t_9_1 .steady true 9 1
cp_site cp_steady_t_10_0 .steady true 10 0
cp_site cp_steady_t_10_1 .steady true 10 1
cp_site cp_steady_t_11_0 .steady true 11 0
cp_site cp_steady_t_11_1 .steady true 11 1
cp_site cp_steady_t_12_0 .steady true 12 0
cp_site cp_steady_t_12_1 .steady true 12 1
cp_site cp_steady_t_13_0 .steady true 13 0
cp_site cp_steady_t_13_1 .steady true 13 1
cp_site cp_steady_t_14_0 .steady true 14 0
cp_site cp_steady_t_14_1 .steady true 14 1
cp_site cp_steady_t_15_0 .steady true 15 0
cp_site cp_steady_t_15_1 .steady true 15 1

set_option maxHeartbeats 4000000 in
/-- **No row copy of the steady block is undefined behaviour** at a state that keeps the row-address
pattern. -/
theorem cp_safe_steady (hp : Pre p L m) {b : Bool} {i : Fin 16} {c : Fin 2} {v : V} {kk : Fin 2}
    (hA : AOk v) {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (h : (code p L g w ent).AtD ⟨.cp .steady b i c, v, kk⟩ t)
    (hc : kernel.code[(Site.cp .steady b i c).pc]? = some ins)
    (hf : Fires (Site.cp .steady b i c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (f : Fault) : e.kind ≠ .ub f := by
  cases b <;> fin_cases i <;> fin_cases c
  · exact cp_steady_f_0_0 hp hA h hc hf f
  · exact cp_steady_f_0_1 hp hA h hc hf f
  · exact cp_steady_f_1_0 hp hA h hc hf f
  · exact cp_steady_f_1_1 hp hA h hc hf f
  · exact cp_steady_f_2_0 hp hA h hc hf f
  · exact cp_steady_f_2_1 hp hA h hc hf f
  · exact cp_steady_f_3_0 hp hA h hc hf f
  · exact cp_steady_f_3_1 hp hA h hc hf f
  · exact cp_steady_f_4_0 hp hA h hc hf f
  · exact cp_steady_f_4_1 hp hA h hc hf f
  · exact cp_steady_f_5_0 hp hA h hc hf f
  · exact cp_steady_f_5_1 hp hA h hc hf f
  · exact cp_steady_f_6_0 hp hA h hc hf f
  · exact cp_steady_f_6_1 hp hA h hc hf f
  · exact cp_steady_f_7_0 hp hA h hc hf f
  · exact cp_steady_f_7_1 hp hA h hc hf f
  · exact cp_steady_f_8_0 hp hA h hc hf f
  · exact cp_steady_f_8_1 hp hA h hc hf f
  · exact cp_steady_f_9_0 hp hA h hc hf f
  · exact cp_steady_f_9_1 hp hA h hc hf f
  · exact cp_steady_f_10_0 hp hA h hc hf f
  · exact cp_steady_f_10_1 hp hA h hc hf f
  · exact cp_steady_f_11_0 hp hA h hc hf f
  · exact cp_steady_f_11_1 hp hA h hc hf f
  · exact cp_steady_f_12_0 hp hA h hc hf f
  · exact cp_steady_f_12_1 hp hA h hc hf f
  · exact cp_steady_f_13_0 hp hA h hc hf f
  · exact cp_steady_f_13_1 hp hA h hc hf f
  · exact cp_steady_f_14_0 hp hA h hc hf f
  · exact cp_steady_f_14_1 hp hA h hc hf f
  · exact cp_steady_f_15_0 hp hA h hc hf f
  · exact cp_steady_f_15_1 hp hA h hc hf f
  · exact cp_steady_t_0_0 hp hA h hc hf f
  · exact cp_steady_t_0_1 hp hA h hc hf f
  · exact cp_steady_t_1_0 hp hA h hc hf f
  · exact cp_steady_t_1_1 hp hA h hc hf f
  · exact cp_steady_t_2_0 hp hA h hc hf f
  · exact cp_steady_t_2_1 hp hA h hc hf f
  · exact cp_steady_t_3_0 hp hA h hc hf f
  · exact cp_steady_t_3_1 hp hA h hc hf f
  · exact cp_steady_t_4_0 hp hA h hc hf f
  · exact cp_steady_t_4_1 hp hA h hc hf f
  · exact cp_steady_t_5_0 hp hA h hc hf f
  · exact cp_steady_t_5_1 hp hA h hc hf f
  · exact cp_steady_t_6_0 hp hA h hc hf f
  · exact cp_steady_t_6_1 hp hA h hc hf f
  · exact cp_steady_t_7_0 hp hA h hc hf f
  · exact cp_steady_t_7_1 hp hA h hc hf f
  · exact cp_steady_t_8_0 hp hA h hc hf f
  · exact cp_steady_t_8_1 hp hA h hc hf f
  · exact cp_steady_t_9_0 hp hA h hc hf f
  · exact cp_steady_t_9_1 hp hA h hc hf f
  · exact cp_steady_t_10_0 hp hA h hc hf f
  · exact cp_steady_t_10_1 hp hA h hc hf f
  · exact cp_steady_t_11_0 hp hA h hc hf f
  · exact cp_steady_t_11_1 hp hA h hc hf f
  · exact cp_steady_t_12_0 hp hA h hc hf f
  · exact cp_steady_t_12_1 hp hA h hc hf f
  · exact cp_steady_t_13_0 hp hA h hc hf f
  · exact cp_steady_t_13_1 hp hA h hc hf f
  · exact cp_steady_t_14_0 hp hA h hc hf f
  · exact cp_steady_t_14_1 hp hA h hc hf f
  · exact cp_steady_t_15_0 hp hA h hc hf f
  · exact cp_steady_t_15_1 hp hA h hc hf f

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
