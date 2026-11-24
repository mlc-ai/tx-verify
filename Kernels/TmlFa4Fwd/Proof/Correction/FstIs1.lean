-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.FstIs0
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part133
import Kernels.TmlFa4Fwd.Flow.Code.Part134
import Kernels.TmlFa4Fwd.Flow.Code.Part135
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part138
import Kernels.TmlFa4Fwd.Flow.Code.Part139
import Kernels.TmlFa4Fwd.Flow.Code.Part140
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

/-! # The address of every final store of a correction lane, stage 1

`fst_exact`: element `s` of the store `hh` of chunk `j` of stage `st` is the word `s` of the lane's
column `2 (j mod 4) + hh` in the quarter `j / 4` of the stage's staging buffer. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

fst_is fstIs_1_0_0 1 0 0 0 0
fst_is fstIs_1_0_1 1 0 1 1 0
fst_is fstIs_1_1_0 1 1 0 2 0
fst_is fstIs_1_1_1 1 1 1 3 0
fst_is fstIs_1_2_0 1 2 0 4 0
fst_is fstIs_1_2_1 1 2 1 5 0
fst_is fstIs_1_3_0 1 3 0 6 0
fst_is fstIs_1_3_1 1 3 1 7 0
fst_is fstIs_1_4_0 1 4 0 0 1
fst_is fstIs_1_4_1 1 4 1 1 1
fst_is fstIs_1_5_0 1 5 0 2 1
fst_is fstIs_1_5_1 1 5 1 3 1
fst_is fstIs_1_6_0 1 6 0 4 1
fst_is fstIs_1_6_1 1 6 1 5 1
fst_is fstIs_1_7_0 1 7 0 6 1
fst_is fstIs_1_7_1 1 7 1 7 1
fst_is fstIs_1_8_0 1 8 0 0 2
fst_is fstIs_1_8_1 1 8 1 1 2
fst_is fstIs_1_9_0 1 9 0 2 2
fst_is fstIs_1_9_1 1 9 1 3 2
fst_is fstIs_1_10_0 1 10 0 4 2
fst_is fstIs_1_10_1 1 10 1 5 2
fst_is fstIs_1_11_0 1 11 0 6 2
fst_is fstIs_1_11_1 1 11 1 7 2
fst_is fstIs_1_12_0 1 12 0 0 3
fst_is fstIs_1_12_1 1 12 1 1 3
fst_is fstIs_1_13_0 1 13 0 2 3
fst_is fstIs_1_13_1 1 13 1 3 3
fst_is fstIs_1_14_0 1 14 0 4 3
fst_is fstIs_1_14_1 1 14 1 5 3
fst_is fstIs_1_15_0 1 15 0 6 3
fst_is fstIs_1_15_1 1 15 1 7 3

/-- **The word of every final store**: element `s` of store `hh` of chunk `j`. -/
theorem fst_exact (hp : Pre p L m) {d : Control.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (Control.code p L g).AtD d t)
    (hc : kernel.code[(Control.code p L g).pc d]? = some ins)
    (hf : Fires ((Control.code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    {st : Fin 2} {j : Fin 16} {hh : Fin 2} (hs : d.site = .fst st j hh) {acc : Acc} {bs : List Byte}
    (hk : e.kind = .wr acc bs) :
    FstIs L g st ⟨2 * (j.val % 4) + hh.val, by omega⟩ (j.val / 4) d.k.val acc := by
  fin_cases st <;> fin_cases j <;> fin_cases hh
  · exact fstIs_0_0_0 hp h hc hf hs hk
  · exact fstIs_0_0_1 hp h hc hf hs hk
  · exact fstIs_0_1_0 hp h hc hf hs hk
  · exact fstIs_0_1_1 hp h hc hf hs hk
  · exact fstIs_0_2_0 hp h hc hf hs hk
  · exact fstIs_0_2_1 hp h hc hf hs hk
  · exact fstIs_0_3_0 hp h hc hf hs hk
  · exact fstIs_0_3_1 hp h hc hf hs hk
  · exact fstIs_0_4_0 hp h hc hf hs hk
  · exact fstIs_0_4_1 hp h hc hf hs hk
  · exact fstIs_0_5_0 hp h hc hf hs hk
  · exact fstIs_0_5_1 hp h hc hf hs hk
  · exact fstIs_0_6_0 hp h hc hf hs hk
  · exact fstIs_0_6_1 hp h hc hf hs hk
  · exact fstIs_0_7_0 hp h hc hf hs hk
  · exact fstIs_0_7_1 hp h hc hf hs hk
  · exact fstIs_0_8_0 hp h hc hf hs hk
  · exact fstIs_0_8_1 hp h hc hf hs hk
  · exact fstIs_0_9_0 hp h hc hf hs hk
  · exact fstIs_0_9_1 hp h hc hf hs hk
  · exact fstIs_0_10_0 hp h hc hf hs hk
  · exact fstIs_0_10_1 hp h hc hf hs hk
  · exact fstIs_0_11_0 hp h hc hf hs hk
  · exact fstIs_0_11_1 hp h hc hf hs hk
  · exact fstIs_0_12_0 hp h hc hf hs hk
  · exact fstIs_0_12_1 hp h hc hf hs hk
  · exact fstIs_0_13_0 hp h hc hf hs hk
  · exact fstIs_0_13_1 hp h hc hf hs hk
  · exact fstIs_0_14_0 hp h hc hf hs hk
  · exact fstIs_0_14_1 hp h hc hf hs hk
  · exact fstIs_0_15_0 hp h hc hf hs hk
  · exact fstIs_0_15_1 hp h hc hf hs hk
  · exact fstIs_1_0_0 hp h hc hf hs hk
  · exact fstIs_1_0_1 hp h hc hf hs hk
  · exact fstIs_1_1_0 hp h hc hf hs hk
  · exact fstIs_1_1_1 hp h hc hf hs hk
  · exact fstIs_1_2_0 hp h hc hf hs hk
  · exact fstIs_1_2_1 hp h hc hf hs hk
  · exact fstIs_1_3_0 hp h hc hf hs hk
  · exact fstIs_1_3_1 hp h hc hf hs hk
  · exact fstIs_1_4_0 hp h hc hf hs hk
  · exact fstIs_1_4_1 hp h hc hf hs hk
  · exact fstIs_1_5_0 hp h hc hf hs hk
  · exact fstIs_1_5_1 hp h hc hf hs hk
  · exact fstIs_1_6_0 hp h hc hf hs hk
  · exact fstIs_1_6_1 hp h hc hf hs hk
  · exact fstIs_1_7_0 hp h hc hf hs hk
  · exact fstIs_1_7_1 hp h hc hf hs hk
  · exact fstIs_1_8_0 hp h hc hf hs hk
  · exact fstIs_1_8_1 hp h hc hf hs hk
  · exact fstIs_1_9_0 hp h hc hf hs hk
  · exact fstIs_1_9_1 hp h hc hf hs hk
  · exact fstIs_1_10_0 hp h hc hf hs hk
  · exact fstIs_1_10_1 hp h hc hf hs hk
  · exact fstIs_1_11_0 hp h hc hf hs hk
  · exact fstIs_1_11_1 hp h hc hf hs hk
  · exact fstIs_1_12_0 hp h hc hf hs hk
  · exact fstIs_1_12_1 hp h hc hf hs hk
  · exact fstIs_1_13_0 hp h hc hf hs hk
  · exact fstIs_1_13_1 hp h hc hf hs hk
  · exact fstIs_1_14_0 hp h hc hf hs hk
  · exact fstIs_1_14_1 hp h hc hf hs hk
  · exact fstIs_1_15_0 hp h hc hf hs hk
  · exact fstIs_1_15_1 hp h hc hf hs hk

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
