-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.step_load
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.Wait
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.step_loadWait_15

@[expose] public section

/-! # The consumer warps' load steps

A Tensor Memory load appends its sixteen values to the accumulator, and the wait of load `j`
converts them and reaches load `j + 1` (or the thread faults when a value does not read as a
single-precision float); after the last load the acknowledgement's `mapa` and
the arrival on the accumulator barrier are reached. Each load's destination registers are a
table (`ldRegs`) that the code confirms, so the register facts of the successor state are
closed for every `j` at once. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- The accumulator wait of load `j`: its values are converted and load `j + 1` is reached, or
after the last load the arrival on the accumulator barrier. -/
theorem step_loadWait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads) (hw : tidOf L g < 256)
    (j : Fin 16) (hs : d.site = .loadWait j) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    (next L g d e = some none ∨
      ∃ d' t', next L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
          Inv d') ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) := by
  by_cases hj : j.val + 1 < 16
  · exact step_loadWait_lt j hj hs hi h hc hf
  · obtain rfl : j = 15 := Fin.ext (by have := j.isLt; omega)
    exact step_loadWait_15 hpre hg hw hs hi h hc hf

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
