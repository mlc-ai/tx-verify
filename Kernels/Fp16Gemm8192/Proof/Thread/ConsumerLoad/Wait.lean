-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.CvtTable

@[expose] public section

/-! # The wait of loads `0` to `14`

The wait of load `j` is followed by the conversions of its values (`loadWait_conv`), which
end at load `j + 1`; when a value does not read as a single-precision float the thread is
dead. One proof for every `j`: the conversions are the generated runs (`cvtTable`), and the
state after them has the facts of load `j + 1` because the value table does not depend on
which of the two sites the state is at. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- Every load's wait is the Tensor Memory wait (the generated lookups of the wait sites). -/
theorem code_wait : ∀ j : Fin 16,
    kernel.code[(Site.loadWait j).pc]? = some ⟨none, .tcWaitLd⟩ := by
  intro j
  fin_cases j
  exacts [Flow.code_tmemWait_0, Flow.code_tmemWait_1, Flow.code_tmemWait_2, Flow.code_tmemWait_3,
    Flow.code_tmemWait_4, Flow.code_tmemWait_5, Flow.code_tmemWait_6, Flow.code_tmemWait_7,
    Flow.code_tmemWait_8, Flow.code_tmemWait_9, Flow.code_tmemWait_10, Flow.code_tmemWait_11,
    Flow.code_tmemWait_12, Flow.code_tmemWait_13, Flow.code_tmemWait_14, Flow.code_tmemWait_15]

/-- The conversions after load `j`'s wait end at load `j + 1`. -/
theorem pc_after_wait : ∀ j : Fin 16, (h : j.val + 1 < 16) →
    (Site.loadWait j).pc + 9 = (Site.load ⟨j.val + 1, h⟩).pc := by
  decide +kernel

/-- The value table is the same at a load's wait and at a load. -/
theorem valueOf_wait_load (L : Launch) (g : Nat) (j j' : Fin 16) (m n m' n' cp ap : Nat)
    (resp : Value) (x : Nat) (acc : Nat → Value) (base : Value) :
    valueOf L g ⟨.loadWait j, m, n, m', n', cp, ap, resp, x, acc, base⟩ =
      valueOf L g ⟨.load j', m, n, m', n', cp, ap, resp, x, acc, base⟩ := by
  funext r
  simp only [valueOf, values, reduceCtorEq, decide_false]

set_option maxHeartbeats 4000000 in
/-- The wait of load `j < 15`: the conversions of its values and load `j + 1`, or a dead
thread when a value does not convert. -/
theorem step_loadWait_lt {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event}
    {ins : Instr} (j : Fin 16) (hj : j.val + 1 < 16) (hs : d.site = .loadWait j) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    (next L g d e = some none ∨
      ∃ d' t', next L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
          Inv d') ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans (code_wait j))
  obtain rfl := fires_async_next (show AsyncAdvancesOp PTX.Op.tcWaitLd from trivial) hf
  have hconv := loadWait_conv (L := L) (g := g)
    (d := ⟨.loadWait j, m, n, m', n', cp, ap, resp, x, acc, base⟩) (cvtTable j) rfl h
  cases hok : chunkOk acc j with
  | false => exact .inr ⟨by simp [next, hok], hconv.2 hok⟩
  | true =>
    obtain ⟨t9, hr9, ht9⟩ := hconv.1 hok
    have hpc := pc_after_wait j hj
    refine .inl (.inr ⟨⟨.load ⟨j.val + 1, hj⟩, m, n, m', n', cp, ap, resp, x, acc, base⟩, t9,
      by simp [next, hok, hj], run_rtg hr9, ?_, ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7⟩⟩)
    show At t9 (Site.load ⟨j.val + 1, hj⟩).pc (factsAt L g (Site.load ⟨j.val + 1, hj⟩).pc _)
    rw [← hpc]
    simpa only [factsAt, valueOf_wait_load L g j ⟨j.val + 1, hj⟩] using ht9

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
