-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.load_value

@[expose] public section

/-! One step of `ConsumerLoad`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- The facts after a load: its destinations hold its values, and the other live registers
keep theirs. -/
theorem load_facts {L : Launch} {g : Nat} {m n m' n' cp ap : Nat} {resp : Value} {x : Nat}
    {acc : Nat → Value} {xs : List Value} {base : Value} {R R' : Nat → Option Value} (j : Fin 16)
    (hS : Holds R (facts L g ⟨.load j, m, n, m', n', cp, ap, resp, x, acc, base⟩))
    (hframe : ∀ r, r ∉ ldRegs j → R' r = R r)
    (hW : Holds R' (Flow.factsFrom (ldRegs j)
      (valueOf L g ⟨.loadWait j, m, n, m', n', cp, ap, resp, x, loadAcc acc j.val xs, base⟩))) :
    Holds R' (facts L g ⟨.loadWait j, m, n, m', n', cp, ap, resp, x, loadAcc acc j.val xs, base⟩) :=
      by
  fin_cases j
  all_goals
    frame_fp hS, hframe
    exact Flow.holds_factsFrom_mono hW (by lit_mem)

/-- A Tensor Memory load: its sixteen values become the accumulator's entries of the load, and
the wait of the same load is reached. -/
theorem step_load {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (j : Fin 16) (hs : d.site = .load j) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    load_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans (code_load j))
  obtain ⟨_, vals, hlen, rfl, rfl⟩ := fires_tcLd (by intro s h; cases h) hf
  right
  have hxl : vals.length = 16 := by rw [hlen, ldRegs_len]
  have hpc : (PTX.next t).pc = (Site.loadWait j).pc := by
    show t.pc + 1 = (Site.loadWait j).pc
    rw [h.1, pc_wait j]
  refine ⟨⟨.loadWait j, m, n, m', n', cp, ap, resp, x, loadAcc acc j.val vals, base⟩,
    setRegs (PTX.next t) (ldRegs j) vals, by simp [next],
    Relation.ReflTransGen.refl,
    at_setRegs (PTX.next t) (ldRegs j) vals hpc h.2.1 h.2.2.1
      h.2.2.2.1 (load_facts j h.2.2.2.2
        (fun r hr => setRegs_other (PTX.next t) (ldRegs j) _ r hr)
        (holds_setRegs _ _ vals _ (ldRegs_nodup j) (by rw [hxl, ldRegs_len])
          (load_value L g _ m n m' n' cp ap resp x acc vals base j))),
    ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7⟩⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
