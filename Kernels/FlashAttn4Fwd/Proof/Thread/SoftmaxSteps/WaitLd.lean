-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.LoadBase
public import Lemmas.Flow.WaitLdAt

@[expose] public section

/-! # The implicit wait of a score load

At a load's sub-step 1 (`ldW`) the thread performs the implicit `tcgen05.wait::ld`
(ASM-TCLD-DATAFLOW) and continues at the next instruction's first sub-step with the facts of
the wait's state (`ldW_at`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A concrete state of a softmax state: at its site's `pc` and sub-step, with its facts. -/
abbrev AtS (L : Launch) (g : Nat) (d : D) (t : TState) : Prop :=
  t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
    Holds t.regs (facts L g d)

/-- The instruction of a load's wait is the load. -/
theorem code_ldW (lp : Bool) (c : Fin 4) :
    ∃ ds ta, kernel.code[(Site.ldW lp c).pc]? = some ⟨none, .tcLd ds ta⟩ := by
  cases lp <;> rcases fin4_cases c with rfl | rfl | rfl | rfl
  · exact ⟨_, _, Flow.code_tmemLoad_0⟩
  · exact ⟨_, _, Flow.code_tmemLoad_1⟩
  · exact ⟨_, _, Flow.code_tmemLoad_2⟩
  · exact ⟨_, _, Flow.code_tmemLoad_3⟩
  · exact ⟨_, _, Flow.code_tmemLoad_4⟩
  · exact ⟨_, _, Flow.code_tmemLoad_5⟩
  · exact ⟨_, _, Flow.code_tmemLoad_6⟩
  · exact ⟨_, _, Flow.code_tmemLoad_7⟩

/-- The implicit wait of load `c`: the event is `tcgen05.wait::ld`, and the thread is at the
next instruction with the facts of the wait's state. -/
theorem ldW_at {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    {lp : Bool} {c : Fin 4} (hs : d.site = .ldW lp c) (h : AtS L g d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    e = ⟨d.site.pc, .tc .waitLd⟩ ∧ At u (d.site.pc + 1) (facts L g d) := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain ⟨ds, ta, hc'⟩ := code_ldW lp c
  obtain rfl := Option.some.inj (hc.symm.trans hc')
  have hw : asms.any (·.tcLdWait (Site.ldW lp c).pc) = true := by
    cases lp
    · exact tcLdWait_ld false c
    · exact tcLdWait_ld true c
  exact waitLd_at hw h.1 (by rw [h.2.1]; simp [Site.sub]) h.2.2.1 h.2.2.2.1 h.2.2.2.2 hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
