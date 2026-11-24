-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

open PTX.Flow PTX.Proof

noncomputable section

/-- Score loads read one of the two 32-column token halves. -/
def scoreLoadColumn (part : Fin 2) : Nat := 400 + 32 * part.val

private def scoreLoadBase (arm part : Fin 2) : Nat :=
  ([[986, 987], [984, 985]].getD arm.val []).getD part.val 0

/-- Recover the defined score-load template at the indexed arm and half. -/
theorem scoreLoad_site_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) {d : D} {arm part : Fin 2} {t : TState} {ins : Instr}
    (hd : d.site = .scoreLoad arm part) (ha : (Wg0.code P L g).AtD d t)
    (hCode : kernel.code[d.site.pc]? = some ins) :
    ∃ k, eventTmpl asms L g t ins.op = .tcLd (scoreLoadColumn part) 32 .s32x32b k := by
  let regs := scoreDsts (arm.val == part.val)
  have hc : kernel.code[(Site.scoreLoad arm part).pc]? =
      some ⟨none, .tcLd regs (scoreLoadBase arm part) .s32x32b none⟩ := by
    fin_cases arm <;> fin_cases part
    · exact Flow.code_278
    · exact Flow.code_280
    · exact Flow.code_283
    · exact Flow.code_285
  have hvalid : scoreLoadColumn part = 400 ∨ scoreLoadColumn part = 432 := by
    fin_cases part <;> decide
  have hn : regs.length = 32 := by simp [regs, scoreDsts]
  rw [hd] at hCode
  obtain rfl := Option.some.inj (hCode.symm.trans hc)
  have hr : t.regs (scoreLoadBase arm part) = some (b32 (scoreLoadColumn part)) := by
    have h := reg_value ha (r := scoreLoadBase arm part) (by
      rw [hd]
      fin_cases arm <;> fin_cases part <;> decide +kernel)
    rw [h]
    fin_cases arm <;> fin_cases part <;> rfl
  refine ⟨fun words => setRegs (PTX.next t) regs words, ?_⟩
  rw [scoreLoad_template hpre hvalid hn hr, hn]

/-- Recover the exact score-load address and full register vector from a fired role event. -/
theorem fired_scoreLoad_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) {d : D} {arm part : Fin 2} {e : Event} {u : TState}
    (hd : d.site = .scoreLoad arm part)
    (hf : (Wg0.code P L g).toMachine.Fired (some d) e (some u)) :
    ∃ words, words.length = 32 ∧ e.kind = .tc (.ld (scoreLoadColumn part) words .s32x32b) := by
  obtain ⟨t, ht, he⟩ := hf
  change (Wg0.code P L g).AtD d t ∧ Inv P L g d at ht
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl asms L g t ins.op
    | none => .ub .pcOutOfRange) e (some u) at he
  cases hCode : kernel.code[d.site.pc]? with
  | none => simp [hCode, Fires] at he
  | some ins =>
    obtain ⟨k, hk⟩ := scoreLoad_site_template hpre hd ht.1 hCode
    rw [hCode] at he
    change Fires t.pc (eventTmpl asms L g t ins.op) e (some u) at he
    rw [hk] at he
    obtain ⟨words, hn, he, _⟩ := he
    exact ⟨words, hn, congrArg Event.kind he⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
