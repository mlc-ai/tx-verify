-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutEvents
public import Lemmas.Flow.EndSite

@[expose] public section

/-! # A consumer at a drain can wait

A consumer thread at one of its slices' drains or at its final drain can perform its bulk-group wait
(`cons_bulk_fire`): the instruction at the site is a bulk wait. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

namespace Consumer

/-- The instruction at a drain site is a bulk-group wait. -/
theorem bulk_op {d : D} {ins : Instr} (hc : kernel.code[d.site.pc]? = some ins)
    (hs : (∃ k, d.site = .drain k) ∨ d.site = .finalDrain) :
    ∃ mode n, ins.op = .bulkWait mode n := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc ⊢
  rcases hs with ⟨k, rfl⟩ | rfl
  · fin_cases k <;> code_at hc <;> subst hc <;> exact ⟨_, _, rfl⟩
  · code_at hc
    subst hc
    exact ⟨_, _, rfl⟩

end Consumer

/-- **A consumer at a drain can perform its bulk-group wait.** -/
theorem cons_bulk_fire {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {es : List Event} {c : Consumer.D} {t : TState}
    (hσ : (code L g).toMachine.after (some (code L g).init) es = some (some (.inr (.cons c))))
    (hs : (∃ k, c.site = .drain k) ∨ c.site = .finalDrain)
    (hr : Run kernel Prod L g {} es (some t)) :
    ∃ t1 u mode n, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨t1.pc, .bulkWait mode n⟩ (some u) := by
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ
  have hout := Code.site_out (sound hpre hg) hgood
  obtain ⟨ins, hc, -⟩ := ((sound hpre hg).steps (.inr (.cons c))).site hgood.2
  obtain ⟨mode, n, hop⟩ := Consumer.bulk_op (d := c) hc hs
  simp only [Code.tmpl, hc, hop] at hout
  exact ⟨t1, next t1, mode, n, hl, _, hout, rfl, rfl⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
