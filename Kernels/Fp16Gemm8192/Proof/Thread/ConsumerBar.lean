-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOut
public import Lemmas.Flow.EndSite

@[expose] public section

/-! # A consumer at a named barrier can arrive

A consumer thread at its group's CLC barrier or at a slice's output barrier can perform the
arrival there, on a barrier below 16 with its group's 128 threads (`cons_bar_fire`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- At a named barrier site the arrival's template is the arrival on the site's barrier. -/
theorem bar_tmpl (hpre : Pre P L mem0) {d : D} {t : TState}
    (hat : (code L g).AtD (.inr (.cons d)) t)
    (hs : d.site = .clcBar ∨ (∃ k, d.site = .barA k) ∨ ∃ k, d.site = .barB k) :
    ∃ ins id t', kernel.code[d.site.pc]? = some ins ∧
      eventTmpl Prod L g t ins.op = .bar id t' (some 128) := by
  have hblock := hpre.block
  have htid : tidOf L g < 384 := by rw [← hblock]; exact Nat.mod_lt _ (by omega)
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hat ⊢
  rcases hs with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · obtain ⟨t', ht'⟩ := tmpl_barN (A := Prod) (L := L) (g := g) (t := t) (r := 145)
      (id := tidOf L g / 32 / 4 + 1) (n := 128)
      ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values))) (by omega) (by decide) (by decide) (by decide) (by omega)
    exact ⟨_, _, t', Flow.code_bar_0, ht'⟩
  all_goals fin_cases k
  all_goals
    obtain ⟨t', ht'⟩ := tmpl_barN (A := Prod) (L := L) (g := g) (t := t) (r := 435)
      (id := tidOf L g / 32 / 4 + 10) (n := 128)
      ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values))) (by omega) (by decide) (by decide) (by decide) (by omega)
  · exact ⟨_, _, t', Flow.code_bar_1, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_3, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_5, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_7, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_9, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_11, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_13, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_15, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_2, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_4, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_6, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_8, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_10, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_12, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_14, ht'⟩
  · exact ⟨_, _, t', Flow.code_bar_16, ht'⟩

end Consumer

/-- **A consumer at a named barrier can arrive on it.** -/
theorem cons_bar_fire {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {es : List Event} {c : Consumer.D} {t : TState}
    (hσ : (code L g).toMachine.after (some (code L g).init) es = some (some (.inr (.cons c))))
    (hs : c.site = .clcBar ∨ (∃ k, c.site = .barA k) ∨ ∃ k, c.site = .barB k)
    (hr : Run kernel Prod L g {} es (some t)) :
    ∃ t1 u id, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨t1.pc, .bar id (some 128)⟩ (some u) := by
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ
  have hout := Code.site_out (sound hpre hg) hgood
  obtain ⟨ins, id, t', hc, ht'⟩ := Consumer.bar_tmpl hpre hgood.1 hs
  simp only [Code.tmpl, hc, ht'] at hout
  exact ⟨t1, t', id, hl, _, hout, rfl, rfl⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
