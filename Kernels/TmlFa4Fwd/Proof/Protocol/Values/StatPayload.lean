-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.SoftStats
import Lemmas.Flow.FloatOutcome
import Lemmas.Flow.Step.RuleStep

@[expose] public section

/-! # What the correction lanes' statistics reads return

Once the Tensor Memory loads of its CTA before it returned numbers, a scale read returns a factor's
word (`scale_payload`), a final read of the row sum a nonnegative number (`sum_payload`), and one of
the row maximum an extended real below `+∞` (`max_payload`): the source store precedes the read, so
the loads before the store did too. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (Site)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {y j : Nat} {a : Acc}
  {bs : List (Option Byte)} {st : Fin 2}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (h8 : 8 ≤ Prologue.warpIndex L y) (h12 : Prologue.warpIndex L y < 12)
  (hL : LoadsBefore L X (y, j))
include hp hX hFw h8 h12 hL

omit hp hX hFw h8 h12 in
private theorem before_source {h i : Nat} (hc : h / L.block = y / L.block)
    (hbc : baseCausality L X (h, i) (y, j)) : LoadsBefore L X (h, i) :=
  fun f a vals hld hfc hf => hL f a vals hld (hfc.trans hc) (.tail hf (.inl hbc))

/-- **A scale read returns a factor's word.** -/
theorem scale_payload (he : X.get (y, j) = some ⟨(Site.rscale st).pc, .rd a bs⟩) :
    ∃ w x, ScaleWord w x ∧ rebuild 3 bs = .ok w := by
  obtain ⟨h, i, pcw, aw, ws, A, N, -, -, hw, hc, -, -, hg, -, -, -, hbc, hbs, -, hA, hN, -,
    hlt, -⟩ := stat_store hp hX hFw h8 h12 he (s := .rscale st) rfl
  obtain ⟨w, hW, hws⟩ := factor_bytes_at hp hX hFw hw hg (before_source hL hc hbc) hN
    (by rw [hA]; exact hlt (stat_sites st).1)
  exact ⟨w, _, hW, rebuild_word hW.bytes hW.scalar hws hbs⟩

/-- **A final read of the row sum returns a nonnegative number.** -/
theorem sum_payload (he : X.get (y, j) = some ⟨(Site.fsum st).pc, .rd a bs⟩) :
    ∃ x : ℝ, 0 ≤ x ∧ rebuild 3 bs = .ok (.float .f32 x) := by
  obtain ⟨h, i, pcw, aw, ws, A, N, -, -, hw, hc, -, -, hg, -, hlw, -, hbc, hbs, -, hA, hN, htl,
    -⟩ := stat_store hp hX hFw h8 h12 he (s := .fsum st) rfl
  obtain ⟨x, hx, hws⟩ := sum_word_at hp hX hFw hw hg (before_source hL hc hbc) hN hlw
    (hA.trans (htl (stat_sites st).2.1))
  exact ⟨x, hx, rebuild_word rfl rfl hws hbs⟩

/-- **A final read of the row maximum returns a value below `+∞`.** -/
theorem max_payload (he : X.get (y, j) = some ⟨(Site.fmax st).pc, .rd a bs⟩) :
    ∃ x : EReal, x ≠ ⊤ ∧ rebuild 3 bs = .ok (Assumption.erealValue .f32 x) := by
  obtain ⟨h, i, pcw, aw, ws, A, N, -, -, hw, hc, -, -, hg, -, hlw, -, hbc, hbs, -⟩ :=
    stat_store hp hX hFw h8 h12 he (s := .fmax st) rfl
  obtain ⟨x, hx, hws⟩ := max_word_at hp hX hFw hw hg (before_source hL hc hbc) hlw
  refine ⟨x, hx, rebuild_word (erealValue_f32_bytes x) ?_ hws hbs⟩
  induction x using EReal.rec with
  | bot => rw [erealValue_f32_bot]; rfl
  | coe x => rw [erealValue_coe]; rfl
  | top => exact absurd rfl hx

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
