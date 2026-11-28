-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Inp

@[expose] public section

/-! # A typed value state stays typed

The step of the value machine keeps the typing of its words (`VTyp`) when the bias word a load
returns is a bias word and the scores the score load returns are numbers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow Control

noncomputable section

theorem bw_dflt : Bw dflt := Or.inr rfl

theorem bw_update {f : Nat → Value} (hf : ∀ j, Bw (f j)) {i : Nat} {x : Value} (hx : Bw x)
    (j : Nat) : Bw (Function.update f i x j) := by
  by_cases h : j = i
  · subst h; simpa using hx
  · simpa [Function.update, h] using hf j

/-- **The step keeps the words typed**, given the events that load words. -/
theorem vtyp_step {L : Launch} {d : D} {ev : Event} {s : Site} (hv : VTyp d.v)
    (hb : (∃ j, d.c.site = .pre j ∨ d.c.site = .nxt j) → ∀ a bs, ev.kind = .rd a bs →
      Bw (Lib.loadWord bs))
    (hs : d.c.site = .ldS → ∀ a vals sh, ev.kind = .tc (.ld a vals sh) → ∀ x ∈ vals,
      SK.fl.Has x) : VTyp (record L d ev s) := by
  obtain ⟨hc, hl, hsc⟩ := hv
  unfold record
  split
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals first
    | exact ⟨hc, hl, hsc⟩
    | exact ⟨fun _ => bw_dflt, fun _ => bw_dflt, hsc⟩
    | exact ⟨hc, fun _ => bw_dflt, hsc⟩
    | exact ⟨hl, fun _ => bw_dflt, hsc⟩
    | exact ⟨hc, hl, hs ‹_› _ _ _ ‹_›⟩
    | (have hw := hb ⟨_, .inl ‹d.c.site = _›⟩ _ _ ‹_›
       first
        | exact ⟨bw_update hl hw, fun _ => bw_dflt, hsc⟩
        | exact ⟨hc, bw_update hl hw, hsc⟩)
    | (have hw := hb ⟨_, .inr ‹d.c.site = _›⟩ _ _ ‹_›
       exact ⟨hc, bw_update hl hw, hsc⟩)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
