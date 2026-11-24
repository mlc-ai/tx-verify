-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CodeU

@[expose] public section

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {B C : Code K A L g}

/-- Reuse a strict site whose incoming facts are unchanged. Only successors actually selected
by the strict step must project their concrete facts onto the control state. -/
theorem StepAt.projectU {d : B.D} {q : C.D} (h : B.StepAt d) (f : B.D → C.D)
    (hp : C.pc q = B.pc d) (hF : C.facts q = B.facts d)
    (hs : C.sub q = B.sub d) (ha : C.acc q = B.acc d) (hi : C.inv q → B.inv d)
    (hn : ∀ e, C.next q e = (B.next d e).map (Option.map f))
    (hout : ∀ e d' t, B.next d e = some (some d') → B.Good (some d') t →
      C.Good (some (f d')) t) : C.StepAtU q where
  site := by
    intro hq
    simpa only [hp, hF] using h.site (hi hq)
  step := by
    intro t e u ins ht hq hc hf
    rw [hp] at hc hf
    have ht' : B.AtD d t := ⟨ht.1.trans hp, ht.2.1.trans hs, ht.2.2.1.trans ha,
      ht.2.2.2.1, hF ▸ ht.2.2.2.2⟩
    rcases h.step ins ht' (hi hq) hc hf with (hx | ⟨d', t', hx, hl, hg⟩) | ⟨hx, hd⟩
    · exact .inl (.inl (by rw [hn, hx]; rfl))
    · exact .inl (.inr ⟨f d', t', by rw [hn, hx]; rfl, hl, .inl (hout e d' t' hx hg)⟩)
    · exact .inr ⟨by rw [hn, hx]; rfl, hd⟩

end PTX.Flow.Code
