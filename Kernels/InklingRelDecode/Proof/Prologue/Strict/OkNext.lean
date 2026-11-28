-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Wf

@[expose] public section

/-! # `Ok` is closed under the machine's steps on well-formed events -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow Control

variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {e : Event}

/-- Outside the broadcast the successor keeps the broadcast word. -/
theorem next_bcast {c c' : Control.D} (hn : Control.next Q L g c e = some (some c'))
    (h : ∀ b, c.site ≠ .psh b) : c'.broadcast = c.broadcast := by
  obtain ⟨s, f, l, q, n, bc⟩ := c
  cases s <;> simp only [Control.next] at hn
  all_goals try exact absurd rfl (h _)
  all_goals repeat' split at hn
  all_goals first | contradiction | (cases hn; rfl) | cases hn

/-- **The step on a well-formed event keeps `Ok`.** -/
theorem ok_next {d d' : Data.D} (hk : Ok Q L g d) (hw : Wf Q L g e) (hpc : e.pc = d.c.site.pc)
    (hn : (Data.code Q L g w).next d e = some (some d')) : Ok Q L g d' := by
  obtain ⟨c', hc, rfl⟩ : ∃ c', Control.next Q L g d.c e = some (some c') ∧
      d' = ⟨c', Data.record d e⟩ := by
    change (Control.next Q L g d.c e).map _ = _ at hn
    rcases h : Control.next Q L g d.c e with _ | _ | c' <;> rw [h] at hn <;> simp at hn
    exact ⟨c', rfl, hn.symm⟩
  obtain ⟨hknown, ⟨x, hx⟩, hpay, hq⟩ := hk
  obtain ⟨w1, w2, w3, w4⟩ := hw
  obtain ⟨⟨s, f, l, q, n, bc⟩, vs⟩ := d
  obtain ⟨pc, kd⟩ := e
  dsimp only at hpc hknown hx hpay hq hc ⊢
  subst hpc
  refine ⟨known_next hknown hc fun j hs a bs he => w1 j (hs ▸ rfl) a bs he, ?_, ?_, ?_⟩
  · by_cases hp : ∃ b, s = .psh b
    · obtain ⟨b, rfl⟩ := hp
      cases kd <;> simp only [Control.next] at hc <;> cases hc <;>
        first | exact ⟨x, hx⟩ | exact w4 b rfl _ _ _ _ _ _ rfl
    · exact ⟨x, (next_bcast hc fun b h => hp ⟨b, h⟩).trans hx⟩
  · intro b h
    simp only [Data.record]
    split
    · next b0 h0 a bs =>
      obtain ⟨p, hp⟩ := w2 b0 h0 rfl a bs rfl
      have hl : Data.loadVal bs = b32 p := by simp only [Data.loadVal, hp]; rfl
      by_cases h1 : b = b0
      · subst h1
        by_cases h2 : h = h0
        · subst h2
          exact ⟨BitVec.ofNat 64 p, by simp [hl, b32]⟩
        · simpa [Function.update_apply, h2] using hpay b h
      · simpa [Function.update_apply, h1] using hpay b h
    · exact hpay b h
    · exact hpay b h
  · simp only [Data.record]
    split
    · exact hq
    · next j a bs =>
      obtain ⟨v, hv, hb⟩ := w3 j rfl a bs rfl
      have hl : Data.loadVal bs = v := by simp only [Data.loadVal, hv]; rfl
      intro k
      by_cases hk : k = j
      · subst hk
        simpa [hl] using hb
      · simpa [Function.update_apply, hk] using hq k
    · exact hq

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
