-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCounts
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # `Counts`: the data of the final part, the chunks

Which step leads into a site of the chunk conjuncts: a final chunk's wait follows its load (which
sets the chunk's values), its stores follow the wait (which checks the products) or an earlier
store; every other step keeps the values and the item (`pre_finChunk`, `pre_fst`). The tactic
`corr_cases` splits a step on the site and the transition. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

theorem snoc_take {es : List Event} {e : Event} {r : Nat} (h : r ≤ es.length) :
    (es ++ [e]).take r = es.take r := List.take_append_of_le_length h

theorem snoc_get {es : List Event} {e : Event} {r : Nat} (h : r < es.length) :
    (es ++ [e])[r]? = es[r]? := List.getElem?_append_left h

theorem snoc_last {es : List Event} {e : Event} : (es ++ [e])[es.length]? = some e := by simp

/-- Split a step on the site and the transition. -/
syntax "corr_cases" ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| corr_cases $hn) => `(tactic| (
      rcases site with _ | _ | st0 | ⟨st0, gen⟩ | a0 | st0 | st0 | ⟨st0, j0⟩ | ⟨st0, j0⟩ |
        ⟨st0, j0⟩ | st0 | ⟨st0, fin⟩ | st0 | st0 | st0 | ⟨st0, j0⟩ | ⟨st0, j0⟩ |
        ⟨st0, j0, h0, el0⟩ | st0 | st0 | _ | _ | _
      all_goals (try fin_cases st0)
      all_goals (try fin_cases a0)
      all_goals (try cases gen)
      all_goals (try cases fin)
      all_goals simp only [next, nextItem, afterTrip] at $hn:ident
      all_goals repeat' (first | split_ifs at $hn:ident | split at $hn:ident)
      all_goals (try simp only [Option.some.injEq, reduceCtorEq] at $hn:ident)
      all_goals (try subst $hn:ident)))

set_option maxHeartbeats 8000000 in
theorem pre_finChunk {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) {st : Fin 2} {j : Fin 8} (h : finChunk d' st j) :
    ((d.site = .fld st j ∧ ∃ a, e.kind = .tc (.ld a d'.o .s32x32b)) ∨
      (finChunk d st j ∧ d'.o = d.o)) ∧
      d'.i = d.i := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  unfold finChunk at h ⊢
  corr_cases hn
  all_goals (try (simp at h; done))
  all_goals first
    | (exfalso; simp_all; done)
    | simp_all

set_option maxHeartbeats 8000000 in
theorem pre_fst {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) {st : Fin 2} {j : Fin 8} {h : Fin 2} {el : Fin 4}
    (hs : d'.site = .fst st j h el) :
    ((d.site = .fldW st j ∧ finOk d.o (fcPair d) = true) ∨ ∃ h' el', d.site = .fst st j h' el') ∧
      d'.o = d.o ∧ d'.aw = d.aw := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  corr_cases hn
  all_goals (try (simp at hs; done))
  all_goals first
    | (exfalso; simp_all; done)
    | simp_all


theorem pre_fenced {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) (st : Fin 2) :
    (d'.site = .oFree st true → d.site = .fence st) ∧
      (d'.site = .staged st → d.site = .oFree st true) := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  corr_cases hn
  all_goals simp_all

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
