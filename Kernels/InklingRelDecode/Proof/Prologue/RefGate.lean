-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.PreloadCount
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open Control

def Site.block : Site → Option (Fin 3)
  | .pb b _ | .arr b | .lb b _ | .psh b | .pel b _ | .ptc b _ => some b
  | _ => none

def OpenBlock (d : D) (n : Nat) : Prop := ∀ b, d.site.block = some b → b.val<n

private theorem query_block (t d k) : (querySite t d k).block = none := by
  unfold querySite; split_ifs <;> rfl

private theorem later_blocks (d : D) (t n : Nat) (b : Fin 3) (j : Fin 4) (h : b.val<n) :
    ∀ b', (afterCopy d t n b j).block = some b' → b'.val<n := by
  intro b' eq
  fin_cases j <;> simp only [afterCopy] at eq
  all_goals repeat' split at eq
  all_goals first | (rw [query_block] at eq; contradiction) |
    (obtain rfl := Option.some.inj eq; first | exact h | (change _+1 < n; omega))

private theorem store_block (i j) : (Control.afterStore i j).block = none := by
  revert i j; decide +kernel

theorem gate_next {Q L g d dn e} (hn : Control.next Q L g d e = some (some dn))
    (ok : OpenBlock d (preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d)) :
    OpenBlock dn (preload Q.splits ((L.ctaidOf (g/L.block)).get .x) dn) := by
  obtain ⟨s,f,l,v,w⟩ := d
  intro b' eq
  cases s <;> simp only [Control.next] at hn
  all_goals repeat' split at hn
  all_goals try contradiction
  all_goals cases hn
  all_goals dsimp only at eq
  all_goals first
    | contradiction
    | (rw [query_block] at eq; contradiction)
    | (unfold afterInit at eq; split at eq <;> contradiction)
    | (exact later_blocks _ _ _ _ _ (ok _ rfl) _ eq)
    | (unfold afterQuery at eq; split at eq <;> try contradiction
       split at eq <;> first | contradiction | (rw [query_block] at eq; contradiction))
    | (rw [store_block] at eq; contradiction)
    | (obtain rfl := Option.some.inj eq; apply ok; rfl)
    | (obtain rfl := Option.some.inj eq; change 0 < _; exact Nat.pos_of_ne_zero (by assumption))
    | (casesm* Site.pb _ _ = Site.pb _ _, Site.lb _ _ = Site.lb _ _
       obtain rfl := Option.some.inj eq; exact ok _ rfl)

end PTX.Kernels.InklingRelDecode.Proof.Prologue
