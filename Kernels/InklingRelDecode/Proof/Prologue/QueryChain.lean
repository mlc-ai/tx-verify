-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Route
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX Control

/-- The position of a site in the chain of the query stores up to the releasing barrier
(`stq 0 0` is 1, `bar18` is 37); zero elsewhere. -/
def storeTail : Site → Nat
  | .stq i j => 4 * i.val + j.val + 1
  | .fnc1 => 33
  | .st8 => 34
  | .st9 j => 35 + j.val
  | .bar18 => 37
  | _ => 0

private theorem query (t d n) : storeTail (querySite t d n) ≤ 1 := by
  simp only [querySite]
  split_ifs <;> decide

private theorem copy (d t n b j) : storeTail (afterCopy d t n b j) ≤ 1 := by
  fin_cases j <;> dsimp only [afterCopy] <;> repeat' split
  all_goals first | exact query .. | simp [storeTail]

private theorem load (d t i) : storeTail (afterQuery d t i) ≤ 1 := by
  simp only [afterQuery]
  split_ifs <;> first | exact query .. | simp [storeTail]

private theorem store : ∀ i j, storeTail (Control.afterStore i j) = storeTail (.stq i j) + 1 := by
  decide +kernel

/-- A step enters the chain at its first site or moves one place along it. -/
theorem storeTail_next {Q L g d ev dn} (hn : Control.next Q L g d ev = some (some dn)) :
    storeTail dn.site ≤ 1 ∨ storeTail dn.site = storeTail d.site + 1 := by
  obtain ⟨s,a,b,c,w⟩ := d
  by_cases h9 : ∃ j, s = .st9 j
  · obtain ⟨j, rfl⟩ := h9
    fin_cases j <;> (simp only [Control.next] at hn; cases hn; right; rfl)
  cases s <;> simp only [Control.next] at hn
  all_goals try exact absurd ⟨_, rfl⟩ h9
  all_goals repeat' split at hn
  all_goals first | contradiction | cases hn
  all_goals first
    | (left; simp [storeTail]; done)
    | (right; rfl)
    | (left; apply query)
    | (left; apply copy)
    | (left; apply load)
    | (right; apply store)
    | (left; unfold afterInit; split <;> simp [storeTail])

/-- The site at a position of the chain. -/
def chainSite (n : Nat) : Site :=
  if h : n < 32 then .stq ⟨n / 4, by omega⟩ ⟨n % 4, by omega⟩
  else if n = 32 then .fnc1 else if n = 33 then .st8 else if n = 34 then .st9 0
  else if n = 35 then .st9 1 else .bar18

theorem storeTail_chain : ∀ n < 37, storeTail (chainSite n) = n + 1 := by decide +kernel

/-- A site of the chain is the site at its position. -/
theorem chainSite_tail (s : Site) (pos : 1 ≤ storeTail s) : s = chainSite (storeTail s - 1) := by
  revert pos
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

end PTX.Kernels.InklingRelDecode.Proof.Prologue
