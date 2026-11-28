-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryEntry
import Lemmas.Flow.DataCompute

@[expose] public section

/-! # The sites that may enter the query part

The barrier before the preload loop and the last copy of each block go to a query site or keep
their facts for the next preload step. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section

/-- A query load or store site. -/
def isQ : Site → Bool
  | .ldq _ | .stq _ _ => true
  | _ => false

theorem qcarry : ∀ s, qside s = true → isQ s = false → ∀ s' ∈ succs s, isQ s' = false →
    ∀ τ ∈ tags s', τ ∈ tags s := by
  intro s
  cases s <;> repeat' (rename_i j; revert j)
  all_goals decide +kernel

theorem qside_tags : ∀ s, qside s = true → isQ s = false → qTags s = [] ∧ s ≠ .exit := by
  intro s
  cases s <;> repeat' (rename_i j; revert j)
  all_goals decide +kernel

theorem qTags_nil : ∀ s, isQ s = false → qTags s = [] := by
  intro s; cases s <;> simp [isQ, qTags]

/-- **The facts of a non-query successor of a site that may enter the query part** are its own. -/
theorem carry_sub_q {Q : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hq : qside d.c.site = true) (hnq : isQ d.c.site = false) (hb : ¬ Bare d.c.site)
    (h : succ Q L g d e = some (some d')) (hd' : isQ d'.c.site = false) :
    ∀ x ∈ dF Q L g d', x ∈ dF Q L g d := by
  obtain ⟨c, hn, rfl⟩ := succ_split h
  have hl : ∀ b h', d.c.site ≠ .lb b h' := fun b h' e => by simp_all [qside]
  have hq' : ∀ j, d.c.site ≠ .ldq j := fun j e => by simp_all [isQ]
  obtain ⟨hm, hbc⟩ := next_succ Q L g hb hn
  have hsub := qcarry _ hq hnq _ hm hd'
  intro x hx
  simp only [dF, List.mem_map] at hx ⊢
  obtain ⟨τ, hτ, rfl⟩ := hx
  refine ⟨τ, hsub τ hτ, ?_⟩
  rw [record_keep hl hq']
  cases τ with
  | col b' h' =>
    have hnb : ∀ b, d.c.site ≠ .psh b := fun b hp => by simp_all [qside]
    simp [Tag.val, hbc hnb]
  | qh k | qw i k =>
    all_goals exact absurd (by
      have := qTags_nil _ hd'
      simp only [tags, this, List.append_nil] at hτ
      first | exact (old_noq c.site).1 _ hτ | exact (old_noq c.site).2 _ _ hτ) id
  | _ => rfl

/-- **A `Reach` of facts held before and written by nothing from the position on.** -/
theorem reach_carry {Q L g} {d d' : D} {p : Nat} {F : List (Nat × Value)}
    (hsub : ∀ τ ∈ tags d'.c.site, τ ∈ tags d.c.site) (hF : ∀ x ∈ dF Q L g d', x ∈ F)
    (hp : d.c.site.pc ≤ p) (hp27 : 27 ≤ p) (hp5 : p ≤ 574) :
    Reach kernel Assumptions.all L g p F (dF Q L g d') := by
  refine Reach.region Lib.rulesFrame (lo := p) (hi := 574) ?_
    (fun pc h1 h2 => seg_range (by omega) h2) le_rfl hp5
    (fun R hR => holds_of_mem fun r v hm => holds_mem hR (hF _ hm))
  have hmap : (dF Q L g d').map Prod.fst = (tags d'.c.site).map Tag.reg := by simp [dF]
  rw [hmap]
  exact region_tags hp27 fun τ hτ => by
    have := Nat.blt_eq.mp (List.all_eq_true.mp (tags_pc d.c.site) τ (hsub τ hτ)); omega

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
