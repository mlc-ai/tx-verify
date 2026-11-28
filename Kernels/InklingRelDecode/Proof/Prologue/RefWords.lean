-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Input
import Kernels.InklingRelDecode.Proof.Prologue.Ledger
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Proof PTX.Flow Control

/-- Each request register is identified as soon as its read has occurred. -/
structure Known (Q : Params) (r : Nat) (d : D) : Prop where
  first : 34 < d.site.pc → d.first = b32 (Q.qStart r)
  last : 37 < d.site.pc → d.last = b32 (Q.qStart (r+1))
  seq : 41 < d.site.pc → d.seq = b32 (Q.seqK r)

theorem known_init (Q r) : Known Q r {} := by
  constructor <;> intro h <;> contradiction

theorem known_next {Q L g e d dn r} (known : Known Q r d)
    (hn : Control.next Q L g d e = some (some dn))
    (input : ∀ j, d.site = .ld j → ∀ a bs, e.kind = .rd a bs →
      rebuild 3 bs = .ok (b32 (requestWord Q r j))) : Known Q r dn := by
  by_cases load : ∃ j, d.site = .ld j
  · obtain ⟨j,site⟩ := load
    obtain ⟨s,f,l,v,w⟩ := d; cases site
    fin_cases j <;> simp only [Control.next] at hn <;> split at hn <;> try contradiction
    all_goals cases hn
    all_goals rename_i a bs h
    all_goals have rebuilt := input _ rfl a bs h
    all_goals rw [rebuilt]
    all_goals constructor
    all_goals first
      | exact fun _ => rfl
      | (intro bound; exact False.elim ((by decide : ¬37<37) bound))
      | (intro bound; exact False.elim ((by decide : ¬41<37) bound)) |
      (intro bound; exact False.elim ((by decide : ¬41<41) bound)) |
      exact fun _ => known.first (by dsimp only; decide) |
      exact fun _ => known.last (by dsimp only; decide)
  by_cases entry : d.site=.sMax
  · simp only [Control.next,entry,Option.some.injEq] at hn
    subst dn; constructor <;> intro h <;> change _ < 34 at h <;> omega
  have lower : 41 < d.site.pc := by
    have bound (s : Site) : (match s with | .sMax | .ld _ => True | _ => 41<s.pc) := by
      cases s <;> repeat' first | exact trivial | (rename_i j; revert j)
      all_goals decide +kernel
    have h := bound d.site
    cases eq : d.site <;> rw [eq] at h
    all_goals first | exact h | contradiction | exact (load ⟨_,eq⟩).elim
  have fixed : dn.first=d.first ∧ dn.last=d.last ∧ dn.seq=d.seq := by
    cases hs : d.site <;> simp only [Control.next,hs] at hn
    all_goals try exact (load ⟨_,hs⟩).elim
    all_goals repeat' split at hn
    all_goals first | contradiction | (cases hn; exact ⟨rfl,rfl,rfl⟩) | cases hn
  obtain ⟨f,l,v⟩ := fixed
  exact ⟨fun _ => f.trans (known.first (by omega)),fun _ => l.trans (known.last (by omega)),
    fun _ => v.trans (known.seq lower)⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue
