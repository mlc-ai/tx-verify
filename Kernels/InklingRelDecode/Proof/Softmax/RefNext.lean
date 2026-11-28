-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Ledger

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow Control

set_option maxRecDepth 100000

private theorem other_pc (s : Site) (a : s ≠ .waitS) (b : s ≠ .waitO) (c : s ≠ .arrive) :
    s.pc ≠ 1257 ∧ s.pc ≠ 2239 ∧ s.pc ≠ 1013 := by
  cases s <;> first | contradiction | decide | exact bias_other true _ | exact bias_other false _

private theorem loop_not_late (e : Entry) (t i : Nat) : (loopSite e t i).late = false := by
  unfold loopSite; split_ifs <;> rfl

private theorem other {ent : Entry} {L : Launch} {g i : Nat} {s : Site} {v : Carry}
    {ev : Event} {dn : D} (ow : s.late = true → 0 < i)
    (pc : ev.pc = s.pc) (hs : s ≠ .waitS) (ho : s ≠ .waitO) (ha : s ≠ .arrive)
    (hn : Control.next ent L g ⟨s,i,v⟩ ev = some (some dn)) :
    Ref (g%L.block) dn ((counts (g%L.block) ⟨s,i,v⟩).bump ev) := by
  obtain ⟨a,b,c⟩ := other_pc s hs ho ha
  rw [bump_other _ _ (pc ▸ a) (pc ▸ b) (pc ▸ c)]
  cases s <;> try contradiction
  all_goals simp only [Control.next] at hn
  all_goals repeat' split at hn
  all_goals try contradiction
  all_goals cases hn
  all_goals try subst i
  all_goals constructor
  all_goals first
    | rfl | (intro h; cases h; done) | (intro h; change 0 < i; omega)
    | (intro eq; rw [loop_not_late] at eq; cases eq)
    | (intro _; exact ow rfl)
    | (simp only [advance,counts_loop]; rfl)
    | (simp only [advance,counts_loop]; simp_all [counts,Site.afterS,Site.afterO])

theorem ref_next {ent : Entry} {L : Launch} {g : Nat} {d dn : D} {ev : Event} {c : Cnt}
    (inv : Inv ent (g%L.block) d)
    (ref : Ref (g%L.block) d c) (pc : ev.pc = d.site.pc)
    (hn : Control.next ent L g d ev = some (some dn)) :
    Ref (g%L.block) dn (c.bump ev) := by
  obtain ⟨s,i,v⟩ := d
  obtain ⟨rfl,ow⟩ := ref
  by_cases hs : s = .waitS
  · subst s
    obtain ⟨p,k⟩ := ev
    cases pc
    simp only [Control.next] at hn
    split at hn <;> try contradiction
    rename_i _ _ _ ok _ _
    cases ok <;> cases hn <;> constructor <;> first | rfl | (intro h; cases h)
  by_cases ho : s = .waitO
  · subst s
    have positive : 0 < i := ow rfl
    obtain ⟨p,k⟩ := ev
    cases pc
    simp only [Control.next] at hn
    split at hn <;> try contradiction
    rename_i _ _ _ ok _ _
    cases ok <;> cases hn <;> constructor <;> first
      | rfl | (intro h; cases h; done) | exact fun _ => positive |
      (simp [counts,Cnt.bump,Site.afterS,Site.afterO,okPollAt]; omega)
  by_cases ha : s = .arrive
  · subst s
    have lead := inv.lead rfl
    cases hn
    constructor
    · rw [show (advance ent (g%L.block) ⟨.arrive,i,v⟩) =
          ⟨loopSite ent (g%L.block) (i+1),i+1,v⟩ by rfl,counts_loop]
      have noPoll (p : Nat) (h : p ≠ 1013) : okPollAt p ev = false := by
        obtain ⟨_,k⟩ := ev
        cases pc
        cases k <;> try rfl
        rename_i _ _ ok _ _
        cases ok <;> simp_all [okPollAt]; omega
      simp [Cnt.bump,counts,Site.afterS,Site.afterO,noPoll _ (by decide : 1257 ≠ 1013),
        noPoll _ (by decide : 2239 ≠ 1013),lead,pc,Site.pc]
    · intro h
      change (loopSite ent (g%L.block) (i+1)).late = true at h
      rw [loop_not_late] at h
      cases h
  exact other ow pc hs ho ha hn

end PTX.Kernels.InklingRelDecode.Proof.Softmax
