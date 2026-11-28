-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Ledger

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX PTX.Flow PTX.Proof Control

private theorem stores_past (n : Nat) : storeAt n ≠ .wait := by
  unfold storeAt; split <;> nofun

private theorem gate_past (a b : Bool) : firstStore a b ≠ .wait := by
  cases a <;> cases b <;> decide

theorem ref_next {ent L g d dn ev n} (ref : Ref d n) (pc : ev.pc = d.site.pc)
    (hn : Control.next ent L g d ev = some (some dn)) :
    Ref dn (n+(okPollAt 2565 ev).toNat) := by
  obtain ⟨s,v⟩ := d
  obtain rfl := ref
  by_cases h : s=.wait
  · subst s
    obtain ⟨p,k⟩ := ev
    cases pc
    simp only [Control.next] at hn
    split at hn <;> try contradiction
    rename_i _ _ _ ok _ _
    cases ok <;> cases hn
    · rfl
    · cases ent.skip <;> simp [Ref,polls,okPollAt,gate_past]
  · have off := bump_away (pc ▸ final_only s h)
    simp only [Ref,polls,off,Bool.toNat_false,Nat.add_zero,ite_eq_right h]
    cases s <;> try contradiction
    all_goals simp only [Control.next] at hn
    all_goals repeat' split at hn
    all_goals try contradiction
    all_goals cases hn
    all_goals simp [gate_past,stores_past]

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
