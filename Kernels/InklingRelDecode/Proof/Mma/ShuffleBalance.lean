-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Ledger
public import Kernels.InklingRelDecode.Proof.Lib.CollectiveAt

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow

/-- A successful poll obliges the lane to broadcast once. -/
def owed : Site → Nat
  | .qkShfl | .pvShfl => 1
  | _ => 0

private theorem after_debt (d : D) : owed (afterQk d).site = 0 := by
  simp only [afterQk, iterNext]; split_ifs <;> rfl

private theorem iter_debt (d : D) : owed (iterNext d).site = 0 := by
  unfold iterNext; split_ifs <;> rfl

private theorem off (s : Site) (h : owed s=0) : Lib.canShuffle s.pc=false := by
  cases s <;> first | contradiction | decide +kernel | (rename_i j; fin_cases j <;> decide +kernel)

theorem owed_next {d dn : D} {L g ev} (src : Lib.CollectiveAt d.site.pc ev)
    (hn : next L g d ev = some (some dn)) :
    (Execution.isShfl ev).toNat + owed dn.site =
      owed d.site + (receipt d.site ev).1 + (receipt d.site ev).2 := by
  obtain ⟨s,i,v⟩ := d
  cases s
  case kvWait | pWait =>
    have off := src.shuffle (off _ rfl)
    rw [off]
    simp only [next] at hn
    split at hn <;> try contradiction
    rename_i ok _ _ he
    cases ok <;> cases hn <;> simp [receipt,he,owed]
  case qkShfl | pvShfl =>
    simp only [next] at hn
    split at hn <;> try contradiction
    rename_i he
    obtain ⟨_,_⟩ := ev
    cases he
    cases hn; split <;> rfl
  all_goals have off := src.shuffle (off _ rfl)
  all_goals rw [off]
  case ldNum =>
    simp only [next] at hn
    split at hn <;> try contradiction
    rename_i bs _
    cases h : (rebuild 3 bs).toOption <;> simp [h] at hn
    subst dn; rfl
  all_goals simp only [next] at hn
  all_goals repeat' split at hn
  all_goals try contradiction
  all_goals cases hn
  all_goals simp only [Bool.toNat_false, Nat.zero_add, receipt, owed, Nat.add_zero]
  all_goals first | apply after_debt | apply iter_debt |
    (unfold startSite; split_ifs <;> rfl) | (unfold issueNext; split_ifs <;> rfl)

end PTX.Kernels.InklingRelDecode.Proof.Mma
