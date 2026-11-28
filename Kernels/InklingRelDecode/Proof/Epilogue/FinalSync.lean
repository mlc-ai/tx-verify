-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
public import Kernels.InklingRelDecode.Proof.Lib.ExitPC

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX Control

theorem final_step {entry L g d ev dn} (hn : Control.next entry L g d ev = some (some dn)) :
    Lib.afterFinal dn.site.pc = Lib.afterFinal d.site.pc + (Lib.finalSync d.site.pc).toNat := by
  have last (s : Site) : Lib.finalSync s.pc = decide (s=.sync0) := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  have post (s : Site) : Lib.afterFinal s.pc = (decide (s=.dealloc ∨ s=.exit)).toNat := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  simp only [last,post]
  obtain ⟨s,v⟩ := d
  cases s <;> simp only [Control.next,firstStore,storeAt] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals rfl

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
