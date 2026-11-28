-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
public import Lemmas.Tmem.PairProtocol
import Kernels.InklingRelDecode.Flow.Code.Part044
import Lemmas.Flow.TmemOperands

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX PTX.Flow Control

/-- Every observed deallocation frees exactly 512 columns in group one.
Its starting column is supplied by the recorded allocation word. -/
theorem dealloc_kind {L g t o grp dst act} {ev : Event}
    (fire : Fires 2851
      (eventTmpl Assumptions.all L g t (.tcDealloc .one (.reg 463) (.imm 512))) ev o)
    (kind : ev.kind=.tc (.resource grp dst act)) :
    ∃ a, grp=.one ∧ dst=none ∧ act=.dealloc a.toNat 512 ∧
      readBits L g t 32 (.reg 463)=.ok a := by
  obtain ⟨a,n,addr,size,req⟩ := fires_tcDealloc_ops fire kind
  have imm : readBits L g t 32 (.imm 512)=.ok (512 : BitVec 64) := rfl
  obtain rfl := Except.ok.inj (size.symm.trans imm)
  obtain ⟨one,none,-⟩ := fires_tcDealloc_at addr size fire kind
  exact ⟨a,one,none,req,addr⟩

/-- A lane of warp zero can only reach its return by consuming the deallocation. -/
theorem exit_count {e L g d ev sn} (low : g%L.block<32)
    (step : Control.next e L g d ev=some (some sn)) :
    (decide (sn.site.pc=2855)).toNat =
      (decide (d.site.pc=2855)).toNat+(decide (d.site.pc=2851)).toNat := by
  have pcs (s : Site) : (s.pc=2855 ↔ s=.exit) ∧ (s.pc=2851 ↔ s=.dealloc) := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  simp only [(pcs _).1,(pcs _).2]
  obtain ⟨s,v⟩ := d
  cases s <;> simp only [Control.next,low,ite_true,firstStore,storeAt] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals rfl

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
