-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Measure
public import Kernels.InklingRelDecode.Proof.Lib.Slots

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX

/-- The MMA band begins 100 ticks into each slot. -/
def slotTime (block : Nat) : Nat := Lib.Slots.mma block

def time (d : D) : Nat :=
  let finish := Lib.Slots.finish
  match d.site with
  | .setMaxReg => Lib.Slots.enter | .ldNum => 287 | .bar0 => Lib.Slots.reuse
  | .finBar => finish - 100 | .finElect => finish - 96 | .finCommit => finish - 92
  | .bar1 => finish + 276 | .setMaxRegInc => finish + 280 | .dispatch => finish + 284
  | s => slotTime d.i + s.position

theorem wait_times (i : Nat) (v : Value) :
    time ⟨.kvWait,i,v⟩ = slotTime i + 1 ∧ time ⟨.pWait,i,v⟩ = slotTime i + 15 :=
  ⟨rfl, rfl⟩

theorem channel_times (r : Nat) (v : Value) :
    time ⟨.kvWait,r,v⟩ = Lib.Slots.readyWait r ∧
    time ⟨.qkCommit,r,v⟩ = Lib.Slots.scoreCommit r ∧
    time ⟨.pWait,r+1,v⟩ = Lib.Slots.probWait r ∧
    time ⟨.pvCommit1,r+1,v⟩ = Lib.Slots.emptyCommit r ∧
    time ⟨.pvCommit2,r,v⟩ = Lib.Slots.doneCommit r ∧
    time ⟨.finCommit,r,v⟩ = Lib.Slots.finalCommit := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem time_bounds {d : D} (hi : Inv d) :
    2 ≤ time d ∧ time d ≤ Lib.Slots.finish + 284 := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Inv, time, Site.position, slotTime,
    Lib.Slots.frame, Lib.Slots.stride, Lib.Slots.finish,
    Lib.Slots.enter, Lib.Slots.reuse, Lib.Slots.mma] at hi ⊢ <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Mma
