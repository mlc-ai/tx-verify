-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Measure
public import Kernels.InklingRelDecode.Proof.Lib.Slots

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow Control

def time (d : D) : Nat :=
  match d.site with
  | .setMaxReg => Lib.Slots.enter | .bar0 => Lib.Slots.reuse | .pre j => 293+4*j.val
  | .epilogue => Lib.Slots.finish
  | s => Lib.Slots.softmax d.i+s.position

theorem time_floor (d : D) : 2 ≤ time d := by
  unfold time
  split
  · decide
  · decide
  · exact Nat.le_trans (by decide : 2 ≤ 293) (Nat.le_add_right ..)
  · decide
  · change 2 ≤ 1000 + 400*d.i + 200 + _
    omega

theorem arrive_time (i : Nat) (v : Carry) :
    time ⟨.arrive,i,v⟩ = Lib.Slots.probArrival i := rfl

theorem poll_times (i : Nat) (v : Carry) :
    time ⟨.waitS,i,v⟩ = Lib.Slots.scoreWait i ∧ time ⟨.waitO,i,v⟩ = Lib.Slots.doneWait i := by
  exact ⟨rfl,rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax
