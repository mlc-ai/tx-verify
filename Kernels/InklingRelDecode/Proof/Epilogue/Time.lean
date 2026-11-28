-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Measure
public import Kernels.InklingRelDecode.Proof.Lib.Slots

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX PTX.Flow Control

def startTime := Lib.Slots.finish
def time (d : D) := startTime + 4*d.site.position

theorem time_floor (d : D) : 2 ≤ time d :=
  Nat.le_trans (by decide : 2 ≤ startTime) (Nat.le_add_right ..)

theorem final_wait_time (v : Value) : time ⟨.wait,v⟩ = Lib.Slots.finalWait :=
  Nat.add_zero Lib.Slots.finish

theorem final_bar_times (v : Value) :
    time ⟨.join,v⟩ = startTime+276 ∧ time ⟨.sync1,v⟩ = startTime+288 ∧
      time ⟨.sync0,v⟩ = startTime+292 := ⟨rfl,rfl,rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
