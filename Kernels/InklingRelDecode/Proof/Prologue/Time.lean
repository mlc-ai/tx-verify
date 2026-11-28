-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Measure
public import Kernels.InklingRelDecode.Proof.Lib.Slots

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow Control

/-- Dense site order includes each vector-store substep; barrier 1 meets Dispatch at 281. -/
def time (d : D) := Lib.Slots.prologue + allSites.idxOf d.site

theorem last_bar_time (a b c : Value) (w : Bool) (recv : Value := PTX.Proof.b32 0) :
    time ⟨.bar18,a,b,c,w,recv⟩ = Lib.Slots.publish := by
  change Lib.Slots.prologue + allSites.idxOf .bar18 = Lib.Slots.publish
  decide +kernel

theorem time_floor (d : D) : 2 ≤ time d := by unfold time Lib.Slots.prologue; omega

end PTX.Kernels.InklingRelDecode.Proof.Prologue
