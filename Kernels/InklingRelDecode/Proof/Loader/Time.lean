-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Measure
public import Kernels.InklingRelDecode.Proof.Lib.Slots

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX

noncomputable section

/-- Iteration times leave room for the MMA and softmax sites of the same block. -/
def slotTime (block : Nat) := Lib.Slots.frame block

def time (d : D) : Nat :=
  match d.site with
  | .dec => Lib.Slots.enter | .first => 287 | .second => 288 | .beginBar => Lib.Slots.reuse
  | .endBar => Lib.Slots.finish + 276
  | .inc => Lib.Slots.finish + 280
  | .dispatch => Lib.Slots.finish + 284
  | s => slotTime (bits d.counter).toNat + s.position

theorem poll_time (i n a b : Value) :
    time ⟨.poll,i,n,a,b⟩ = slotTime (bits i).toNat := rfl

theorem ready_times (i n a b : Value) (p : Fin 4) (s : Bool) :
    time ⟨.arrive,i,n,a,b⟩ = Lib.Slots.readyArrival (bits i).toNat ∧
    time ⟨.copy p s,i,n,a,b⟩ = Lib.Slots.readyCopy (bits i).toNat p s := ⟨rfl,rfl⟩

theorem time_bounds (d : D) : 2 ≤ time d ∧ time d ≤ Lib.Slots.finish + 284 := by
  obtain ⟨s,i,n,a,b⟩ := d
  have hi := bits_lt i
  have hs := position_bound s
  cases s <;> simp only [time, slotTime, Lib.Slots.frame, Lib.Slots.stride, Lib.Slots.finish,
    Lib.Slots.enter, Lib.Slots.reuse] <;> omega

/-- The complete loader band precedes the MMA band 100 ticks after the start of a slot. -/
theorem before_mma (s : Site) (i : Nat) : slotTime i + s.position < slotTime i + 100 := by
  have h := position_bound s
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
