-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Seq
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpKinds
public import Lemmas.Flow.ReachSegU
public import Lemmas.Flow.ReachFrameGuard

@[expose] public section

/-! # The first window as a reach to the shuffle of pc 1838

From the registers the window reads (`kW1`, any values) every path to the shuffle at pc 1838 knows
the register of the value the thread sends (register 1520), read under `vFin`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code

set_option maxRecDepth 100000
noncomputable section
variable {L : Launch} {g : Nat}

theorem kXin_fin : ∀ r ∈ kXin, r ∈ kFin := by decide +kernel

/-- **The sent word of the first window**: from `kW1` to the shuffle, the register 1520 holds
`vFin` of the file. -/
theorem w1_reach (V : Nat → Value) :
    Reach kernel Assumptions.all L g 1299 (factsFrom kW1 V) (factsFrom kXin (vFin V)) :=
  SegU.reach_then (w1_fin V) (reach_frameSetG (S := []) Lib.rulesFrame (by simp [frameSetG])
    (fun _ h => nomatch h) (by decide +kernel)
    (fun R h => holds_of_mem fun r x hm => by
      obtain ⟨r', hr', he⟩ := List.mem_map.mp hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact holds_mem h (mem_factsFrom (kXin_fin r' hr'))))

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
