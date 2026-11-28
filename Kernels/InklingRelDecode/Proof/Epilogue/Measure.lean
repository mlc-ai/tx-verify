-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Ledger

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX PTX.Flow Control

/-- The output words occupy consecutive positions between the optional LSE store and the join. -/
def Site.position : Site → Nat
  | .wait => 0 | .shfl => 1 | .load => 2 | .waitLd => 3 | .lse => 4
  | .store j => 5+j.val | .join => 69 | .setMax => 70 | .roleWord => 71
  | .sync1 => 72 | .sync0 => 73 | .dealloc => 74 | .exit => 75

def measure (d : D) := 75-d.site.position

theorem position_bound (s : Site) : s.position ≤ 75 := by
  cases s <;> simp only [Site.position] <;> omega

theorem measure_bound (d : D) : measure d ≤ 75 := Nat.sub_le ..

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
