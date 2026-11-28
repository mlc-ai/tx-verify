-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Startup.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Startup

def measure (s : Site) : Nat :=
  match s with
  | .alloc => 7 | .allocWr => 6 | .bar0 => 5 | .ld0 => 4
  | .bar1 => 3 | .relinq => 2 | .shfl => 1 | .enter _ => 0

theorem measure_next {L g d dn ev} (next : succ L g d ev=some (some dn)) :
    measure dn.site < measure d.site := by
  obtain ⟨s,tm,x,w⟩ := d
  cases s <;> simp only [succ] at next
  all_goals repeat' split at next
  all_goals cases next
  all_goals simp [measure]

end PTX.Kernels.InklingRelDecode.Proof.Startup
