-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Startup.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Startup
open PTX PTX.Flow PTX.Proof

theorem inv_next {L g d dn ev} (hi : Inv L g d) (step : succ L g d ev=some (some dn)) :
    Inv L g dn := by
  obtain ⟨s,tm,x,w⟩ := d
  cases s <;> simp only [succ] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals simp_all [Inv]

end PTX.Kernels.InklingRelDecode.Proof.Startup
