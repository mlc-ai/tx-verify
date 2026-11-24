-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Projection
import Kernels.TmlFa4Fwd.Proof.Softmax.Steps

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow
noncomputable section

def schedulerSite : Site → Bool
  | .setmax | .bar1 | .word .. | .down .. | .up .. | .total .. | .vote .. | .pre ..
  | .tiles .. | .q0 | .q1 | .uk | .finarr | .wend .. | .barEnd .. | .exit .. => true
  | _ => false

private def pcs := [3102,3103,3110,3111,3130,3134,3138,3142,3146,3150,3169,3171,3192,
  3195,3198,3201,3204,3207,3220,3227,3231,3369,3370,3373,7616,7621,7622,7642,7645,7648,
  7651,7654,7657,7677,7679,7700,7703,7706,7709,7712,7715,7726,7731,7732,7738,7741,9205]

set_option maxRecDepth 100000 in
private theorem table : pcs.all (fun pc => liveD pc == ctlLive pc) = true := by decide +kernel

private theorem pc_mem (s : Site) (hs : schedulerSite s = true) : s.pc ∈ pcs := by
  cases s with
  | word sk | down sk | total sk => cases sk <;> decide
  | up sk j => cases sk <;> fin_cases j <;> decide
  | vote l | pre l | tiles l | wend l | barEnd l | exit l => cases l <;> decide
  | setmax | bar1 | q0 | q1 | uk | finarr => decide
  | _ => cases hs

theorem stepAt_schedulerU {p L m g} (hp : Pre p L m) (hg : g < L.threads)
    (hw : g % L.block / 32 < 8) (d : D) (hs : schedulerSite d.site = true) :
    (code p L g).StepAtU d := by
  have heq : livePc d.scheduler = d.site.pc := by
    obtain ⟨s,v,k,acc⟩ := d
    cases s <;> first | rfl | cases hs
  have hr : readsData d.site = false := by
    obtain ⟨s,v,k,acc⟩ := d
    cases s <;> first | rfl | cases hs
  have hl := beq_iff_eq.mp (List.all_eq_true.mp table _ (pc_mem _ hs))
  apply project_data hr (facts_eq_data (heq ▸ hl))
  apply stepAt_ctl hp hg hw
  obtain ⟨s,v,k,acc⟩ := d
  cases s <;> first | rfl | cases hs

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
