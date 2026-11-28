-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryStq
public import Kernels.InklingRelDecode.Proof.Prologue.Data.Column

@[expose] public section

/-! # The data step of every state of the prologue -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section

/-- **The data step of a query load.** -/
theorem ldq_step {Q L g w} (d : D) (j : Fin 64) (hs : d.c.site = .ldq j) :
    DataStep (code Q L g w) (dF Q L g) d :=
  ldq_step_of d j hs fun d' v hon hcc hv => by
    obtain ⟨hi, h64, hjh, hsite, hoff, -⟩ := after_site d.c (g % L.block) j hon
    have hcc' : d'.c = {d.c with site := qSiteAt hi} := hcc.trans (by rw [hsite])
    by_cases hlt : hi < 64
    · exact ldq_reach_lt hs hon hcc' hv hlt hjh hoff
    · obtain rfl : hi = 64 := by omega
      exact ldq_reach_end hs hon hcc' hv hoff

/-- **The data step of every state of the prologue.** -/
theorem data_step_all {Q L g w m} (hp : Pre Q L m) (d : D) :
    DataStep (code Q L g w) (dF Q L g) d := by
  by_cases hq : qside d.c.site = false
  · exact data_step d hq
  · have hq' : qside d.c.site = true := by simpa using hq
    generalize hs : d.c.site = s at hq'
    cases s with
    | bar2 => exact bar2_step hp d hs
    | pel b j => fin_cases j <;> first | exact pel3_step hp d b hs | simp [qside] at hq'
    | ptc b j => fin_cases j <;> first | exact ptc3_step hp d b hs | simp [qside] at hq'
    | ldq j => exact ldq_step d j hs
    | stq i j => fin_cases j <;> first | exact stq3_step d i hs | simp [qside] at hq'
    | _ => simp [qside] at hq'

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
