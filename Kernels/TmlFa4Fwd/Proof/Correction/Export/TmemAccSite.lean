-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.NoLdSt

@[expose] public section

/-! # The sites of the correction stores: a correction store is fired at a rescale store -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 8000000 in
theorem corr_st_site {d : Correction.D} {pc a : Nat} {vals : List Value} {sh : TcShape}
    (hev : Correction.Ev p L g d ⟨pc, .tc (.st a vals sh)⟩) : ∃ st c, d.site = .rst st c := by
  obtain ⟨s, v, kk⟩ := d
  cases s
  case rst st c => exact ⟨st, c, rfl⟩
  all_goals exfalso
  all_goals simp only [Correction.Ev] at hev
  all_goals first | exact (epi_noldst (hev := hev) (by trivial)).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [Correction.rdOrUb]

end
end PTX.Kernels.TmlFa4Fwd.Proof
