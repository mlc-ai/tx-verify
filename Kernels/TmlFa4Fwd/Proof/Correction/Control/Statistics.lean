-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.Havoc
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Lemmas.Flow.LandsU
import Lemmas.Flow.SegCtl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

private theorem keys {live : List Nat} {val : Nat → Value} :
    (factsFrom live val).map Prod.fst = live := by
  simp only [factsFrom, List.map_map, Function.comp_def]
  exact List.map_id live

set_option hygiene false in
local macro "stat_load " dst:term " at " reg:term " via " lookup:term : tactic =>
  `(tactic| (
    refine Code.step_loadU (C := code p L g) (d' := $dst) (r := $reg) $lookup rfl rfl rfl rfl rfl
      rfl rfl rfl rfl (fun _ _ => rfl) (Or.inl rfl) ?_ ?_
    · change _ ∉ (factsFrom _ _).map Prod.fst
      rw [keys]
      dsimp only [live, D.site]
      decide +kernel
    · dsimp only [code, facts]
      seg_ctl rules_frame, hooks_ok))

variable {p : Params} {L : Launch} {g : Nat}

theorem stepAt_rscaleU (st : Fin 2) (v : V) : (code p L g).StepAtU ⟨.rscale st, v, 0⟩ := by
  fin_cases st
  · stat_load ⟨.rvote 0, v, 0⟩ at 1651 via Flow.code_8007
  · stat_load ⟨.rvote 1, v, 0⟩ at 1652 via Flow.code_8226

theorem stepAt_fsumU (st : Fin 2) (v : V) : (code p L g).StepAtU ⟨.fsum st, v, 0⟩ := by
  fin_cases st
  · stat_load ⟨.fmax 0, v, 0⟩ at 6512 via Flow.code_8466
  · stat_load ⟨.fmax 1, v, 0⟩ at 1653 via Flow.code_8762

theorem stepAt_fmaxU (st : Fin 2) (v : V) : (code p L g).StepAtU ⟨.fmax st, v, 0⟩ := by
  fin_cases st
  · stat_load ⟨.farr 0, v, 0⟩ at 6513 via Flow.code_8467
  · stat_load ⟨.farr 1, v, 0⟩ at 1654 via Flow.code_8763

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
