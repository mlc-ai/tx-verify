-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeScan
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.End
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Final
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.FinalWait
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fld00
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fld01
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fld10
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fld11
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fst000
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fst001
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fst010
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fst011
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fst100
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fst101
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fst110
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fst111
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fwl00
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fwl01
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fwl10
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Fwl11
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Lse
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Rld0
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Rld1
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Rldw0
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Rldw1
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.RldwZ0
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.RldwZ1
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Round
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.RoundArr
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Rst0
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Rst1
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Select
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Start1
import Kernels.TmlFa4Fwd.Proof.Correction.ShapeSet.Start2
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' shape table at every state

`shape`: every event a state of the correction machine fires has the state's shape (`Ev`), from
the groups of sites of `ShapeScan.lean` and `ShapeSet/` (each by `site_shape`, a file per group)
and the states at a sub-step their site does not have (`shapeAt_junk`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt (hp : Pre p L m) (d : D) : (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k⟩ := d
  by_cases hk : k = 0
  · subst hk
    cases s with
    | word sc | down sc | total sc => exact shapeAt_scan hp _ rfl sc (by simp)
    | up sc j => exact shapeAt_scan hp _ rfl sc (by simp)
    | setmax | bar1 | q0 => exact shapeAt_Start1 hp _ rfl (by simp)
    | arr a => exact shapeAt_Start1 hp _ rfl (by fin_cases a <;> simp)
    | q1 | uk | free => exact shapeAt_Start2 hp _ rfl (by simp)
    | nb a => exact shapeAt_Start2 hp _ rfl (by fin_cases a <;> simp)
    | vote b | pre b | tiles b => exact shapeAt_Select hp _ rfl (by cases b <;> simp)
    | wend b | barEnd b | exit b => exact shapeAt_End hp _ rfl (by cases b <;> simp)
    | rbar st | rscale st | rvote st | rwait st =>
      exact shapeAt_Round hp _ rfl (by fin_cases st <;> simp)
    | rarr st a => exact shapeAt_RoundArr hp _ rfl (by fin_cases st <;> fin_cases a <;> simp)
    | rld st c =>
      fin_cases st
      · exact shapeAt_Rld0 hp _ rfl (by fin_cases c <;> simp)
      · exact shapeAt_Rld1 hp _ rfl (by fin_cases c <;> simp)
    | rst st c =>
      fin_cases st
      · exact shapeAt_Rst0 hp _ rfl (by fin_cases c <;> simp)
      · exact shapeAt_Rst1 hp _ rfl (by fin_cases c <;> simp)
    | rldw st c =>
      fin_cases st
      · exact shapeAt_RldwZ0 hp _ rfl (by fin_cases c <;> simp)
      · exact shapeAt_RldwZ1 hp _ rfl (by fin_cases c <;> simp)
    | farr0 => exact shapeAt_Final hp _ rfl (by simp)
    | fbar st | fsum st | fmax st | farr st =>
      exact shapeAt_Final hp _ rfl (by fin_cases st <;> simp)
    | fence st => exact shapeAt_FinalWait hp _ rfl (by fin_cases st <;> simp)
    | fw st a | fdone st a =>
      exact shapeAt_FinalWait hp _ rfl (by fin_cases st <;> fin_cases a <;> simp)
    | fld st j =>
      fin_cases st <;> fin_cases j <;>
        first
        | (refine shapeAt_Fld00 hp _ rfl ?_; simp; done)
        | (refine shapeAt_Fld01 hp _ rfl ?_; simp; done)
        | (refine shapeAt_Fld10 hp _ rfl ?_; simp; done)
        | (refine shapeAt_Fld11 hp _ rfl ?_; simp; done)
    | fwl st j =>
      fin_cases st <;> fin_cases j <;>
        first
        | (refine shapeAt_Fwl00 hp _ rfl ?_; simp; done)
        | (refine shapeAt_Fwl01 hp _ rfl ?_; simp; done)
        | (refine shapeAt_Fwl10 hp _ rfl ?_; simp; done)
        | (refine shapeAt_Fwl11 hp _ rfl ?_; simp; done)
    | fst st j h =>
    fin_cases st <;> fin_cases h <;> fin_cases j <;>
      first
      | (refine shapeAt_Fst000 hp _ ?_; simp; done)
      | (refine shapeAt_Fst001 hp _ ?_; simp; done)
      | (refine shapeAt_Fst010 hp _ ?_; simp; done)
      | (refine shapeAt_Fst011 hp _ ?_; simp; done)
      | (refine shapeAt_Fst100 hp _ ?_; simp; done)
      | (refine shapeAt_Fst101 hp _ ?_; simp; done)
      | (refine shapeAt_Fst110 hp _ ?_; simp; done)
      | (refine shapeAt_Fst111 hp _ ?_; simp; done)
    | lse h => exact shapeAt_Lse hp _ (by fin_cases h <;> simp)
  · cases s with
    | fst st j h =>
    fin_cases st <;> fin_cases h <;> fin_cases j <;>
      first
      | (refine shapeAt_Fst000 hp _ ?_; simp; done)
      | (refine shapeAt_Fst001 hp _ ?_; simp; done)
      | (refine shapeAt_Fst010 hp _ ?_; simp; done)
      | (refine shapeAt_Fst011 hp _ ?_; simp; done)
      | (refine shapeAt_Fst100 hp _ ?_; simp; done)
      | (refine shapeAt_Fst101 hp _ ?_; simp; done)
      | (refine shapeAt_Fst110 hp _ ?_; simp; done)
      | (refine shapeAt_Fst111 hp _ ?_; simp; done)
    | lse h => exact shapeAt_Lse hp _ (by fin_cases h <;> simp)
    | rldw st c =>
      by_cases h1 : k = 1
      · subst h1
        fin_cases st
        · exact shapeAt_Rldw0 hp _ rfl (by fin_cases c <;> simp)
        · exact shapeAt_Rldw1 hp _ rfl (by fin_cases c <;> simp)
      · exact shapeAt_junk (by simp [Site.midOk, hk, h1])
    | _ => exact shapeAt_junk (by simp [Site.midOk, hk])

/-- **Every event a state of the correction machine fires has the state's shape.** -/
theorem shape (hp : Pre p L m) : (code p L g).Shape (Ev p L g) :=
  Code.Shape.of_at (shapeAt hp)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
