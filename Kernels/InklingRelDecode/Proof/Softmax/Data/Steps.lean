-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Frames
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Bias
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Cross
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Init
public import Kernels.InklingRelDecode.Proof.Softmax.Data.RescaleSteps
public import Kernels.InklingRelDecode.Proof.Softmax.StepAt

@[expose] public section

/-! # The softmax value machine takes every step the control machine takes -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The epilogue state has no successor. -/
theorem data_epilogue {d : D} (hs : d.c.site = .epilogue) : DataStep (code e L g) (dF L) d := by
  intro t ev u d' ins hat hi hc' hf hn
  obtain ⟨c', hnc, -⟩ := succ_inv hn
  simp [Control.next, hs] at hnc

/-- **The data step of every state.** -/
theorem data_step (d : D) : DataStep (code e L g) (dF L) d := by
  obtain ⟨⟨s, i, h⟩, v⟩ := d
  cases s with
  | setMaxReg => exact data_setMaxReg rfl
  | bar0 => exact data_bar0 rfl
  | pre j =>
    by_cases hj : j.val + 1 < 64
    · exact data_pre rfl hj
    · have : j = 63 := Fin.ext (by omega)
      subst this
      exact data_pre63 rfl
  | nxt j => exact data_nxt rfl
  | waitS => exact data_waitS rfl
  | shfl4 => exact data_shfl4 rfl
  | ldS => exact data_ldS rfl
  | waitLd => exact data_waitLd rfl
  | shfl5 => exact data_shfl5 rfl
  | shfl6 => exact data_shfl6 rfl
  | waitO => exact data_waitO rfl
  | bar22 => exact data_bar22 rfl
  | shfl7 => exact data_shfl7 rfl
  | shfl8 => exact data_shfl8 rfl
  | shfl9 => exact data_shfl9 rfl
  | shfl10 => exact data_shfl10 rfl
  | store10 => exact data_store10 rfl
  | bar23 => exact data_bar23 rfl
  | ldL => exact data_ldL rfl
  | shfl11 => exact data_shfl11 rfl
  | shfl12 => exact data_shfl12 rfl
  | ldO => exact data_ldO rfl
  | waitLdO => exact data_waitLdO rfl
  | bar24 => exact data_bar24 rfl
  | stO => exact data_stO rfl
  | waitStO => exact data_waitStO rfl
  | bar20 => exact data_bar20 rfl
  | tmemSt => exact data_tmemSt rfl
  | tmemWait => exact data_tmemWait rfl
  | bar21 => exact data_bar21 rfl
  | arrive => exact data_arrive rfl
  | epilogue => exact data_epilogue rfl

/-- **Every state of the value machine takes the step of the control machine and keeps the data
facts.** -/
theorem stepAt (d : D) : (code e L g).StepAtU d :=
  Code.Over.stepAtU (over e L g) (fun c => Control.stepAt c) (data_step d)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
