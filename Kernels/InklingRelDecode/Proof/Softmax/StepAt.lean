-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Arrive
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Entry
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Broadcast
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Butterfly
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.First
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Linear
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Poll
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Publish
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.RescaleBranch
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.RescaleWord
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Tiles

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

private theorem bias_step {e L g i v} (b : Bias) (j : Fin 64) :
    (code e L g).StepAtU ⟨b.site j,i,v⟩ := by
  by_cases h : j.val < 63
  · exact Bias.step_inner b ⟨j.val,h⟩
  · have eq : j = 63 := Fin.ext (show j.val = 63 by omega)
    subst j
    cases b
    · exact step_last_pre
    · exact step_last_nxt

/-- Every softmax state, including the hand-off at the epilogue poll. The entry
bounds used by the conditional steps are in the machine invariant. -/
theorem stepAt {e L g} (d : D) : (code e L g).StepAtU d := by
  obtain ⟨s,i,v⟩ := d
  cases s with
  | setMaxReg => exact step_entry
  | bar0 => exact step_bar0
  | pre j => exact bias_step .pre j
  | nxt j => exact bias_step .nxt j
  | waitS => exact step_waitS
  | shfl4 => exact step_shfl4
  | ldS => exact step_ldS
  | waitLd => exact step_waitLd
  | shfl5 => exact step_shfl5
  | shfl6 => exact step_shfl6
  | waitO => exact step_waitO
  | bar22 => exact step_bar22
  | shfl7 => exact step_shfl7
  | shfl8 => exact step_shfl8
  | shfl9 => exact step_shfl9
  | shfl10 => exact step_shfl10
  | store10 => exact step_store10
  | bar23 => exact step_bar23
  | ldL => exact step_ldL
  | shfl11 => exact step_shfl11
  | shfl12 => exact step_shfl12
  | ldO => exact step_ldO
  | waitLdO => exact step_waitLdO
  | bar24 => exact step_bar24
  | stO => exact step_stO
  | waitStO => exact step_waitStO
  | bar20 => exact step_bar20
  | tmemSt => exact step_tmemSt
  | tmemWait => exact step_tmemWait
  | bar21 => exact step_bar21
  | arrive => exact step_arrive
  | epilogue => exact step_handoff

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
