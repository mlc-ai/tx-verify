-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Run
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Poll
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Fold
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Load
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Tiles
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Bcast
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Bias
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.BiasN
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Arrive
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteL
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteP
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteC
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteJ
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteK
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteR
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteS
public import Lemmas.Flow.StepsQFOs

@[expose] public section

/-! # The strict step of every site of the softmax

`step_soft` dispatches on the site; the exit has no step (a glued machine leaves the softmax at
the exit). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

variable {e : Control.Entry} {L : Launch} {g : Nat}

/-- The steps that read the entry's base word are those of the entry with it. -/
theorem base_eq (hb : e.base = b32 0) : e = {e with base := b32 0} := by
  cases e
  cases hb
  rfl

/-- **Every state of the softmax but the exit steps strictly.** -/
theorem step_soft (hb : e.base = b32 0) (hsc : ScaleOk L) (d : Data.D)
    (hs : d.c.site ≠ .epilogue) (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf d ev := by
  obtain ⟨⟨s, i, v⟩, w⟩ := d
  cases s with
  | setMaxReg => exact sstep_setMaxReg ev
  | bar0 => exact sstep_bar0 hsc ev
  | pre j =>
    by_cases h : j.val + 1 < 64
    · exact sstep_pre j h ev
    · obtain rfl : j = 63 := Fin.ext (by omega)
      exact sstep_pre_last ev
  | nxt j =>
    by_cases h : j.val + 1 < 64
    · exact sstep_nxt j h ev
    · obtain rfl : j = 63 := Fin.ext (by omega)
      exact sstep_nxt_last ev
  | waitS => rw [base_eq hb]; exact sstep_waitS e ev
  | shfl4 => rw [base_eq hb]; exact sstep_shfl4 e ev
  | ldS => exact sstep_ldS ev
  | waitLd => exact sstep_waitLd ev
  | shfl5 => exact sstep_shfl5 ev
  | shfl6 => exact sstep_shfl6 ev
  | bar22 => exact sstep_bar22 ev
  | shfl7 => exact sstep_shfl7 ev
  | shfl8 => exact sstep_shfl8 ev
  | shfl9 => exact sstep_shfl9 ev
  | shfl10 => exact sstep_shfl10 ev
  | store10 => exact sstep_store10 ev
  | bar23 => exact sstep_bar23 ev
  | ldL => exact sstep_ldL ev
  | shfl11 => exact sstep_shfl11 ev
  | shfl12 => rw [base_eq hb]; exact sstep_shfl12 e ev
  | waitO => exact sstep_waitO ev
  | ldO => exact sstep_ldO ev
  | waitLdO => exact sstep_waitLdO ev
  | bar24 => exact sstep_bar24 ev
  | stO => exact sstep_stO ev
  | waitStO => exact sstep_waitStO ev
  | bar20 => exact sstep_bar20 ev
  | tmemSt => exact sstep_tmemSt ev
  | tmemWait => exact sstep_tmemWait ev
  | bar21 => exact sstep_bar21 ev
  | arrive => exact sstep_arrive ev
  | epilogue => exact absurd rfl hs

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
