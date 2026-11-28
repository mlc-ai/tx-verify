-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.StepsBegin
public import Kernels.InklingRelDecode.Proof.Loader.NoUbSite
import Kernels.InklingRelDecode.Proof.Loader.StepsLast
import Kernels.InklingRelDecode.Proof.Loader.StepsRead
import Kernels.InklingRelDecode.Proof.Loader.StepsPage
import Kernels.InklingRelDecode.Proof.Loader.Steps
import Kernels.InklingRelDecode.Gen.StepDispatch

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX.Flow

/-- The hand-off site is the first observable instruction of dispatch. -/
theorem dispatch_step {L : Launch} {g : Nat} {w : Value} {regs : Nat → Value} (i n a b : Value) :
    (code L g w regs).StepAtU ⟨.dispatch,i,n,a,b⟩ := by
  exact ⟨fun _ => ⟨_, Flow.code_2337, rfl, trivial⟩, fun _ _ _ _ _ => .inl (.inl rfl)⟩

theorem stepsU {Q : Params} {L : Launch} {g : Nat} {w : Value} {rest : Nat → Value} (d : D) :
    (code L g w (inputs Q L g rest)).StepAtU d := by
  obtain ⟨s,i,n,a,b⟩ := d
  cases s with
  | dec => exact (dec_step ..).toStepAtU
  | first => exact (first_step ..).toStepAtU
  | second => exact (second_step ..).toStepAtU
  | beginBar => exact beginBar_step ..
  | poll => exact (poll_step ..).toStepAtU
  | readyBar => exact (readyBar_step ..).toStepAtU
  | arrive => exact (arrive_step ..).toStepAtU
  | page upper => exact page_step i n a b upper
  | warpBar pair => exact (warpBar_step i n a b pair).toStepAtU
  | elect pair =>
    by_cases h : pair.val < 3
    · exact (elect_pair_step i n a b pair h).toStepAtU
    · have : pair = 3 := Fin.ext (by omega)
      subst pair
      exact elect_last_step ..
  | copy pair upper =>
    cases upper with
    | false => exact (copy_first_step i n a b pair).toStepAtU
    | true =>
      by_cases h : pair.val < 3
      · exact (copy_second_step i n a b pair h).toStepAtU
      · have : pair = 3 := Fin.ext (by omega)
        subst pair
        exact copy_last_step ..
  | endBar => exact (endBar_step ..).toStepAtU
  | inc => exact (inc_step ..).toStepAtU
  | dispatch => exact dispatch_step ..

end PTX.Kernels.InklingRelDecode.Proof.Loader
