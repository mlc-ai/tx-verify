-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.Rows
public import Kernels.InklingRelDecode.Proof.Lib.ScoreEv
public import Kernels.InklingRelDecode.Proof.Protocol.Values.FinalOut
import Kernels.InklingRelDecode.Proof.Protocol.Values.SoftPw
import Kernels.InklingRelDecode.Proof.Protocol.Values.NoRescale
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleOrder
import Kernels.InklingRelDecode.Proof.Softmax.Export.Exact
import Kernels.InklingRelDecode.Proof.Top.Safe.LateOWord
import Kernels.InklingRelDecode.Proof.Top.Safe.NoUb
import Kernels.InklingRelDecode.Proof.Top.Safe.NoRace
import Kernels.InklingRelDecode.Proof.Top.Safe.NoAssumptionUb
import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
import Kernels.InklingRelDecode.Proof.Top.Safe.ValEnv
import Kernels.InklingRelDecode.Proof.Top.Safe.NoClc
import Kernels.InklingRelDecode.Proof.Top.Inputs
import Kernels.InklingRelDecode.Proof.Top.Result.Frame
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvCopyForm

@[expose] public section

/-! # The epilogue's load returns the accumulator of the fold, in a complete execution

The environment of the value inductions as `Top/Safety.lean` builds it, and the accumulator load's
word by `final_out`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol.Values Lib.SoftRow

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **No thread of a launch without a cluster cancellation is canceled.** -/
theorem Result.notCanceled {X : Execution} (hX : Consistent L kernel Assumptions.all m X) :
    ∀ g, ¬ ClcCanceled L X g := by
  rintro h ⟨-, r, hr⟩
  obtain ⟨i, s, ts, -, ⟨pc, hi⟩, -⟩ := hX.clc.canceled_has_issue hr
  exact Lib.no_clc hX hi

/-- **Every score load of the lane is exact**: the score events of every lane. -/
theorem Result.scoreEv (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) :
    ∀ g, Lib.ScoreEv Q L g X := by
  have init := initRows_of hp hX hf
  have rows := mbarRows_of hp hX hf
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have hu := Safe.noUb hp hX hf
  have hou : NoUbOutside L X := .of_noUb hu
  have gr := Protocol.Shared.global_reads hp hX hf (Protocol.Shared.tensor_input_bytes hp hX hf)
  have nub : ¬ Assumptions.inputReadOnly.ub L m X := fun h =>
    Safe.noAssumptionUb hp hX (Result.output_placed hp hX hf) ⟨_, by simp [Assumptions.all], h⟩
  have race := Safe.noRace hp hX hf rows init words hou gr nub
  obtain ⟨base, -, hG, hws, ht, hmd, form⟩ := Safe.valEnv hp hX hf race rows init
  exact fun g => score_ev hp hX hf hou race base rows init hG hws ht hmd words nub form

/-- **The word of the epilogue's load of a valid row is the `o` of the row's fold.** -/
theorem Result.finalWord (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hc : Complete L X) (hf : Follow Q L X)
    {t k0 a vals sh j} (he : X.get (t, k0) = some ⟨2607, .tc (.ld a vals sh)⟩)
    (hj : j < vals.length)
    (valid : Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh a j).lane)) :
    vals[j]? = some (.float .f32 (rowState Q (ctaZ L (t / L.block)) (ctaXc L (t / L.block))
      (laneRow (tcDataCell L t sh a j).lane / 6)
      (ctaY L (t / L.block) * 6 + laneRow (tcDataCell L t sh a j).lane % 6)
      ((tcDataCell L t sh a j).column - 256)).o) := by
  have init := initRows_of hp hX hf
  have rows := mbarRows_of hp hX hf
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have hu := Safe.noUb hp hX hf
  have hou : NoUbOutside L X := .of_noUb hu
  have gr := Protocol.Shared.global_reads hp hX hf (Protocol.Shared.tensor_input_bytes hp hX hf)
  have nub : ¬ Assumptions.inputReadOnly.ub L m X := fun h =>
    Safe.noAssumptionUb hp hX (Result.output_placed hp hX hf) ⟨_, by simp [Assumptions.all], h⟩
  have race := Safe.noRace hp hX hf rows init words hou gr nub
  obtain ⟨base, -, hG, hws, ht, hmd, form⟩ := Safe.valEnv hp hX hf race rows init
  have hov := fun {t j a' ov sh'} (he : X.get (t, j) = some ⟨2260, .tc (.ld a' ov sh')⟩) =>
    Safe.ldOFloat hp hX hf hou race rows init nub he (.inl rfl)
  exact final_out hp hX hf hou race hG base rows init hws ht hmd words nub form
    (Safe.pWords hp hX hf hou race rows init nub)
    (pwords_soft hp hX hf hou race base rows init hG hws ht hmd words nub form)
    (fun get => Safe.rescaleFloat hp hX hf hou race rows init nub get)
    (Softmax.Export.rescale_ld hp hX) (Softmax.Export.ld_before_st hp hX)
    (rescale_al hp hX hf hou race base rows init hG hws ht hmd words nub form
      fun t j a' ov sh' he => hov he)
    (no_rescale_al hp hX hf hou race base rows init hG hws ht hmd words nub form
      (fun g hg => (hc.1 g hg).resolve_left (Result.notCanceled hX g))
      fun c => NoUbLane.of_noUb hu _)
    (rescale_bound hp hX hf) (fold_words Q L) hp.scalePos he hj valid

end PTX.Kernels.InklingRelDecode.Proof.Top
