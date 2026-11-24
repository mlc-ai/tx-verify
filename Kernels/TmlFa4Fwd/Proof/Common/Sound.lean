-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Lemmas.Flow.CodeU
import Kernels.TmlFa4Fwd.Proof.Common.ControlHandoff
public import Kernels.TmlFa4Fwd.Proof.Common.DataSound
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Steps
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Steps
import Lemmas.Flow.GlueU
import Lemmas.Flow.CountedU

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX.Flow

theorem frag_stepsU {p L m g} (hp : Pre p L m) (hg : g < L.threads) (i : Role)
    (d : (frag p L g i).D) : (frag p L g i).StepAtU d := by
  cases i with
  | correction => exact Correction.Control.stepAtU hp hg d
  | softmax => exact SmWarp.control_step fun hw => Softmax.Control.stepAtU hp hg hw d
  | mma => exact (fragD_steps hp hg .mma d).toStepAtU
  | epilogue => exact (fragD_steps hp hg .epilogue d).toStepAtU
  | loader b => exact (fragD_steps hp hg (.loader b) d).toStepAtU
  | stub r => exact (fragD_steps hp hg (.stub r) d).toStepAtU

/-- The counted, glued control machine follows the concrete thread through any final UB. -/
theorem thread_sound {p L m g} (hp : Pre p L m) (hg : g < L.threads) :
    (thread p L g).SoundU :=
  Code.counted_soundU (Code.glue_soundU (start hp)
    (fun d hx => (startup_steps hp hg d hx).toStepAtU) (frag_stepsU hp hg) (handoffU hp hg))

end PTX.Kernels.TmlFa4Fwd.Proof
