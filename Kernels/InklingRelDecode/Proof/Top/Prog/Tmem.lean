-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
import Kernels.InklingRelDecode.Proof.Common.Export.Tmem
import Kernels.InklingRelDecode.Proof.Top.Prog.Tc
import Kernels.InklingRelDecode.Proof.Lib.AssumptionStep
import Lemmas.Quiet.Progress.TmemOne

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

/-- A pending warp-zero resource request steps under a quiet extension. -/
public theorem Prog.tmem {Q L m} (hp : Pre Q L m) : Prog.Async Q L m [.tmem] := by
  intro hs X hm hf o mem hob
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  subst o
  exact Sched.tmem_one_stepsQ Lib.assumptions_step.wfQuiet hm (Export.tmem_ops hp hm.1 hf)
    hp.launchValid.1 (fun h => hs.2 X hm.1 (by simp [Unsafe,h])) hob

end PTX.Kernels.InklingRelDecode.Proof.Top
