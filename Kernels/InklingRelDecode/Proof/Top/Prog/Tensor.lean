-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
import Kernels.InklingRelDecode.Proof.Lib.AssumptionStep

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

/-- Every issued copy can drain once its coordinate row places global sources
in the launch inputs. The read-only safety clause protects those bytes from
every writer, including a pending asynchronous writer. -/
public theorem Prog.tensor {Q L m X} (hp : Pre Q L m) (hm : Maximal L kernel Assumptions.all m X)
    (hs : ¬ Unsafe L kernel Assumptions.all m X) (inputs : Protocol.Shared.TensorInputBytes Q X)
    (o : Descent.Obl L X .tensor) : Sched.Steps (schedule Q L) m X .tensor :=
  Sched.tensor_stepsQ Lib.assumptions_step.wfQuiet hm
    (Protocol.Shared.tensor_sources hp hm.1 hs inputs) o

end PTX.Kernels.InklingRelDecode.Proof.Top
