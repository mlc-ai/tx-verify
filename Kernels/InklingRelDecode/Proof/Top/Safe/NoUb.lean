-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.Export.NoUb
import Kernels.InklingRelDecode.Proof.Protocol.Shared.BaseZero
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Top.Safe.LateValues
public import Kernels.InklingRelDecode.Proof.Softmax.Export.NoUbLane
import Kernels.InklingRelDecode.Proof.Top.Safe.NoUbLate
import Kernels.InklingRelDecode.Proof.Top.Safe.NoRace
import Kernels.InklingRelDecode.Proof.Top.Safe.NoAssumptionUb
import Kernels.InklingRelDecode.Proof.Top.Inputs
import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvCopyForm
import Kernels.InklingRelDecode.Proof.Top.Result.Frame
import Kernels.InklingRelDecode.Proof.Prologue.Export.NoUbLane

@[expose] public section

/-! # ERR-UB: no execution has undefined behaviour

A lane's first undefined-behaviour event ends the lane, so the lane's earlier events are all
ordinary, and every state the machine of the lane held before it was strictly good
(`Frame.noUb_strict_lane`). That is proved for the startup (`Startup.Export.noUb_early`) and for
every worker lane (`worker_noUb`), for any pc, and at the prologue's pcs by
`Prologue.Export.noUb_prologue`: so undefined behaviour is only in a data lane from pc 574 on
(`Safe.noUbOutside`). Race freedom and the value facts follow from that, and then no data lane has
it at the softmax and epilogue pcs (`Safe.noUbLate`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **Undefined behaviour is in a data lane at a pc from 574 on**: workers never fault, and a data
lane does not in the prologue. -/
theorem Safe.noUbOutside (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) :
    NoUbOutside L X := by
  intro g k pc f he
  have base : Iface.BaseRead L X := Protocol.Shared.base_read hp hX hf
  obtain ⟨lane, -⟩ := Export.ub_past_startup hp hX hf base
    (fun h => Protocol.Shared.role_bytes hp hX h)
    (fun h site => Protocol.Shared.published_counts hp hX h site) he
  refine ⟨lane, ?_⟩
  by_contra hlt
  exact Prologue.Export.noUb_prologue hp hX hf base he lane (by unfold SoftEpiPc at hlt; omega)

theorem Safe.noUb (hp : Pre Q L m)
    {X : Execution} (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) :
    ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, he⟩
  have hou := Safe.noUbOutside hp hX hf
  obtain ⟨lane, hpc⟩ := hou g k pc f he
  have init := initRows_of hp hX hf
  have rows := mbarRows_of hp hX hf
  have nub : ¬ Assumptions.inputReadOnly.ub L m X := fun h =>
    Safe.noAssumptionUb hp hX (Result.output_placed hp hX hf) ⟨_, by simp [Assumptions.all], h⟩
  have race := Safe.noRace hp hX hf rows init (fun h => Protocol.Shared.role_bytes hp hX h) hou
    (Protocol.Shared.global_reads hp hX hf (Protocol.Shared.tensor_input_bytes hp hX hf)) nub
  exact Safe.noUbLate hp hX hf (Protocol.Shared.base_read hp hX hf)
    (Safe.lateValues hp hX hf hou race rows init nub) lane he hpc

end PTX.Kernels.InklingRelDecode.Proof.Top
