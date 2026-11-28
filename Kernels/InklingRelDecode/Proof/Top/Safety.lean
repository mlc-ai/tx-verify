-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Followed
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoUb
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoUnalloc
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoRace
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoMixed
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoBarMismatch
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTma
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemSource
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoAssumptionUb
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoSharedLifetime
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoClc
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTensor
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTensorStore
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTensorAllocation
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemResource
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemRelease
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoPollShape
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTcCommit
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemInstruction
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoRegister
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoCtaBar
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoCluster
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoWarpDivergence
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoMatrix
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoUninit
public import Kernels.InklingRelDecode.Proof.Top.Result.Output
public import Kernels.InklingRelDecode.Proof.Top.Result.Lse
public import Kernels.InklingRelDecode.Proof.Top.Result.Frame
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Top.Inputs
import Kernels.InklingRelDecode.Proof.Protocol.Shared.BaseZero
import Kernels.InklingRelDecode.Proof.Top.Safe.NoAligned
import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemAccess
import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemWrites
import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemReads
import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemSource
import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvCopyForm

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem safe (hp : Pre Q L m) : SafeGoal kernel Assumptions.all L m := by
  refine ⟨Lib.tcGroupUniform, fun X hX => ?_⟩
  have hf := followed hp hX
  have init := initRows_of hp hX hf
  have rows := mbarRows_of hp hX hf
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have hu := Safe.noUb hp hX hf
  have gr := Protocol.Shared.global_reads hp hX hf (Protocol.Shared.tensor_input_bytes hp hX hf)
  have nub : ¬ Assumptions.inputReadOnly.ub L m X := fun h =>
    Safe.noAssumptionUb hp hX (Result.output_placed hp hX hf) ⟨_,by simp [Assumptions.all],h⟩
  have race := Safe.noRace hp hX hf rows init words (.of_noUb hu) gr nub
  have aligned := Safe.noAligned hp (Protocol.Shared.base_read hp hX hf) hX hf race
  simp only [Unsafe,
    Safe.noUb hp hX hf,
    Safe.noUnalloc hp hX hf rows init gr (Result.output_placed hp hX hf),
    race,
    Safe.noMixed hp hX hf rows init words hu gr nub,
    Safe.noBarMismatch hp hX aligned,
    Safe.noTma hp hX hf rows init,
    Safe.noTmemSource hp (Protocol.Shared.base_read hp hX hf) hX hf hu race rows init
      (Safe.completed hp hX hf hu race rows init nub),
    Safe.noAssumptionUb hp hX (Result.output_placed hp hX hf),
    aligned,
    Safe.noSharedLifetime hp (Protocol.Shared.base_read hp hX hf) hX hf hu rows init,
    Safe.noClc hX,
    Safe.noTensor hp hX,
    Safe.noTensorStore hX,
    Safe.noTensorAllocation hp hX hf,
    Safe.noTmemResource hp (Protocol.Shared.base_read hp hX hf) hX hf,
    Safe.noTmemRelease hp (Protocol.Shared.base_read hp hX hf) hX hf,
    Safe.noPollShape hX,
    Safe.noTmemAccess hp (Protocol.Shared.base_read hp hX hf) hX hf hu race rows init,
    Safe.noTcCommit hp hX,
    Safe.noTmemWrites hp (Protocol.Shared.base_read hp hX hf) hX hf hu race rows init,
    Safe.noTmemInstruction hp (Protocol.Shared.base_read hp hX hf)
      (Safe.completed hp hX hf hu race rows init nub) hX hf,
    Safe.noTmemReads hp (Protocol.Shared.base_read hp hX hf) hX hf hu race rows init,
    Safe.noRegister hp hX hf,
    Safe.noCtaBar hp hX hf words race,
    Safe.noCluster hX,
    Safe.noWarpDivergence hp hX hf rows,
    Safe.noMatrix hX,
    Safe.noUninit init, or_self, not_false_eq_true]

end PTX.Kernels.InklingRelDecode.Proof.Top
