-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemInstruction
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Lemmas.Tmem.Tmem1Protocol
public import Lemmas.Tmem.AccessCp
public import Kernels.InklingRelDecode.Proof.Iface.KvCopyForm
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemSource
import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvCopyForm
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Protocol.Shared.BaseZero
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AsyncDone
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PvStore
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.QkStore
import Kernels.InklingRelDecode.Proof.Common.Export.Tmem

@[expose] public section

/-! # The facts every value induction over the MMAs starts from -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **The environment of the value inductions**: base words, role bytes, acyclic Tensor Core order,
safe writes, the allocation facts and the form of the K and V copies. -/
theorem Safe.valEnv (hp : Pre Q L m) {X : Execution} (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (rows : MbarRows Q L X)
    (init : Protocol.Mbar.InitRows L X) :
    Iface.BaseRead L X ∧ RoleBytes L X ∧ SyncGuarded L kernel X ∧ TcMma.WritesSafe L X ∧
      Tmem.One.Tmem1Facts L X 0 ∧ Tmem.AccessCp.AsyncDoneDealloc L X ∧ Iface.KvCopyForm Q L X := by
  have base : Iface.BaseRead L X := Protocol.Shared.base_read hp hX hf
  have hws : TcMma.WritesSafe L X := not_not.mp
    (Tmem.writes_safe hp hX hf base (Tmem.qk_store_order hp hX hf safe base rows init)
      (Tmem.pv_store_order hp hX hf safe base rows init))
  exact ⟨base, fun h => Protocol.Shared.role_bytes hp hX h, Safe.guarded hp hX hf rows init, hws,
    Export.tmem_facts hp hX hf base, Tmem.async_done hp hX hf rows init base,
    Protocol.Shared.kv_copy_form hp hX hf⟩

end PTX.Kernels.InklingRelDecode.Proof.Top
