-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
import Lemmas.Flow.AccessLocal
import Lemmas.Flow.NotBulk
import Lemmas.Flow.OpPcsFast

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

private def localLoad (op : Op) : Bool :=
  loadSpace op == some .local || loadSpace op == some .const || (dynamicAccess op && readOp op)

private theorem load_sites : OpPcsFast kernel.code localLoad [13,2340,2345,2423] = true := by
  decide +kernel

/-- A thread load of the local or constant space is one of the four generic loads. -/
theorem load_off_space {L m X g k pc a bs} (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g,k) = some ⟨pc,.rd a bs⟩)
    (sp : a.loc.space = .local ∨ a.loc.space = .const) : pc ∈ [13,2340,2345,2423] := by
  obtain ⟨_,bad⟩ | ⟨_,_,_,_,code,fire⟩ := get_source hX get
  · cases bad
  apply OpPcsFast.mem load_sites code
  rcases fires_read_loc fire rfl with ⟨h,_⟩ | dyn
  · rcases sp with sp | sp <;> simp [localLoad,h,sp]
  · simp [localLoad,dyn,fires_read_op fire rfl]

end PTX.Kernels.InklingRelDecode.Proof.Lib
