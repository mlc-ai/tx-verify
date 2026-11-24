-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Data.Decoded
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.OpPcsFast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow Decoded

private def functionExit (op : Op) : Bool :=
  match op with
  | .ret | .exit => true
  | _ => false

private theorem functionExitCode : OpPcsFast kernel.code functionExit [9205] = true := by
  decide +kernel

/-- Every observed return is issued at the decoded terminal instruction. -/
theorem actualExitPc {A : List Assumption} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {pc : Nat}
    (hx : X.get i = some ⟨pc, .exit⟩) : pc = 9205 := by
  rcases get_source hX hx with ⟨_, hn⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hn
  · have hOp := fires_exit_op hf rfl
    have hb : functionExit ins.op = true := by
      rcases hOp with h | h
      · rw [h]; rfl
      · rw [h]; rfl
    exact List.mem_singleton.mp (OpPcsFast.mem functionExitCode hc hb)

end PTX.Kernels.TmlFa4Fwd
