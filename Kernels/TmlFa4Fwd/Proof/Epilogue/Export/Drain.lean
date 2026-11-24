-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Kernel.Safety.ClassPcs
import Kernels.TmlFa4Fwd.Proof.Epilogue.Drain
import Lemmas.Async.BulkCommitted
import Lemmas.Flow.NotClc
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output warp's tensor stores are drained before its exits

A read wait of the lane covers each of its tensor stores before its exit (`store_wait`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

theorem kernel_exit : OpPcsFast kernel.code Frame.isRetOp [9205] = true := by decide +kernel

/-- **A read wait between a tensor store and its lane's exit** covers the store. -/
theorem store_wait {p : Params} {L : Launch} {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) {g k pc pcx a : Nat} {s : TensorStore.Spec}
    (hw : Prologue.warpIndex L g = 13)
    (he : X.get (g, k) = some ⟨pc, .tensorStore a s⟩)
    (hx : X.get (g, (X.tr g).length - 1) = some ⟨pcx, .exit⟩) :
    ∃ w pcw, w + 1 < (X.tr g).length ∧ X.get (g, w) = some ⟨pcw, .bulkWait .read 0⟩ ∧
      BulkWaitsFor X .read (g, k) (g, w) := by
  have hpcx : pcx = 9205 := by
    rcases get_source hX hx with ⟨_, h⟩ | ⟨t, ins, o, -, hc, hf⟩
    · cases h
    · have := OpPcsFast.mem kernel_exit hc
        (by rcases fires_exit_op hf rfl with h | h <;> rw [h] <;> rfl)
      simpa using this
  subst hpcx
  obtain ⟨c, w, hkc, hcw, hwl, hcm, hwt⟩ := commit_wait hp hX hw he (by
    rw [List.getLast?_eq_getElem?]; exact hx)
  exact ⟨w, _, hwl, hwt, bulkWaitsFor_of_commit he hcm hwt hkc hcw⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
