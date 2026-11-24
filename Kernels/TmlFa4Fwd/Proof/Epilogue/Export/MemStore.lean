-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.StoreReady
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Assign
import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # What the output warp's tensor stores read

A tensor store reads the 16384 bytes of one of its CTA's eight staging boxes: box `bx` of stage `st`
is at `sb + 3072 + 65536 st + 16384 bx` (`storeRead_box`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A tensor store reads inside one staging box of its CTA. -/
theorem storeRead_box (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {i : EvId}
    {addr : Nat} {s : TensorStore.Spec} (hw : Prologue.warpIndex L i.1 = 13)
    (hi : X.TensorStoreIssue i addr s) : ∃ st : Fin 2,
      ∃ bx : Fin 4, ∀ x y k l, TensorStore.readLoc s x y k = some l →
      l.space = .shared ∧ l.cta = i.1 / L.block ∧
      L.sharedBase + 3072 + 65536 * st.val + 16384 * bx.val ≤ l.addr ∧
      l.addr < L.sharedBase + 3072 + 65536 * st.val + 16384 * bx.val + 16384 := by
  obtain ⟨st, bx, -, h⟩ := store_read_ready hp hX hw hi
  exact ⟨st, bx, h⟩

/-- **No tensor store reduces.** -/
theorem store_reduce (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {i : EvId}
    {addr : Nat} {s : TensorStore.Spec} (hw : Prologue.warpIndex L i.1 = 13)
    (hi : X.TensorStoreIssue i addr s) : s.reduce = none := by
  obtain ⟨-, b, -, st, bx, -, -, rfl⟩ := Epilogue.store_issue hp hX hw hi
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof
