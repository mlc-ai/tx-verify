-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Assign
import Lemmas.Tensor.TensorSwizzle
import Kernels.TmlFa4Fwd.Proof.Epilogue.Assign

@[expose] public section

/-! # A tensor store's bytes and its ready poll (`store_read_ready`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A tensor store follows its stage's ready poll** and reads bytes of one of its boxes. -/
theorem store_read_ready (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {i : EvId}
    {addr : Nat} {s : TensorStore.Spec} (hw : Prologue.warpIndex L i.1 = 13)
    (hi : X.TensorStoreIssue i addr s) : ∃ st : Fin 2,
      ∃ bx : Fin 4, (∃ j < i.2, X.get (i.1, j) =
        some ⟨(Epilogue.Site.ready st).pc, .wait (Epilogue.readyLoc L i.1 st) 0 true true .cta⟩) ∧
      ∀ x y k l, TensorStore.readLoc s x y k = some l →
      l.space = .shared ∧ l.cta = i.1 / L.block ∧
      L.sharedBase + 3072 + 65536 * st.val + 16384 * bx.val ≤ l.addr ∧
      l.addr < L.sharedBase + 3072 + 65536 * st.val + 16384 * bx.val + 16384 := by
  obtain ⟨st', bx', hb, j, hj, hwt⟩ := Epilogue.store_ready hp hX hw hi
  obtain ⟨-, b, -, st, bx, -, -, rfl⟩ := Epilogue.store_issue hp hX hw hi
  have hst : st = st' := by
    have h1 := congrArg Loc.addr hb
    simp only [Epilogue.writebackStoreSpec, Epilogue.sharedSlot] at h1
    have := st.isLt
    have := st'.isLt
    have := bx.isLt
    have := bx'.isLt
    exact Fin.ext (by omega)
  subst hst
  refine ⟨st, bx, ⟨j, hj, hwt⟩, fun x y k l h => ?_⟩
  unfold TensorStore.readLoc at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨x', y', k'⟩, -, rfl⟩ := h
  have hc0 : TensorTile.count p.oMap.box 0 = 32 := by
    simp [Params.oMap, TensorTile.count, TensorTile.step]
  have hc1 : TensorTile.rows p.oMap.box = 128 := by
    simp [Params.oMap, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step]
  have hx' : x'.val < TensorTile.count p.oMap.box 0 := x'.isLt
  have hy' : y'.val < TensorTile.rows p.oMap.box := y'.isLt
  rw [hc0] at hx'
  rw [hc1] at hy'
  have hk' : k'.val < 4 := k'.isLt
  refine ⟨rfl, rfl, ?_⟩
  simp only [Epilogue.writebackStoreSpec, TensorBox.sharedLoc, TensorTile.sharedByte,
    Epilogue.sharedSlot]
  have hlin : TensorTile.linearByte p.oMap.box p.oMap.format.bytes p.oMap.swizzle x'.val y'.val
      k'.val = y'.val * 128 + x'.val * 4 + k'.val := by
    have hf : p.oMap.format.bytes = 4 := rfl
    have hs : p.oMap.swizzle = .b128 := rfl
    simp only [TensorTile.linearByte, TensorTile.rowBytes, hc0, hf, hs, TensorTile.swizzleWidth]
    norm_num
  have hr := TensorSwizzle.offset_row p.oMap.swizzle
    (L.sharedBase + (3072 + 65536 * st.val + 16384 * bx.val))
    (y'.val * 128 + x'.val * 4 + k'.val)
  rw [hlin]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
