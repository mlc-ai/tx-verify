-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface
public import Lemmas.Tcgen05.MemFloat
public import Lemmas.Kernel.Memory

@[expose] public section

/-! # The memory after a complete execution

Byte `z` of output element `(i, j)` has one writer (`OutputWrites`), which writes the dot
product's byte (`OutputValues`), so the final memory holds it and the element reads as the dot
product (`memFloat_float`); a global byte outside `D` has no writer (`GlobalWrites`), so the final
memory holds its launch content (`post_of`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX

noncomputable section

namespace Result

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A global byte outside `D` has no writer. -/
theorem frame (hw : GlobalWrites P X) {l : Loc} (hs : l.space = .global)
    (hout : ¬ (l.cta = 0 ∧ P.dBase ≤ l.addr ∧ l.addr < P.dBase + matrixBytes)) :
    ∀ w a bs, X.MemWrites w a bs → ¬ a.Covers l := by
  intro w a bs hm hc
  obtain ⟨hsp, hcta, hlo, hhi⟩ := hc
  obtain ⟨h1, h2, h3, h4, -⟩ := hw w a bs hm (hsp ▸ hs)
  rw [h1] at hhi
  exact hout ⟨hcta.trans h2, by omega, by omega⟩

/-- The final memory of a complete execution holds byte `z` of every output element's ideal
value, from the element byte's only writer. -/
theorem output_bytes (ho : OutputWrites P L X) (hv : OutputValues P L X) {m : FinalMem}
    (hf : IsFinal L mem0 X m) {i j z : Nat} (hi : i < 8192) (hj : j < 8192) (hz : z < 2) :
    m ((elementLoc P.dBase i j).at z) = some (some ((Value.float .f16 (dot P i j)).byteAt z)) := by
  obtain ⟨g, k, pc, a, sp, c, s, x, y, o, b, he, hσ, hs', hx, hy, hrow, hcol, ho', hb, hm,
    hu⟩ := ho i hi j hj z hz
  have hval := hv g k pc a sp c s x y z o b he hσ hs' hx hy hz ho' hb
  rw [hrow, hcol] at hval
  let l := (elementLoc P.dBase i j).at z
  have hcov : ({ loc := l, size := 1, acquire := false, release := false, scope := .cta } :
      Acc).Covers l := ⟨rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
  have hmem := hf.unique hm hcov hu
  change m l = _
  simp only [hmem, hval, wbyte, l, Nat.sub_self, List.getElem?_cons_zero]

/-- **The final memory of a complete execution is the specified output**, from its writes. -/
theorem post_of (hw : GlobalWrites P X) (ho : OutputWrites P L X) (hv : OutputValues P L X)
    {m : FinalMem} (hf : IsFinal L mem0 X m) : Post P mem0 m :=
  ⟨fun _ hi _ hj => memFloat_float fun _ hz => output_bytes ho hv hf hi hj hz,
    fun _ hs hout => hf.unwritten (frame hw hs hout)⟩

end Result

end

end PTX.Kernels.Fp16Gemm8192.Proof
