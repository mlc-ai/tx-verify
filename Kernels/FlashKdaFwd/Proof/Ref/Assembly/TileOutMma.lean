-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Example
public import Kernels.FlashKdaFwd.Proof.Values.TileClaim
public import Kernels.FlashKdaFwd.Proof.Top.Wire

@[expose] public section

/-!
# The operands of every warp-level multiply-accumulate, from the claim of the tile induction

`Top.DirectFacts.mmaOperands` (`Proof/Top/Wire.lean`; the same statement is the field
`mmaOperands` of `DataHalf`, `Ref/Assembly/DirectData.lean`) speaks of every *warp instance* of
an `mma.sync`: a thread `w` with lane 0 (`laneOf L w = 0`) such that each of the 32 threads
`w + lane` makes, as its matrix event number `n`, a multiply-accumulate at instruction `pc`
(`WarpMatrix.WarpInstance`). The conclusion of the tile induction, `Values.TileClaim.mma`, is
the same statement for the first thread `c * L.block + 32 * w'` of a *compute warp* (`w' < 4`)
of a thread block `c` (`c < L.grid`).

The step between the two: a matrix event is made only by a compute thread (a thread whose
index in its block is below 128; `Example.matrix_in_compute`, from the chain of the phases). So
the first thread of the instance is a launched compute thread with lane 0, which is the first
thread of a compute warp. The warps of the load and of the store role (indices 128 to 191) have
no matrix instance.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace TileOut

/-- **A thread that makes a matrix event and has lane 0 is the first thread of a compute warp**
of a launched thread block: `w = c * L.block + 32 * w'` with `c < L.grid` and `w' < 4`. -/
theorem warp_of_matrix (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {w k : ℕ} {e : Event} (he : X.get (w, k) = some e) (hm : isMatrix e = true)
    (hlane : laneOf L w = 0) :
    w / L.block < L.grid ∧ w % L.block / 32 < 4 ∧
      w = w / L.block * L.block + 32 * (w % L.block / 32) := by
  have hlt : w < L.threads := Frame.lt_of_get hX he
  have htid : tid w < 128 := (Example.matrix_in_compute hpre hX he hm).1
  have hb := hpre.block
  unfold laneOf at hlane
  unfold tid at htid
  unfold Launch.threads at hlt
  rw [hb] at hlane hlt ⊢
  refine ⟨(Nat.div_lt_iff_lt_mul (by norm_num)).mpr hlt, by omega, by omega⟩

end TileOut

/-- **`DirectFacts.mmaOperands`, for every warp.** In every instance of a warp-level
multiply-accumulate the instruction is the bfloat16 `m16n8k16` form and the registers the 32
lanes contribute hold real matrices. For a compute warp this is the claim of the tile induction
(`TileClaim.mma`); no other warp has a matrix instance. -/
theorem mmaOperands (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (T : Values.TileClaim P L mem0 X) :
    ∀ w n pc s parts, laneOf L w = 0 →
      WarpMatrix.WarpInstance X w n pc (.mma s) parts →
      s = WarpMatrix.mma16 ∧ ∃ ra rb rc a b c, WarpMatrix.Operands ra rb rc a b c ∧
        ∀ l < 32, parts l = WarpMatrix.mmaParts ra rb rc l := by
  intro w n pc s parts hlane hW
  obtain ⟨j, recv, he, -⟩ := hW 0 (by omega)
  rw [Nat.add_zero] at he
  obtain ⟨hc, hw4, hw⟩ := TileOut.warp_of_matrix hpre hX he rfl hlane
  rw [hw] at hW
  exact T.mma _ _ hc hw4 n pc s parts hW

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
