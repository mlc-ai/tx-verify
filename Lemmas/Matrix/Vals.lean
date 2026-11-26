-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Matrix.Mma
public import Lemmas.Flow.Matrix
public import Lemmas.Snoc.MatrixAppend

@[expose] public section

/-! # Warp matrix instructions, on the side of a site machine

A proof tool, generic over the kernel. `Lemmas/Matrix/{Move,Mma}.lean` say what a lane *receives*
from an instance of a matrix instruction and how Core's thread rule (`afterMatrix`) writes it to
the registers. A site machine that keeps data registers as opaque values does not use
`afterMatrix`: it records the values that the received bytes rebuild into (`Flow.matrixVals`) and
it describes what a lane *contributes* by `Flow.ownBytes` of the values of its source registers.
This file restates the closed forms for those two functions:

* `ownBytes_eq`, `ownBytes_mma`, `ownBytes_bf16`, `ownBytes_bf16_one`: the contribution of a lane
  whose registers hold the operands of a multiply-accumulate (`mmaParts`), four packed pairs of
  bf16 payloads (`regPart (fragRegs bf16Enc F)`) or one (`reg1Part (fragReg1 bf16Enc F)`).
* `matrixVals_bf16`, `matrixVals_bf16_one`, `matrixVals_mma`: the values rebuilt from the bytes
  of a load or `movmatrix` of bf16 payloads (packed pairs) and of a multiply-accumulate (f32
  payloads at the positions `cRow`, `cCol`).
* `lanes_of_event`, `WarpInstance.of_lanes`: when one lane of a warp has made its `n`-th matrix
  event and no lane of the warp has exited before making that many, all 32 lanes have made it
  (a matrix event that exists has returned, so its needs are filled, DEP-WARP-MATRIX); with the
  position, the operation and the contribution of each lane's event this is the instance.
-/

namespace PTX.WarpMatrix
open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ## Contributions -/

/-- The contribution of registers holding `vs`, value by value. -/
theorem ownBytes_eq (vs : List Value) :
    ownBytes vs = vs.flatMap fun v => v.toBytes.map some := by
  simp [ownBytes, List.map_flatMap]

/-- The contribution of the ten source registers of a multiply-accumulate is `mmaParts`. -/
theorem ownBytes_mma (ra rb rc : Nat → Nat → Value) (l : Nat) :
    ownBytes [ra l 0, ra l 1, ra l 2, ra l 3, rb l 0, rb l 1, rc l 0, rc l 1, rc l 2, rc l 3] =
      mmaParts ra rb rc l :=
  ownBytes_eq _

/-- The contribution of four registers that hold the fragments `F` of bf16 payloads. -/
theorem ownBytes_bf16 (F : Nat → Nat → Nat → ℝ) (l : Nat) :
    ownBytes ((List.range 4).map fun r => bf16Pair (F l r 0) (F l r 1)) =
      regPart (fragRegs bf16Enc F) l := by
  rw [ownBytes_eq, regPart_bf16]

/-- The contribution of one register that holds the fragment `F` of bf16 payloads. -/
theorem ownBytes_bf16_one (F : Nat → Nat → ℝ) (l : Nat) :
    ownBytes [bf16Pair (F l 0) (F l 1)] = reg1Part (fragReg1 bf16Enc F) l := by
  rw [ownBytes_eq, reg1Part_bf16]
  simp

/-! ## Rebuilt values -/

/-- The four bytes of an f32 payload rebuild to it (THREAD-BYTES). -/
theorem rebuild_f32 (x : ℝ) :
    rebuild 3 ((Value.float .f32 x).toBytes.map some) = .ok (.float .f32 x) := by
  simp [rebuild, Value.bytes, FloatFmt.bytes, Value.toBytes, Value.byteAt, List.range_succ, pure,
    Except.pure]

/-- **The values after a load of bf16 elements.** A lane that receives the register bytes of
the fragments `F` of bf16 payloads (`ld4_elems` with `enc := bf16Enc`) records, for its four
destination registers, the packed pairs `bf16Pair (F l r 0) (F l r 1)`. -/
theorem matrixVals_bf16 (F : Nat → Nat → Nat → ℝ) (l : Nat) :
    matrixVals 32 4 (regPart (fragRegs bf16Enc F) l) =
      .ok ((List.range 4).map fun r => bf16Pair (F l r 0) (F l r 1)) := by
  have h : regPart (fragRegs bf16Enc F) l =
      [bf16Enc (F l 0 0) 0, bf16Enc (F l 0 0) 1, bf16Enc (F l 0 1) 0, bf16Enc (F l 0 1) 1,
       bf16Enc (F l 1 0) 0, bf16Enc (F l 1 0) 1, bf16Enc (F l 1 1) 0, bf16Enc (F l 1 1) 1,
       bf16Enc (F l 2 0) 0, bf16Enc (F l 2 0) 1, bf16Enc (F l 2 1) 0, bf16Enc (F l 2 1) 1,
       bf16Enc (F l 3 0) 0, bf16Enc (F l 3 0) 1, bf16Enc (F l 3 1) 0, bf16Enc (F l 3 1) 1] :=
    rfl
  rw [h]
  exact matrixVals_x4.mpr ⟨rfl, _, _, _, _, rfl, rebuild_bf16Pair _ _, rebuild_bf16Pair _ _,
    rebuild_bf16Pair _ _, rebuild_bf16Pair _ _⟩

/-- **The value after `movmatrix` of bf16 elements.** A lane that receives the register bytes
of the fragment `F` of bf16 payloads (`mov_elems`) records the packed pair. -/
theorem matrixVals_bf16_one (F : Nat → Nat → ℝ) (l : Nat) :
    matrixVals 32 1 (reg1Part (fragReg1 bf16Enc F) l) = .ok [bf16Pair (F l 0) (F l 1)] := by
  have h : reg1Part (fragReg1 bf16Enc F) l =
      [bf16Enc (F l 0) 0, bf16Enc (F l 0) 1, bf16Enc (F l 1) 0, bf16Enc (F l 1) 1] := rfl
  rw [h]
  exact matrixVals_x1.mpr ⟨rfl, _, rfl, rebuild_bf16Pair _ _⟩

/-- **The values after a multiply-accumulate.** A lane that receives `outParts d l` records,
for its four destination registers, the f32 payloads `d (cRow l r) (cCol l r)`. -/
theorem matrixVals_mma (d : Nat → Nat → ℝ) (l : Nat) :
    matrixVals 32 4 (outParts d l) =
      .ok ((List.range 4).map fun r => Value.float .f32 (d (cRow l r) (cCol l r))) := by
  have h : outParts d l =
      (Value.float .f32 (d (cRow l 0) (cCol l 0))).toBytes.map some ++
      ((Value.float .f32 (d (cRow l 1) (cCol l 1))).toBytes.map some ++
      ((Value.float .f32 (d (cRow l 2) (cCol l 2))).toBytes.map some ++
      (Value.float .f32 (d (cRow l 3) (cCol l 3))).toBytes.map some)) := rfl
  rw [h]
  exact matrixVals_x4.mpr ⟨rfl, _, _, _, _, rfl, rebuild_f32 _, rebuild_f32 _, rebuild_f32 _,
    rebuild_f32 _⟩

/-! ## The instance, from one lane's event -/

/-- Two lanes of the warp whose first thread is `w` are in one warp. -/
theorem sameWarp_lanes (hb : L.block % 32 = 0) {w l l' : Nat} (hw : laneOf L w = 0)
    (hg : w + l < L.threads) (hl : l < 32) (hl' : l' < 32) : SameWarp L (w + l) (w + l') := by
  have h := (PTX.Step.sameWarp_lane hb hg hl').1
  rwa [laneOf_add hb hw hl, Nat.add_sub_cancel] at h

/-- **Every lane has made the event.** If lane `l` of the warp whose first thread is `w` has a
matrix event of ordinal `n`, then every lane `l'` of the warp has one, unless it exited having
made at most `n` matrix events. A matrix event that exists has returned, so each of its needs,
one per lane, is filled (DEP-WARP-MATRIX). -/
theorem lanes_of_event (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0) {w n l i : Nat}
    (hw : laneOf L w = 0) (hl : l < 32) (hk : X.MatrixK (w + l, i) n)
    (hexit : ∀ l' < 32, ∀ j, ¬ X.ExitedShort isMatrix (w + l', j) n) {l' : Nat} (hl' : l' < 32) :
    ∃ j, X.MatrixK (w + l', j) n := by
  obtain ⟨⟨ev, hget, -⟩, -⟩ := id hk
  have hg : w + l < L.threads := by
    by_contra hn
    have hk' := (List.getElem?_eq_some_iff.mp hget).1
    rw [hX.outside (w + l) (by omega)] at hk'
    simp at hk'
  rcases PTX.Step.matrix_lane_of_ready hX hk (sameWarp_lanes hb hw hg hl hl') with h | ⟨j, h⟩
  · exact h
  · exact absurd h (hexit l' hl' j)

/-- **The instance of a warp from its lanes' events.** When every lane `l'` that has a matrix
event of ordinal `n` has it at position `pc` with operation `op` and contributes `parts l'`,
and one lane has such an event while no lane exits short of it, the 32 lanes form the instance
of ordinal `n`. -/
theorem WarpInstance.of_lanes (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0)
    {w n l i pc : Nat} {op : MatrixOp} {parts : Nat → List (Option Byte)}
    (hw : laneOf L w = 0) (hl : l < 32) (hk : X.MatrixK (w + l, i) n)
    (hexit : ∀ l' < 32, ∀ j, ¬ X.ExitedShort isMatrix (w + l', j) n)
    (hshape : ∀ l' < 32, ∀ j, X.MatrixK (w + l', j) n →
      ∃ recv, X.get (w + l', j) = some ⟨pc, .matrix op (parts l') recv⟩) :
    WarpInstance X w n pc op parts := fun l' hl' => by
  obtain ⟨j, hj⟩ := lanes_of_event hX hb hw hl hk hexit hl'
  obtain ⟨recv, hr⟩ := hshape l' hl' j hj
  exact ⟨j, recv, hr, hj⟩

end PTX.WarpMatrix
