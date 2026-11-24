-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcDataAddress

@[expose] public section

/-! # The cells of a Tensor Memory load or store

Facts about `tcDataCell` (THREAD-TC-DATA-ADDRESS) for every shape: the cell is in the issuing
thread's CTA (`tcDataCell_cta`), and one thread's distinct registers are distinct cells
(`tcDataCell_inj`). The `.32x32b` case in closed form, `tcDataCell32` (`tcDataCell_s32x32b`), is
what kernels that issue only `.32x32b` loads and stores rewrite with. -/

namespace PTX

/-- The cell of a Tensor Memory load or store is in the issuing thread's CTA. -/
theorem tcDataCell_cta (L : Launch) (g : Nat) (s : TcShape) (a j : Nat) :
    (tcDataCell L g s a j).cta = g / L.block := rfl

/-- The lane and the column of a register, within the access, determine the register: the maps
of Figures 186 to 190 are injective, and packing doubles the columns. -/
theorem TcShape.laneIn_columnIn_inj (s : TcShape) (l : Nat) :
    ∀ p q : Nat, (s.laneIn l p, s.columnIn l p) = (s.laneIn l q, s.columnIn l q) → p = q := by
  induction s with
  | s32x32b => intro p q h; simp only [TcShape.columnIn, Prod.mk.injEq] at h; omega
  | s16x64b => intro p q h; simp only [TcShape.columnIn, Prod.mk.injEq] at h; omega
  | s16x128b =>
    intro p q h; simp only [TcShape.laneIn, TcShape.columnIn, Prod.mk.injEq] at h; omega
  | s16x256b =>
    intro p q h; simp only [TcShape.laneIn, TcShape.columnIn, Prod.mk.injEq] at h; omega
  | s16x32bx2 off => intro p q h; simp only [TcShape.columnIn, Prod.mk.injEq] at h; omega
  | packed16 s ih =>
    intro p q h
    simp only [TcShape.laneIn, TcShape.columnIn, Prod.mk.injEq] at h
    have h2 : p / 2 = q / 2 := ih (p / 2) (q / 2) (Prod.ext h.1 (by omega))
    omega

/-- **Distinct registers of one thread are distinct cells**, for every shape. -/
theorem tcDataCell_inj {L : Launch} {g : Nat} {s : TcShape} {a j j' : Nat}
    (h : tcDataCell L g s a j = tcDataCell L g s a j') : j = j' := by
  have hl := congrArg TcMma.Cell.lane h
  have hc := congrArg TcMma.Cell.column h
  simp only [tcDataCell] at hl hc
  refine TcShape.laneIn_columnIn_inj s (laneOf L g) j j' ?_
  rw [Nat.add_left_cancel_iff.mp hl, Nat.add_left_cancel_iff.mp hc]

/-- The `.32x32b` cell in closed form: lane `l` of the warp's chunk and the address column plus
the register index (Figure 186). -/
def tcDataCell32 (L : Launch) (g a j : Nat) : TcMma.Cell :=
  ⟨g / L.block, laneBase L g + laneOf L g, a % 2 ^ 16 + j⟩

/-- **The `.32x32b` cell** is `tcDataCell32`, for every address: a 32-lane access starts at the
chunk's first lane. -/
theorem tcDataCell_s32x32b (L : Launch) (g a j : Nat) :
    tcDataCell L g .s32x32b a j = tcDataCell32 L g a j := by
  simp [tcDataCell, tcDataCell32, chunkOffset, TcShape.base, TcShape.lanes, TcShape.laneIn,
    TcShape.columnIn]

end PTX
