-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.TcVec

@[expose] public section

/-! # Equal counts before two collective events fix the position, up to one decision

Two lanes of a warp at their `k`-th collective `tcgen05` event have made the same events before:
the counts of the data positions agree (`tcVec`), and so do the paired Tensor Memory operations.
`TcFacts` collects what is known of one lane's event. The counts fix the position, but for the
Softmax loop's rescale decision: the O load (pc 2260) and the P store (pc 1009) of one round
follow the same events. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib

/-- What is known of a lane's collective event at `pc`: its round `i`, the visits `R`, the number
`e` of the epilogue's loads, the launch's loop count `lm`, whether it is in warp zero (`w0`) and
the number `tm` of earlier paired Tensor Memory operations. -/
structure TcFacts (pc i R e lm tm : Nat) (w0 : Bool) : Prop where
  mem : pc = 11 ∨ pc = 15 ∨ pc ∈ tcVecPcs
  loop : pc ∈ loopTcPcs → i < lm
  prev : pc = 2260 ∨ pc = 2261 ∨ pc = 2328 ∨ pc = 2329 → 1 ≤ i
  visit : pc = 2328 ∨ pc = 2329 → 1 ≤ R
  epi : pc = 2607 ∨ pc = 2608 ∨ pc = 2851 → i = lm
  load : pc = 2607 ∨ pc = 2608 → lm ≠ 0
  dealloc : pc = 2851 → e = if lm = 0 then 0 else 1
  warp : pc = 11 ∨ pc = 15 ∨ pc = 2851 → w0 = true
  alloc : pc = 11 → tm = 0
  relinq : pc = 15 → tm = 1
  other : pc ≠ 11 → pc ≠ 15 → tm = if w0 then 2 else 0

/-- **No collective event follows a lane's exit**: the lane's whole run is counted before its exit.
A lane that exits after the counts `tmf` and `lm` and a later event of its warp are at once
impossible when the later event's counts cover the exit's. -/
theorem tcExit_clash {pe ie Re ee lm tm Rf ef tmf : Nat} {w0 : Bool}
    (hx : TcFacts pe ie Re ee lm tm w0)
    (hle : List.Forall₂ (· ≤ ·) (tcVec 2851 lm Rf ef) (tcVec pe ie Re ee))
    (hef : ef = if lm = 0 then 0 else 1) (hw : tmf = if w0 then 3 else 0) (htm : tmf ≤ tm) :
    False := by
  have mx := hx.mem
  obtain ⟨-,l1,l2,l3,l4,l5,l6,l7,l8,l9,l10⟩ := hx
  simp only [tcVecPcs,dataPcs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at mx
  rcases mx with rfl|rfl|(rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|rfl <;>
  first
    | (simp (config := {decide := true}) [tcVec] at *
       all_goals (try split_ifs at *)
       all_goals omega)

theorem tcVec_cases {px py ix iy Rx Ry ex ey lm tm : Nat} {w0 : Bool}
    (hx : TcFacts px ix Rx ex lm tm w0) (hy : TcFacts py iy Ry ey lm tm w0)
    (hvec : tcVec px ix Rx ex = tcVec py iy Ry ey) :
    px = py ∨ (px = 2260 ∧ py = 1009 ∧ ix = iy ∧ Rx = Ry) ∨
      (px = 1009 ∧ py = 2260 ∧ ix = iy ∧ Rx = Ry) := by
  have mx := hx.mem
  have my := hy.mem
  obtain ⟨-,l1,l2,l3,l4,l5,l6,l7,l8,l9,l10⟩ := hx
  obtain ⟨-,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩ := hy
  simp only [tcVecPcs,dataPcs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at mx my
  rcases mx with rfl|rfl|(rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|rfl <;>
  rcases my with rfl|rfl|(rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|rfl <;>
  first
    | (left; rfl)
    | (simp (config := {decide := true}) [tcVec] at *
       all_goals (try split_ifs at *)
       all_goals omega)

end PTX.Kernels.InklingRelDecode.Proof.Lib
