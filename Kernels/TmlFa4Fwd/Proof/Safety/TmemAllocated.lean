-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccessEntry
import Kernels.TmlFa4Fwd.Proof.Safety.StageOwnership
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcMmaACell

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX Thread

private theorem mmaDataEvent {X : Execution} {i : EvId} {dst : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i dst s acc mask) :
    TensorDataEvent X i := by
  obtain ⟨_, he⟩ := hi
  exact ⟨_, he, .inr ⟨_, _, _, _, rfl⟩⟩

private theorem resultCellOwner {s : TcMma.OperandSpec} {dst row col owner : Nat}
    {cell : TcMma.Cell} (hLo : s.lowCta = owner) (hHi : s.highCta = owner)
    (h : TcMma.resultCell s dst row col = some cell) : cell.cta = owner := by
  unfold TcMma.resultCell at h
  dsimp only at h
  split at h
  · simp only [hLo, hHi, ite_self] at h
    split at h
    · exact congrArg TcMma.Cell.cta (Option.some.inj h).symm
    · split at h <;> exact congrArg TcMma.Cell.cta (Option.some.inj h).symm
  · cases h

private theorem mmaACellRange {s : TcMma.OperandSpec} {i b owner : Nat} {cell : TcMma.Cell}
    (hLo : s.lowCta = owner) (hHi : s.highCta = owner)
    (h : TcMma.aCell s i = some (cell, b)) : cell.cta = owner ∧ cell.column < 512 := by
  unfold TcMma.aCell at h
  dsimp only at h
  rw [TcMma.row_bytes] at h
  cases hAt : s.aTmem with
  | none => simp [hAt] at h
  | some address =>
    simp only [hAt, Option.bind_some] at h
    split at h
    · rename_i hGuard
      simp only [hLo, hHi, ite_self, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      change owner = owner ∧ address % 2 ^ 16 + i % 32 / 4 < 512
      have hb : address % 2 ^ 16 + 8 ≤ 512 := hGuard.2.2.1
      exact ⟨rfl, by omega⟩
    · cases h

/-- The actual CTA allocation covers every MMA accumulator and Tensor Memory operand cell. -/
theorem mmaAccessAllocated {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {cell : TcMma.Cell} (hAccess : X.MmaAccess i cell) :
    ∃ r ∈ X.tmemHistory (i.1 / l.block), Tmem.Pair.Covers l X r cell.cta i cell.column := by
  have use {dst row col : Nat} {s : TcMma.OperandSpec} {mask : List Nat} {acc : Bool}
      (hi : X.MmaIssue i dst s acc mask) (hc : TcMma.resultCell s dst row col = some cell) :
      ∃ r ∈ X.tmemHistory (i.1 / l.block), Tmem.Pair.Covers l X r cell.cta i cell.column := by
    obtain ⟨hLo, hHi⟩ := mmaOperandOwners hp hX hi
    rw [resultCellOwner hLo hHi hc]
    exact allocatedTensorColumn hp hX (mmaDataEvent hi) (TcMma.resultCell_bounds hc).2
  rcases hAccess with hWrite | hRead | hA
  · obtain ⟨_, _, _, _, _, _, hi, hc⟩ := hWrite
    exact use hi (TcMma.writeCell_resultCell hc)
  · obtain ⟨_, _, _, _, _, hi, hc⟩ := hRead
    exact use hi hc
  · obtain ⟨_, _, _, _, _, _, hi, hc⟩ := hA
    obtain ⟨hLo, hHi⟩ := mmaOperandOwners hp hX hi
    obtain ⟨hOwner, hBound⟩ := mmaACellRange hLo hHi hc
    rw [hOwner]
    exact allocatedTensorColumn hp hX (mmaDataEvent hi) hBound

end PTX.Kernels.TmlFa4Fwd.Safety
