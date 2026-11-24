-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedByteRange
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialQueryAcquire
import Lemmas.Tcgen05.MmaOperandObservations

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX
open PTX.Kernels.TmlFa4Fwd.Mma (SharedOperandRange qStart qkStage qkPlane)

private def queryPlane (step : Fin 8) : Fin 2 := ⟨qkPlane step, by
  have := step.isLt
  unfold qkPlane
  omega⟩

/-- A shared MMA read either uses the cache or carries a matching successful query acquire
and exact physical subbox. This classification includes every loop visit. -/
theorem sharedMmaOperandBank {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {loc : Loc} {isB : Bool} {index : Nat} (h : X.MmaFootprint i isB index loc) :
    SharedOperandRange l i.1 loc ∧
      ((l.sharedBase + 68608 ≤ loc.addr) ∨
        ∃ (stage plane : Fin 2) (wait : EvId) (e : Event) (d : Nat) (op : TcMma.OperandSpec)
          (accum : Bool) (mask : List Nat),
          isB = false ∧ X.MmaIssue i d op accum mask ∧ op.byteLoc .a index = some loc ∧
          qStart l stage + 16384 * plane.val ≤ loc.addr ∧
          loc.addr < qStart l stage + 16384 * (plane.val + 1) ∧
          X.get wait = some e ∧
          e.kind = .wait (Output.queryObject l (wait.1 / l.block) stage) 0 true true .cta ∧
          TraceBefore X wait i) := by
  obtain ⟨_,d,op,accum,mask,hi,hByte⟩ := mmaSharedFootprintIssue hX h
  rcases actualMmaInstruction hX hi with ⟨block,step,hQk⟩ | ⟨block,step,hPv⟩
  · cases isB with
    | false =>
      obtain ⟨hRange,hLo,hHi⟩ := (hQk.queryOperand hp hX).operandBankRange hp hByte
      obtain ⟨wait,e,he,hKind,hEarlier⟩ := hQk.queryAcquire hp hX
      exact ⟨hRange, .inr ⟨qkStage block, queryPlane step, wait, e, d, op, accum, mask,
        rfl, hi, hByte, hLo, hHi, he, hKind, hEarlier⟩⟩
    | true =>
      obtain ⟨hRange,hLo⟩ := hQk.keyByteBank hp hX hByte
      exact ⟨hRange, .inl hLo⟩
  · have hB := hPv.sharedOperandB hX hByte
    subst isB
    obtain ⟨hRange,hLo⟩ := hPv.valueByteBank hp hX hByte
    exact ⟨hRange, .inl hLo⟩

end PTX.Kernels.TmlFa4Fwd.Thread
