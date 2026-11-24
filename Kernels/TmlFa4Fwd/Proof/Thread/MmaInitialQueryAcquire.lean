-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSecondQueryAcquire
public import Kernels.TmlFa4Fwd.Proof.MmaQkQuerySetupReplay

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX
open PTX.Kernels.TmlFa4Fwd.Mma (initialQkBlock qkPc qkStage qkIssueEvent
  firstQueryWaitBeforeGate firstQueryPollOperands)

/-- An actual first QK fragment of the given query stage. -/
def InitialQueryFragment (X : Execution) (stage : Fin 2) (i : EvId) : Prop :=
  ∃ (step : Fin 8) (d : Nat) (op : TcMma.OperandSpec) (accum : Bool) (mask : List Nat),
    X.get i = some ⟨qkPc (initialQkBlock stage) + step.val, .tc (.mma d op accum mask)⟩

/-- The issued fragment follows the successful parity-zero acquire for its physical query bank. -/
theorem InitialQueryFragment.acquire {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {stage : Fin 2} (hIssue : InitialQueryFragment X stage i) :
    ∃ wait e, X.get wait = some e ∧
      e.kind = .wait (Output.queryObject l (wait.1 / l.block) stage) 0 true true .cta ∧
      TraceBefore X wait i := by
  obtain ⟨g, index⟩ := i
  obtain ⟨step, d, op, accum, mask, he⟩ := hIssue
  have hStep := step.isLt
  fin_cases stage
  · obtain ⟨j, _, loc, parity, hPoll, hRes⟩ := firstQueryWaitBeforeGate hp hX he
      (by change 2145 ≤ 2197 + step.val; omega)
      (by change 2197 + step.val ≤ 2642; omega)
    obtain ⟨rfl, rfl⟩ := firstQueryPollOperands hp hX hPoll
    exact ⟨(g, j), _, hPoll, by simp [Output.queryObject], hRes.1⟩
  · obtain ⟨wait, e, hGet, hKind, hOrder⟩ := secondQueryBeforeFirstFragment hp hX he
      (by change 2259 ≤ 2259 + step.val; omega)
      (by change 2259 + step.val ≤ 2266; omega)
    exact ⟨wait, e, hGet, by simpa [hOrder.1, Output.queryObject] using hKind, hOrder⟩

/-- The kernel's first QK issue form supplies the abstract initial-fragment witness. -/
theorem initialQueryFragmentOfIssue {l : Launch} {X : Execution} {stage : Fin 2}
    {i : EvId} (step : Fin 8) (use : Nat)
    (he : X.get i = some (qkIssueEvent l i.1 (initialQkBlock stage) step use)) :
    InitialQueryFragment X stage i :=
  ⟨step, _, _, _, _, he⟩

/-- Every actual QK or PV issue follows the successful initial Q0 acquire in its lane. -/
theorem mmaIssueInitialQueryAcquire {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hMma : X.MmaIssue i d op accum mask) :
    ∃ wait e, X.get wait = some e ∧
      e.kind = .wait (Output.queryObject l (wait.1 / l.block) 0) 0 true true .cta ∧
      TraceBefore X wait i := by
  obtain ⟨g, index⟩ := i
  have reach {site : Nat} (he : X.get (g,index) = some ⟨site, .tc (.mma d op accum mask)⟩)
      (hLo : 2145 ≤ site) (hHi : site ≤ 2642) :=
    firstQueryWaitBeforeGate hp hX he hLo hHi
  have hWait :
      ∃ j < index, ∃ loc q, X.get (g,j) = some ⟨2141, .wait loc q true true .cta⟩ ∧
        Resumes kernel X (g,j) (g,index) := by
    rcases actualMmaInstruction hX hMma with ⟨bank, step, h⟩ | ⟨bank, step, h⟩
    · have hb : ∀ b : Fin 4, ∀ f : Fin 8, 2145 ≤ qkPc b + f.val ∧
          qkPc b + f.val ≤ 2642 := by decide
      exact reach h.decoded (hb bank step).1 (hb bank step).2
    · have hb : ∀ b : Fin 4, ∀ f : Fin 8, 2145 ≤ TmlFa4Fwd.Mma.pvPc b f ∧
          TmlFa4Fwd.Mma.pvPc b f ≤ 2642 := by decide
      exact reach h.decoded (hb bank step).1 (hb bank step).2
  obtain ⟨j, _, loc, parity, he, hOrder⟩ := hWait
  obtain ⟨rfl, rfl⟩ := firstQueryPollOperands hp hX he
  exact ⟨(g,j), _, he, by simp [Output.queryObject], hOrder.1⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX
open PTX.Kernels.TmlFa4Fwd.Mma (qkPc qkStage secondQueryWaitBeforeBank secondQueryPollOperands)

/-- An issued QK fragment follows its own physical query bank's successful acquire. -/
theorem QkInstruction.queryAcquire {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {block : Fin 4} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} (hi : QkInstruction X i block step d op accum mask) :
    ∃ wait e, X.get wait = some e ∧
      e.kind = .wait (Output.queryObject l (wait.1 / l.block) (qkStage block)) 0 true true .cta ∧
      TraceBefore X wait i := by
  by_cases hStage : qkStage block = 0
  · rw [hStage]
    exact Mma.mmaIssueInitialQueryAcquire hp hX ⟨_,hi.decoded⟩
  have hBounds : 2259 ≤ qkPc block + step.val ∧ qkPc block + step.val ≤ 2541 := by
    fin_cases block <;> fin_cases step <;> first | decide | exact (hStage rfl).elim
  have hOne : qkStage block = 1 := Fin.ext (by
    have := (qkStage block).isLt
    have hNonzero : (qkStage block).val ≠ 0 := fun h => hStage (Fin.ext h)
    omega)
  obtain ⟨g,index⟩ := i
  obtain ⟨j,_,object,parity,hPoll,hResume⟩ := secondQueryWaitBeforeBank hp hX hi.decoded
    hBounds.1 hBounds.2
  obtain ⟨rfl,rfl⟩ := secondQueryPollOperands hp hX hPoll
  exact ⟨(g,j), _, hPoll, by rw [hOne]; rfl, hResume.1⟩

end PTX.Kernels.TmlFa4Fwd.Thread
