-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryInputOrder
public import Kernels.TmlFa4Fwd.Proof.MmaReadyRelease
import Kernels.TmlFa4Fwd.Proof.MmaQkIssue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX
open PTX.Kernels.TmlFa4Fwd.Mma (qkPc secondQueryPollOperands secondQueryWaitBeforeGate)

/-- An actual MMA fragment of the initial second-stage QK assembly. -/
@[no_expose] def InitialSecondQueryFragment (X : Execution) (i : EvId) : Prop :=
  ∃ (step : Fin 8) (d : Nat) (op : TcMma.OperandSpec) (accum : Bool) (mask : List Nat),
    X.get i = some ⟨qkPc 1 + step.val, .tc (.mma d op accum mask)⟩

/-- Each actual event in the first Q1 fragment interval follows the issuing lane's
successful parity-zero Q1 acquire, including in an incomplete execution. -/
theorem secondQueryBeforeFirstFragment {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 2259 ≤ e.pc) (hHi : e.pc ≤ 2266) :
    ∃ wait observed, X.get wait = some observed ∧
      observed.kind = .wait (Output.queryObject l (g / l.block) 1) 0 true true .cta ∧
      TraceBefore X wait (g, index) := by
  obtain ⟨j, _, object, parity, hPoll, hResume⟩ := secondQueryWaitBeforeGate hp hX he hLo hHi
  obtain ⟨rfl, rfl⟩ := secondQueryPollOperands hp hX hPoll
  exact ⟨(g, j), _, hPoll, rfl, hResume.1⟩

/-- The initial Q1 fragment observes its lane's successful parity-zero query acquire. -/
theorem InitialSecondQueryFragment.acquire {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} (hIssue : InitialSecondQueryFragment X i) :
    ∃ wait e, X.get wait = some e ∧
      e.kind = .wait (Output.queryObject l (i.1 / l.block) 1) 0 true true .cta ∧
      TraceBefore X wait i := by
  obtain ⟨g, index⟩ := i
  obtain ⟨step, _, _, _, _, he⟩ := hIssue
  exact secondQueryBeforeFirstFragment hp hX he (by change 2259 ≤ 2259 + step.val; omega)
    (by change 2259 + step.val ≤ 2266; have := step.isLt; omega)

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
