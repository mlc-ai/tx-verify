-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Lemmas.Flow.MemTmpl

namespace PTX.Tests.ClcQuery
noncomputable section

private def L : Launch := { grid := 16, block := 128, params := fun _ => none }
private def success : ClcResponse := ⟨19, some (6, 2, 1)⟩
private def failure : ClcResponse := ⟨20, none⟩
private def t (r : ClcResponse) : TState :=
  { regs := fun name => if name = 2 then some (.clc r) else none }
private def env : Decode.Env :=
  { classes := [⟨"p".toList, 0, 1⟩, ⟨"r".toList, 0, 32⟩, ⟨"q".toList, 0, 128⟩], labels := [],
      params := [] }

example : Decode.op env "clusterlaunchcontrol.query_cancel.is_canceled.pred.b128"
    [.register "p", .register "q"] = .ok (.clcQuery .isCanceled 0 (.reg 2)) := rfl
example : Decode.op env "clusterlaunchcontrol.query_cancel.get_first_ctaid::x.b32.b128"
    [.register "r", .register "q"] = .ok (.clcQuery (.first .x) 1 (.reg 2)) := rfl
example : Decode.op env "clusterlaunchcontrol.query_cancel.get_first_ctaid::y.b32.b128"
    [.register "r", .register "q"] = .ok (.clcQuery (.first .y) 1 (.reg 2)) := rfl
example : Decode.op env "clusterlaunchcontrol.query_cancel.get_first_ctaid::z.b32.b128"
    [.register "r", .register "q"] = .ok (.clcQuery (.first .z) 1 (.reg 2)) := rfl

example : clcQueryValue .isCanceled success = .ok (.pred true) := rfl
example : clcQueryValue .isCanceled failure = .ok (.pred false) := rfl
example : clcQueryValue (.first .x) success = .ok (.bits 32 6) := rfl
example : clcQueryValue (.first .y) success = .ok (.bits 32 2) := rfl
example : clcQueryValue (.first .z) success = .ok (.bits 32 1) := rfl
example : clcQueryValue (.first .x) failure = .error .badValue := rfl

-- The active thread dispatcher records observation of failure, not a silent local step.
example : eventTmpl [] L 0 (t failure) (.clcQuery .isCanceled 0 (.reg 2)) =
    .clcQuery .isCanceled failure (next (setReg (t failure) 0 (.pred false))) := rfl
example : eventTmpl [] L 0 (t failure) (.clcQuery (.first .x) 1 (.reg 2)) =
    .ub .badValue := rfl
example : Op.isLocal (.clcQuery .isCanceled 0 (.reg 2)) = false := rfl

-- From the actual instruction stream, the query emits the recorded event and state.
private def K : Kernel := {
  name := "query", params := [], code := [{ op := .clcQuery .isCanceled 0 (.reg 2) }]
}
example : EStep K [] L 0 (t failure) ⟨0, .clcQuery .isCanceled failure⟩
    (some (next (setReg (t failure) 0 (.pred false)))) := by
  exact ⟨_, rfl, rfl, rfl⟩

-- A complete 16-byte store/load preserves the opaque response, including request identity.
example (r : ClcResponse) :
    rebuild 3 ((Value.clc r).toBytes.map some) = .ok (.clc r) := by
  exact PTX.Proof.rebuild_scalar (v := .clc r) (by change 0 < 16; decide) rfl

-- An arbitrary raw integer is not silently decoded as a forged response.
example : clcTmpl L 0 {} (.clcQuery .isCanceled 0 (.imm 0)) = .ub .typeMismatch := rfl

end
end PTX.Tests.ClcQuery
