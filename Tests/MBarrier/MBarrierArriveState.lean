-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Source.Decode

/-! `mbarrier.arrive{.expect_tx}.shared.b64 state, [addr], …` (§9.7.15.16.16): the `.shared` state
space is `.shared::cta` (§5.1.7), and the form with a state destination is the existing arrival
rule (THREAD-TMA); only the thread's state differs: the destination holds no value afterwards. -/
namespace PTX.Tests.MBarrierArriveState
open PTX.Syntax
noncomputable section

-- `%r0`, `%r1` are registers 0, 1 (32-bit); `%rd0` is register 2 (64-bit).
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 2, 32⟩, ⟨"%rd".toList, 1, 64⟩], labels := [], params := [] }

/-! ## Decoding -/

-- FA4's two forms: an arrival with a count operand, and an expect-tx arrival.
example : Decode.op env "mbarrier.arrive.shared.b64"
    [.register "%rd0", .address [.register "%r0"], .register "%r1"] =
    .ok (.mbarArrive 0 0 (.imm 0) (.reg 1) false true .cta (some 2)) := rfl
example : Decode.op env "mbarrier.arrive.expect_tx.shared.b64"
    [.register "%rd0", .address [.register "%r0"], .register "%r1"] =
    .ok (.mbarArrive 0 0 (.reg 1) (.imm 1) false true .cta (some 2)) := rfl
-- The same forms with the sink are the existing `.shared::cta` rule.
example : Decode.op env "mbarrier.arrive.shared.b64"
    [.sink, .address [.register "%r0"], .register "%r1"] =
    Decode.op env "mbarrier.arrive.shared::cta.b64"
      [.sink, .address [.register "%r0"], .register "%r1"] := rfl
-- "Sink symbol '_' is mandatory for the destination operand" of a `.shared::cluster` object.
example : (Decode.op env "mbarrier.arrive.shared::cluster.b64"
    [.register "%rd0", .address [.register "%r0"]]).isOk = false := rfl
-- The state is a 64-bit register.
example : (Decode.op env "mbarrier.arrive.shared.b64"
    [.register "%r1", .address [.register "%r0"]]).isOk = false := rfl

/-! ## The event -/

private def launch : Launch := { grid := 1, block := 128, params := fun _ => none }
private def m : Loc := ⟨.shared, 0, 128⟩
private def t : TState := {
  regs := fun r => if r = 0 then some (.bits 32 128)
    else if r = 1 then some (.bits 32 64) else if r = 2 then some (.bits 64 9) else none
}

-- The arrival is the same event with or without the state destination; the continuation differs
-- only in the destination register.
example : tmaTmpl launch 0 t (.mbarArrive 0 0 (.reg 1) (.imm 1) false true .cta none) =
    .arrive m 64 (next t) 1 true .cta := rfl
example : tmaTmpl launch 0 t (.mbarArrive 0 0 (.reg 1) (.imm 1) false true .cta (some 2)) =
    .arrive m 64 (next (mbarStateDest t (some 2))) 1 true .cta := rfl
example : tmaTmpl launch 0 t (.mbarArrive 0 0 (.imm 0) (.reg 1) false true .cta (some 2)) =
    .arrive m 0 (next (mbarStateDest t (some 2))) 64 true .cta := rfl

-- "Contents of the state operand are implementation specific.": reading it is a fault.
example : readReg (next (mbarStateDest t (some 2))) 2 = .error .uninitialized := rfl
-- Other registers are unchanged.
example : readReg (next (mbarStateDest t (some 2))) 1 = .ok (.bits 32 64) := rfl

end
end PTX.Tests.MBarrierArriveState
